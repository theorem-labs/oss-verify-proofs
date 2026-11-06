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
Variables (hi_453 : bv 20).
Variables (lo_454 : bv 12).
Variables (G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_453 : decode_any (Z_to_bv 32 w_453) = Some (Auipc 10 hi_453, 4%Z).
Hypothesis E_453 : is_ecall (Z_to_bv 32 w_453) = false.
Hypothesis D_454 : decode_any (Z_to_bv 32 w_454) = Some (OpImm ALU_ADD 10 10 lo_454, 4%Z).
Hypothesis E_454 : is_ecall (Z_to_bv 32 w_454) = false.
Hypothesis ANCH_454 : gw_anch (Z.shiftl (bv_signed hi_453) 12 + (base + 1812) + bv_signed lo_454)%Z G_102fd.
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
Definition S_TAIL : ltac:(gw_rebind_ty (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL gw_tbl_15).
#[global] Arguments S_TAIL {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_CV_C : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_CV_C segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_C gw_tbl_16).
#[global] Arguments S_CV_C {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
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
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Notation F_printf_core_common__S_CV_C := S_CV_C (only parsing).
Notation F_printf_core_common__S_TAIL := S_TAIL (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_453 E_453 D_454 E_454 ANCH_454 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation body_loc := (QROt.Mq0.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common__S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

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

#[using="Type"] Lemma mod64_mod256 : forall i, ((i mod 18446744073709551616) mod 256 = i mod 256)%Z.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_TAIL. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]; first [clear HS_TAIL | gw_hide HS_TAIL | idtac].
intros i. replace (i mod 18446744073709551616)%Z with (i + (- (i / 18446744073709551616) * 72057594037927936) * 256)%Z by (Z.div_mod_to_equations; lia).
apply Z_mod_plus_full.
Qed.
#[using="Type"] Lemma le1_mod : forall v, (0 <= v < 2^64)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 (v mod 256)].
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_TAIL. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]; first [clear HS_TAIL | gw_hide HS_TAIL | idtac].
intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow].
change (2^8)%Z with 256%Z. rewrite Z.mod_mod by lia. reflexivity.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_453 lo_454 G_102fd STATIC_SPLIT CODE D_453 E_453 D_454 E_454 ANCH_454 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR"] Lemma L_CV_C : S_CV_C.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_453 lo_454 G_102fd STATIC_SPLIT CODE D_453 E_453 D_454 E_454 ANCH_454 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0 VAHI BS0. try clear BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl flc w p xp i pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP HFC.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (Hmi : (0 <= i mod 18446744073709551616 < 2^64)%Z) by (apply Z.mod_pos_bound; lia).
assert (Hmb : (0 <= i mod 256 < 256)%Z) by (apply Z.mod_pos_bound; lia).
stmt (HS_TAIL fuel HH) as NX.
ienter.
zs. zs.

pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
pose proof (u8arr_store_ok segs _ _ _ 23%Z (wa (q + -369)) DA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite (le1_mod (i mod 18446744073709551616)) by lia. rewrite mod64_mod256.
replace (q + -369)%Z with (q + -392 + 23)%Z by lia.
pose proof (u8arr_write segs _ _ _ 23%Z (Z_to_bv 8 (i mod 256)) DA ltac:(lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
replace (length (upd digs (Z.to_nat 23) (Z_to_bv 8 (i mod 256)))) with 24%nat in DIG by (rewrite upd_length; lia).
pose proof (proj1 DA2) as BODY. rewrite (upd_firstn_skipn) in BODY by lia. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat 23) (length digs))) with 23%Z in BODY by lia.
lazymatch type of BODY with bytes_at _ _ _ (?b :: ?l) => change (b :: l) with ([b] ++ l) in BODY end.
apply bytes_at_app in BODY. destruct BODY as [BODY _].
change [Z_to_bv 8 (i mod 256)] with (zb [i mod 256]%Z) in BODY.
zs. zs. zs. zs. zs. zs. zs. zs.
match goal with |- evt _ _ ?ms => idtac "AT-TAIL" ms end.
unfold ZERO_PAD in HFC |- *. rewrite <- HFC.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := flc) (w := w) (p := 1%Z) (prefix := []) (body := [i mod 256]%Z)
(BA := (q + -392 + 23)%Z) (PFXA := G_102fd)).
all: first [ mk_finv | hyp_cells | exact DIG | exact PAD | exact HS | exact APC | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY
| apply Forall_nil | (constructor; [lia | apply Forall_nil]) | (intros m' MI'; (pose proof (pfx_sub m' 0 0 MI' ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0))
| (unfold body_loc; left; zl) | (subst flc; lia) | lia | zl | (unfold INT_MAX, zlength; cbn [length]; lia)
| match goal with |- ?g => idtac "LEFT" g; fail end ].
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
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
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
Definition fp_postq : ltac:(gw_rebind_ty (@QROt.Mq0.fp_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.fp_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.fp_postq segs got_ssp ssp_guard) fp_postq gw_tbl_10).
#[global] Arguments fp_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_11)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_12)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_13)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_14)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_15).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition S_CV_FP : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_CV_FP segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_FP gw_tbl_16).
#[global] Arguments S_CV_FP {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition fp_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fp_callq) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fp_callq)).
#[global] Arguments fp_callq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope TOK q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope AP%_Z_scope VA%_Z_scope LO GLO QHI TQ SEP_F SEP_B HAP ra'%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a1%_bv_scope a2%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope Ft fc%_bv_scope m%_function_scope st y%_Z_scope w%_Z_scope p%_Z_scope fl%_Z_scope t%_Z_scope _ _ _ _ _ _ _ _ _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
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

Definition F_printf_core_common__Fok_trans : ltac:(gw_ctx_fold_ty (@QROt.Mq0.Fok_trans) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.Fok_trans)).
Notation F_printf_core_common__S_CV_FP := S_CV_FP (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__fp_callq := fp_callq (only parsing).
Notation F_printf_core_common__fp_postq := fp_postq (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation fp_postq := (F_printf_core_common__fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (F_printf_core_common__fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_CV_FP := (F_printf_core_common__S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 STATIC_SPLIT CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ"] Lemma L_CV_FP : S_CV_FP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 STATIC_SPLIT CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ St Fp B BS SINK TOPOK OUT OUTFP SFR SFL HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI BS0. try clear BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP Hy CT.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (conv_type_dbl t CT) as [Ht Hta].
pose proof (lo64_range y) as RL. pose proof (hi64_range y) as RH.
ienter.

assert (XF : (xp && (p <? 0))%bool = false).
{ destruct XP as [[-> ->] | [-> Hp]]; [reflexivity|]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite XF.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z];
[ zs; zs; rewrite Z.land_0_l; zs; if_lit
| zs; zs;
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia);
cbn [Z.b2z Z.land]; zs; if_lit ].

all: destruct (Z.ltb_spec0 1 w) as [W1|W1]; [cbn [orb]; ileave; apply implM_unr_l|].
all: match goal with |- context [if (?a || ?b)%bool then munr else _] =>
destruct b eqn:P20; [ileave; apply implM_unr_l | cbn [orb]] end.
all: match goal with P20 : (?a <=? ?pp)%Z = false |- _ => apply Z.leb_gt in P20 end.
all: zs; zs; zs; zs; zs; zs; zs; zs.
all: ileave; massoc; eapply implM_bind;
[ eapply fp_callq;
[ exact FPC1 | exact HS | rewrite !unsigned_lit by lia; symmetry; apply lo64_hi64; lia | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | exact Hta
| exact ST | gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact SSP1 | exact SSP2] | exact MI | exact FRM ]
| cbv beta ].
all: intros r st'; lazymatch goal with |- context [fp_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call segs mm end.
all: try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end).
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: unfold INT_MAX in *.

all: destruct (Z.lt_ge_cases r 0) as [RN|RP];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; exact RN); apply implM_unr_l | ].
all: destruct (Z.lt_ge_cases 2147483647 r) as [RB|RS];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; right; apply Z.ltb_lt; lia); apply implM_unr_l | ].
all: replace (r <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [orb].
all: destruct (Z.ltb_spec0 (2147483647 - c) r) as [OV|OV]; [apply implM_unr_l|].
all: apply implM_ret_l.
all: ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
(try g_ret_pc) end).
all: zs; zs; brf KR; [ | exfalso; try rewrite unsigned_lit in KR by lia; try rewrite land_M64_id in KR by lia; lia ].
all: stmt HH as NXH.
all: jumpM (eapply NXH with (i := i4) (cnt := c) (l := r) (k := k));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; hyp | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC
| assumption | exact FOK2 | lia | lia | lia | unfold INT_MAX; lia ].
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
Variables (hi_438 : bv 20).
Variables (lo_439 : bv 12).
Variables (G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_438 : decode_any (Z_to_bv 32 w_438) = Some (Auipc 11 hi_438, 4%Z).
Hypothesis E_438 : is_ecall (Z_to_bv 32 w_438) = false.
Hypothesis D_439 : decode_any (Z_to_bv 32 w_439) = Some (OpImm ALU_ADD 17 11 lo_439, 4%Z).
Hypothesis E_439 : is_ecall (Z_to_bv 32 w_439) = false.
Hypothesis ANCH_439 : gw_anch (Z.shiftl (bv_signed hi_438) 12 + (base + 1752) + bv_signed lo_439)%Z G_102fd.
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
Definition S_CV_U : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_CV_U segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_U gw_tbl_16).
#[global] Arguments S_CV_U {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

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
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Notation F_printf_core_common__S_CV_U := S_CV_U (only parsing).
Notation F_printf_core_common__S_FMTU := S_FMTU (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_438 E_438 D_439 E_439 ANCH_439 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_CV_U := (F_printf_core_common__S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_438 lo_439 G_102fd STATIC_SPLIT CODE D_438 E_438 D_439 E_439 ANCH_439 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR"] Lemma L_CV_U : S_CV_U.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_438 lo_439 G_102fd STATIC_SPLIT CODE D_438 E_438 D_439 E_439 ANCH_439 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0 VAHI BS0. try clear BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
stmt (HS_FMTU fuel HH) as NX.
ienter.
zs. zs. zs. zs. zs. zs.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros m' MI'; (pose proof (pfx_sub m' 0 0 MI' ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
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
Variables (hi_467 hi_533 : bv 20).
Variables (lo_468 lo_534 : bv 12).
Variables (G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_467 : decode_any (Z_to_bv 32 w_467) = Some (Auipc 11 hi_467, 4%Z).
Hypothesis E_467 : is_ecall (Z_to_bv 32 w_467) = false.
Hypothesis D_468 : decode_any (Z_to_bv 32 w_468) = Some (OpImm ALU_ADD 14 11 lo_468, 4%Z).
Hypothesis E_468 : is_ecall (Z_to_bv 32 w_468) = false.
Hypothesis D_533 : decode_any (Z_to_bv 32 w_533) = Some (Auipc 11 hi_533, 4%Z).
Hypothesis E_533 : is_ecall (Z_to_bv 32 w_533) = false.
Hypothesis D_534 : decode_any (Z_to_bv 32 w_534) = Some (OpImm ALU_ADD 11 11 lo_534, 4%Z).
Hypothesis E_534 : is_ecall (Z_to_bv 32 w_534) = false.
Hypothesis ANCH_468 : gw_anch (Z.shiftl (bv_signed hi_467) 12 + (base + 1868) + bv_signed lo_468)%Z G_102fd.
Hypothesis ANCH_534 : gw_anch (Z.shiftl (bv_signed hi_533) 12 + (base + 2132) + bv_signed lo_534)%Z G_102fd.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
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
Definition S_INTC : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC gw_tbl_15).
#[global] Arguments S_INTC {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition xloop_post : ltac:(gw_rebind_ty (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.xloop_post segs base) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.xloop_post segs base) xloop_post gw_tbl_16).
Definition S_XLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_XLOOP segs base) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_XLOOP segs base) S_XLOOP gw_tbl_17).
Definition S_CV_X : ltac:(gw_rebind_ty (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_CV_X segs base got_ssp GLOBALS_TOP ssp_guard) S_CV_X gw_tbl_18).
#[global] Arguments S_CV_X {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition rw_CB_length : ltac:(gw_ctx_fold_ty (@QROt.Mq0.rw_CB_length) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.rw_CB_length)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition bytes_at_nil : ltac:(gw_ctx_fold_ty (@QROt.Mq0.bytes_at_nil) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.bytes_at_nil)).
Definition pfx_sub : ltac:(gw_ctx_fold_ty (@QROt.Mq0.pfx_sub) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.pfx_sub)).
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
Notation F_printf_core_common__S_CV_X := S_CV_X (only parsing).
Notation F_printf_core_common__S_INTC := S_INTC (only parsing).
Notation F_printf_core_common__S_XLOOP := S_XLOOP (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_102fd G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_467 E_467 D_468 E_468 D_533 E_533 D_534 E_534 ANCH_468 ANCH_534 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_INTC := (F_printf_core_common__S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_XLOOP := (F_printf_core_common__S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (F_printf_core_common__S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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
Hypothesis HS_XLOOP : S_XLOOP.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_467 hi_533 lo_468 lo_534 G_102fd STATIC_SPLIT CODE D_467 E_467 D_468 E_468 D_533 E_533 D_534 E_534 ANCH_468 ANCH_534 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR"] Lemma L_CV_X : S_CV_X.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_467 hi_533 lo_468 lo_534 G_102fd STATIC_SPLIT CODE D_467 E_467 D_468 E_468 D_533 E_533 D_534 E_534 ANCH_468 ANCH_534 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_102fd ROM_G_102fd LAY_G_102fd_STATIC_SPLIT BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0 VAHI.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
stmt (HS_INTC fuel HH) as NX.
unfold ALT_FORM.
assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
pose proof (hex_digits_length (Z.land t 32) u) as LH.
assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
{ eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
ienter.
zs. zs. zs. zs. brf K0.
-
replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
zs. zs. zs. zs.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
| intros mq MIq; (pose proof (pfx_sub mq 0 0 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
zs. zs.
replace (Z.land t 32) with (Z.land t 32) by reflexivity.
stmt HS_XLOOP as NL.
callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
[ exact MI | exact DIG | lia | exact Hl | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST. cbv zeta in *.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
zs. zs. brf K1.
+
replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
zs. zs. zs. zs. zs. zs. zs. zs.
destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
* (pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := (G_102fd + 7)%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
* (pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := (G_102fd + 5)%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
+
replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
zs. zs. zs.
(pose proof RNG_G_102fd as RNG_pfx_; pose proof LAY_G_102fd_STATIC_SPLIT as LAY_pfx_; unfold gw_br in RNG_pfx_; unfold gw_le in LAY_pfx_); jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := G_102fd));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; (pose proof (pfx_sub mq 0 0 MIq ltac:(lia)) as H_pfx0; cbn [Z.of_nat skipn] in H_pfx0; rewrite Z.add_0_r in H_pfx0; exact H_pfx0) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
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
Definition S_FLAGS : ltac:(gw_rebind_ty (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_FLAGS segs base got_ssp ssp_guard) S_FLAGS gw_tbl_9).
Definition S_WIDTH : ltac:(gw_rebind_ty (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) S_WIDTH gw_tbl_10).
Definition S_PREC : ltac:(gw_rebind_ty (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) S_PREC gw_tbl_11).
Definition S_STATE : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) S_STATE gw_tbl_12).
Definition S_STATEL : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) S_STATEL gw_tbl_13).
Definition S_DIR : ltac:(gw_rebind_ty (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) S_DIR gw_tbl_14).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Notation d_w := G.T_printf.d_w.
Notation d_p := G.T_printf.d_p.
Notation d_xp := G.T_printf.d_xp.
Notation d_t := G.T_printf.d_t.
Notation d_ty := G.T_printf.d_ty.

Definition flag_none : ltac:(gw_ctx_fold_ty (@QFau.flag_none) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QFau.flag_none)).

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_DIR := S_DIR (only parsing).
Notation F_printf_core_common__S_FLAGS := S_FLAGS (only parsing).
Notation F_printf_core_common__S_PREC := S_PREC (only parsing).
Notation F_printf_core_common__S_STATE := S_STATE (only parsing).
Notation F_printf_core_common__S_STATEL := S_STATEL (only parsing).
Notation F_printf_core_common__S_WIDTH := S_WIDTH (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).

Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_FLAGS := (F_printf_core_common__S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_WIDTH := (F_printf_core_common__S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_PREC := (F_printf_core_common__S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (F_printf_core_common__S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (F_printf_core_common__S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common__S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Notation sfx := (sfx fmt).

Notation SPv := (Z_to_bv 64 (q + -544)).

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

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

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

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.
Hypothesis HS_STATEL : S_STATEL.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF HS_FLAGS HS_PREC HS_STATE HS_STATEL HS_WIDTH"] Lemma L_DIR : S_DIR.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF HS_FLAGS HS_PREC HS_STATE HS_STATEL HS_WIDTH St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).

destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.

assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evt segs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x228)) fc None m (seg_rom segs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.

assert (TYS : forall k3 (t1q a1q a3q a4q : word), (k2 <= k3)%Z -> (-1 <= d_p d <= INT_MAX)%Z -> tyspec (sfx k3) = Some (d_ty d, d_t d, rest) ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1q x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) a1q (Z_to_bv 64 (A + k3)) a3q a4q (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 fl) (Z_to_bv 64 (d_p d)) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x448)) fc None m (seg_rom segs))).
{ intros k3 t1q a1q a3q a4q Hk23 Hp TS. assert (Hk30 : (0 <= k3)%Z) by (subst k1 k2; lia).
destruct (tyspec_shape _ _ _ _ TS) as [(Es3 & N108 & CT) | (Es3 & CT)].
- destruct (sfx_cons_inv fmt k3 (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k3) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2.
assert (PS : d_ps d = 0%Z).
{ unfold d_ps. destruct (conv_type_ty _ _ CT) as [-> | [-> | [-> | ->]]]; reflexivity. }
rewrite PS in HK.
jump (apply (HK (k3 + 1)%Z); [zl | exact Erest | replace (k3 + 1 - 1)%Z with k3 by lia; symmetry; exact Et | lia | lia | lia]).
- destruct (sfx_cons_inv fmt k3 108 (d_t d :: rest) Hk30 Es3) as (Hk3 & El & Es4).
destruct (sfx_cons_inv fmt (k3 + 1) (d_t d) rest ltac:(lia) (eq_sym Es4)) as (Hk31 & Et & Erest).
stmt HS_STATEL as NXS. jump (eapply NXS with (k3 := k3) (ty := d_ty d); [exact FI' | lia | zl | symmetry; exact El | rewrite <- Et; exact CT | ]).
intros a2q a3q2.
assert (PS : d_ps d = 1%Z).
{ unfold d_ps. destruct (conv_type_l_ty _ _ CT) as [[-> _] | [-> _]]; reflexivity. }
rewrite PS in HK.
jump (apply (HK (k3 + 2)%Z); [zl | rewrite Erest; f_equal; lia | replace (k3 + 2 - 1)%Z with (k3 + 1)%Z by lia; symmetry; exact Et | lia | lia | lia]). }
destruct PX as [(N46 & Hpq & Hxp & TS) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & TS)].
- stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := k2); [exact FI' | exact LOW' | lia | | ]).
{ left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity. }
intros a1q a3q a4q Hp. apply (TYS k2 _ a1q a3q a4q ltac:(lia) Hp). first [rewrite Es2 | rewrite <- Es2]. exact TS.
- rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
assert (Hk3 : (k2 + 1 + Z.of_nat n3 < zlength fmt)%Z).
{ rewrite Hs3 in TS. destruct (Z.lt_ge_cases (k2 + 1 + Z.of_nat n3) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (k2 + 1 + Z.of_nat n3)) in TS by lia. discriminate TS. }
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (k2 + 1 + Z.of_nat n3)%Z); [exact FI' | exact LOW' | lia | | ]).
{ right. rewrite Hxp. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp. apply (TYS (k2 + 1 + Z.of_nat n3)%Z _ a1q a3q a4q ltac:(lia) Hp). rewrite <- Hs3. exact TS. }

assert (FL34 : forall (a3 a4 a5 : word), evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x198)) fc None m (seg_rom segs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.

assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }

rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
-  zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. (brf K1; [ | exfalso; lia ]). apply FL34.
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
Definition S_EXIT : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) S_EXIT gw_tbl_10).
#[global] Arguments S_EXIT {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_END : ltac:(gw_rebind_ty (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_END segs base got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.S_END segs base got_ssp ssp_guard) S_END gw_tbl_11).
#[global] Arguments S_END {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_END := S_END (only parsing).
Notation F_printf_core_common__S_EXIT := S_EXIT (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_EXIT := (F_printf_core_common__S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_END := (F_printf_core_common__S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

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

Hypothesis HS_EXIT : S_EXIT.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP HS_EXIT LO SEP_F VAHI"] Lemma L_END : S_END.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP HS_EXIT LO SEP_F VAHI St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF QHI TQ FRM0 HA SEP_B HVA A0 BS0.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
FI LOW DIG PAD HS APC FRM FOK Hr.
pose proof FI as FI'. dest_finv FI.
zs. (brf K; [ | exfalso; lia ]).
stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
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
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
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
Definition S_EXIT : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_EXIT segs base got_ssp ssp_guard) S_EXIT gw_tbl_10).
#[global] Arguments S_EXIT {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.

Notation F_printf_core_common__POST := POST (only parsing).
Notation F_printf_core_common__S_EXIT := S_EXIT (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_G_11778.

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

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_EXIT := (F_printf_core_common__S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Ltac hush := idtac.

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO"] Lemma L_EXIT : S_EXIT.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
dest_finv FI. gw_expose ssp_guard; unfold lo_cells in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear - Kc w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.

release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
split; [exact ST|]. split; [exact HS|]. split; [gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
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

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
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
Definition POST1 : ltac:(gw_rebind_ty (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.POST1 segs got_ssp ssp_guard) POST1 gw_tbl_9).
Definition S_EXIT1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) S_EXIT1 gw_tbl_10).

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.

Notation F_printf_core_common__POST1 := POST1 (only parsing).
Notation F_printf_core_common__S_EXIT1 := S_EXIT1 (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_G_11778.

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

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation POST1 := (F_printf_core_common__POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (F_printf_core_common__S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Ltac hush := idtac.

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO"] Lemma L_EXIT1 : S_EXIT1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE LO St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
dest_finv FI. gw_expose ssp_guard; unfold lo_cells in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear - Kc w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.
release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST1.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
split; [exact ST|]. gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact SSP1 | exact SSP2].
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
Definition S_INTC2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC2 gw_tbl_15).
#[global] Arguments S_INTC2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_INTC : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_INTC segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC gw_tbl_16).
#[global] Arguments S_INTC {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_17)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
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
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

Notation F_printf_core_common__S_INTC := S_INTC (only parsing).
Notation F_printf_core_common__S_INTC2 := S_INTC2 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).

Local Notation implM_eq_ms := (F_printf_core_common__implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_INTC2 := (F_printf_core_common__S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (F_printf_core_common__S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_INTC2 : S_INTC2.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HS_INTC2"] Lemma L_INTC : S_INTC.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HS_INTC2 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
stmt (HS_INTC2 fuel HH) as NX.
unfold conv_int.
ienter.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
-
replace (false && (-1 <? 0))%bool with false by reflexivity.
zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
-
replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
zs. zs.
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
rewrite (nzmask_eq fl) in FLB |- * by lia.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
Qed.
End PrintfCore.

End G.
End Mq8.

Module Mq9.

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
Definition S_TAIL : ltac:(gw_rebind_ty (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL gw_tbl_15).
#[global] Arguments S_TAIL {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_INTC2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.S_INTC2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_INTC2 gw_tbl_16).
#[global] Arguments S_INTC2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

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

Notation F_printf_core_common__S_INTC2 := S_INTC2 (only parsing).
Notation F_printf_core_common__S_TAIL := S_TAIL (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation body_loc := (QROt.Mq0.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common__S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_INTC2 := (F_printf_core_common__S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

Hypothesis HS_TAIL : S_TAIL.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP HS_TAIL LO QHI SEP_B SEP_F"] Lemma L_INTC2 : S_INTC2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP GLO HAP HS_TAIL LO QHI SEP_B SEP_F St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA HVA A0 VAHI BS0.
intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (zb_length body) as LB.
set (n := Z.of_nat (length body)) in *.
stmt (HS_TAIL fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
-
replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
zs. brf K3.
+
assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
+
assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| apply bytes_at_nil; lia | apply Forall_nil
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mq9.

Module Mqa.

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
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_7).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_8).
Definition S_SCAN : ltac:(gw_rebind_ty (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) S_SCAN gw_tbl_9).
Definition S_DIR : ltac:(gw_rebind_ty (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_DIR segs base got_ssp ssp_guard) S_DIR gw_tbl_10).
Definition POST1 : ltac:(gw_rebind_ty (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QROt.Mq0.POST1 segs got_ssp ssp_guard) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.POST1 segs got_ssp ssp_guard) POST1 gw_tbl_11).
Definition S_EXIT1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.S_EXIT1 segs base got_ssp ssp_guard) S_EXIT1 gw_tbl_12).
Definition S_P1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.S_P1 segs base got_ssp ssp_guard) S_P1 gw_tbl_13).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Notation F_printf_core_common__S_DIR := S_DIR (only parsing).
Notation F_printf_core_common__S_EXIT1 := S_EXIT1 (only parsing).
Notation F_printf_core_common__S_P1 := S_P1 (only parsing).
Notation F_printf_core_common__S_SCAN := S_SCAN (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).

Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_SCAN := (F_printf_core_common__S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_DIR := (F_printf_core_common__S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Local Notation S_EXIT1 := (F_printf_core_common__S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (F_printf_core_common__S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

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

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_EXIT1 : S_EXIT1.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF HS_DIR HS_EXIT1 HS_SCAN"] Lemma L_P1 : S_P1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF HS_DIR HS_EXIT1 HS_SCAN St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
FI MU1 LOW DIG PAD P1.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. gw_expose ssp_guard; unfold lo_cells in LOW.
stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (n := Z.of_nat (length (lit_run fmt))) in *.
rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
/\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
{ rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
destruct TERM as [TERM PDX].

zs. zs. zs. (brf K; [ exfalso; lia | ]). zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
-
assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
-
jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
[ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
| destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
| unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2. rewrite !Z.add_0_r.
zs. if_lit. zs. brf K1.
+
assert (N0 : n = 0%Z) by lia.
destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
rewrite N0 in PD.
jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
+
zs. zs. zs. (brf K2; [ exfalso; lia | ]). zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
*
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
*
destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
destruct (PDX K3) as (d & rest & PD).
jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
[ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
| right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1' a2''. rewrite !Z.add_0_r.
zs. if_lit. zs. if_lit.
jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
Qed.
End PrintfCore.

End G.
End Mqa.

Module Mqb.

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
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_7).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_8).
Definition S_PLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_PLOOP segs base got_ssp ssp_guard) S_PLOOP gw_tbl_9).
Definition S_PREC : ltac:(gw_rebind_ty (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_PREC segs base got_ssp ssp_guard) S_PREC gw_tbl_10).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_PLOOP := S_PLOOP (only parsing).
Notation F_printf_core_common__S_PREC := S_PREC (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).

Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_PLOOP := (F_printf_core_common__S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (F_printf_core_common__S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].

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

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_PLOOP : S_PLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. (brf K; [ | exfalso; lia ]).
zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. try rewrite Z.lor_0_l.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. zs. zs. zs.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
- assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_PREC : S_PLOOP -> S_PREC.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
FI LOW Hk2 PX HK.
pose proof FI as FI'. dest_finv FI.
rd_fmt k2. zs. fix_u8 k2. zs. zs.
destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
- (brf K; [ | exfalso; lia ]). subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
- (brf K; [ exfalso; lia | ]). rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. (brf K1; [ | exfalso; lia ]).
subst xp. zsto (base + 0x398)%Z.
pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
zs. brf K3.
+
assert (ND : is_digit (znth fmt (k2 + 1)) = false).
{ destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ep Es. subst p.
assert (k3 = k2 + 1)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
+ assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
zs. zs.
stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
{ intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
assert (k3' = k3)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
subst k3'. apply HK. lia.
Qed.
End PrintfCore.

End G.
End Mqb.

Module Mqc.

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
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_7).
Definition S_SCAN : ltac:(gw_rebind_ty (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.S_SCAN segs base got_ssp ssp_guard) S_SCAN gw_tbl_8).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Notation F_printf_core_common__S_SCAN := S_SCAN (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_9)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
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

Local Notation hi_cells := (QROt.Mq0.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).

Local Notation finv := (F_printf_core_common__finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_SCAN := (F_printf_core_common__S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).

Notation SPv := (Z_to_bv 64 (q + -544)).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
finv m ->
k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
(0 <= i)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->

(forall a0, evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then (base + 0xe4) else (base + 0xec))) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd4)) fc None m (seg_rom segs)).
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF segs base St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
-
assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
dest_finv FI. unfold INT_MAX in *.
zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
- destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
pose proof (LIT j ltac:(lia)) as [NZ N37].
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
zs. (brf K; [ exfalso; lia | ]).
rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
+
pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
(brf K1; [ | exfalso; lia ]). replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z FI'); try lia; try assumption.
+ assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
destruct TERM as [T0 | (T37 & Hn1 & T1)].
* rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
* (brf K1; [ | exfalso; lia ]). eapply (IH n FI'); try lia; try assumption.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP STATIC_SPLIT CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 HA HF"] Lemma L_SCAN : S_SCAN.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP STATIC_SPLIT CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP A0 HA HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 SEP_F SEP_B HAP HVA VAHI BS0.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
assert (NZ0 : znth fmt i <> 0%Z).
{ destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
zs. zs. (brf K; [ exfalso; lia | ]).
eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
{ cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
{ destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
intros a0.

assert (TL : forall a1 a2, evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x118)) fc None m (seg_rom segs))).
{ intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. (brf K1; [ exfalso; lia | ]). zs. fixr. apply HK. }
destruct TERM as [T0 | (T37 & Hn1 & T1)].
- rewrite T0, Z.eqb_refl. zs. zs. apply TL.
- rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. (brf K1; [ | exfalso; lia ]). zs. apply TL.
Qed.
End PrintfCore.

End G.
End Mqc.

Module Mqd.

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
Variables (hi_281 : bv 20).
Variables (lo_282 : bv 12).
Variables (G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_281 : decode_any (Z_to_bv 32 w_281) = Some (Auipc 13 hi_281, 4%Z).
Hypothesis E_281 : is_ecall (Z_to_bv 32 w_281) = false.
Hypothesis D_282 : decode_any (Z_to_bv 32 w_282) = Some (OpImm ALU_ADD 13 13 lo_282, 4%Z).
Hypothesis E_282 : is_ecall (Z_to_bv 32 w_282) = false.
Hypothesis ANCH_282 : gw_anch (Z.shiftl (bv_signed hi_281) 12 + (base + 1124) + bv_signed lo_282)%Z G_118c0.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis RNG_G_118c0 : gw_br G_118c0 116.
Hypothesis ROM_G_118c0 : ro_bytes segs G_118c0 [Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 10; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 3; Z_to_bv 8 10; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 27; Z_to_bv 8 9; Z_to_bv 8 11; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 13; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0].
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
Definition S_STATE : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.S_STATE segs base got_ssp ssp_guard) S_STATE gw_tbl_8).
Definition S_STATEL : ltac:(gw_rebind_ty (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_STATEL segs base got_ssp ssp_guard) S_STATEL gw_tbl_9).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition states0_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.states0_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.states0_read)).
Definition states0_read_l : ltac:(gw_ctx_fold_ty (@QROt.Mq0.states0_read_l) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.states0_read_l)).
Definition states1_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.states1_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.states1_read)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_STATE := S_STATE (only parsing).
Notation F_printf_core_common__S_STATEL := S_STATEL (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_STATE := (F_printf_core_common__S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATEL := (F_printf_core_common__S_STATEL Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF"] Lemma L_STATE : S_STATE.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty _ FI Hk3 CT HK.
pose proof FI as FI'. dest_finv FI.
pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
{ exfalso. rewrite land_M64_neg in K by lia. lia. }
clear K. zs. zs. zs. zs. zs. zs.
pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
clear K4. zs. (brf K5; [ | exfalso; lia ]).
jump (apply HK).
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF"] Lemma L_STATEL : S_STATEL.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 hi_281 lo_282 G_118c0 GLOBALS_TOP CODE D_281 E_281 D_282 E_282 ANCH_282 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty _ FI Hk3 Hk31 HL CT HK.
pose proof FI as FI'. dest_finv FI.
pose proof (conv_type_l_ty _ _ CT) as TY. unfold T_LONG, T_ULONG in TY.
assert (TR : (99 <= znth fmt (k3 + 1) <= 117)%Z) by lia.
assert (TYR : (13 <= ty <= 14)%Z) by lia.

zs. zs. rd_fmt k3. zs. fix_u8 k3. rewrite HL. zs. zs. try (brf K; [ exfalso; try rewrite land_M64_neg in K by lia; lia | clear K ]).
zs. zs. zs. zs. zs. zs.
pose proof (states0_read_l m MI) as RD2. zs. cbv beta. rewrite (u8_lit 1) by lia.
zs. zs. zs. brf K2. 2:{ exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2.

rd_fmt (k3 + 1)%Z. replace (A + k3 + 1)%Z with (A + (k3 + 1))%Z by lia. zs. fix_u8 (k3 + 1)%Z. zs. zs. brf K.
{ exfalso. rewrite land_M64_neg in K by lia. lia. }
clear K. zs. zs. zs. zs. zs. zs.
pose proof (states1_read m _ _ MI CT) as RD3. zs. cbv beta. rewrite (u8_lit ty) by lia.
zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
clear K4. zs. (brf K5; [ | exfalso; lia ]).
replace (A + (k3 + 1) + 1)%Z with (A + k3 + 2)%Z by lia.
jump (apply HK).
Qed.
End PrintfCore.

End G.
End Mqd.

Module Mqe.

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
Variables (joff_627 joff_648 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_fwritex e_memset : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_627 : decode_any (Z_to_bv 32 w_627) = Some (Jal 1 joff_627, 4%Z).
Hypothesis E_627 : is_ecall (Z_to_bv 32 w_627) = false.
Hypothesis D_648 : decode_any (Z_to_bv 32 w_648) = Some (Jal 1 joff_648, 4%Z).
Hypothesis E_648 : is_ecall (Z_to_bv 32 w_648) = false.
Hypothesis LINK_627 : gw_anch (base + 2508 + bv_signed joff_627)%Z (e_memset + 0)%Z.
Hypothesis LINK_648 : gw_anch (base + 2592 + bv_signed joff_648)%Z (e_fwritex + 0)%Z.
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
Definition S_T2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 gw_tbl_18).
#[global] Arguments S_T2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T1 gw_tbl_19).
#[global] Arguments S_T1 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Hypothesis memset_callZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq2.gw_all) (@Q91D.Mq2.memset_callZ) (base + 3940)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_20))) in let T := gw_fold_pcs T base (3940)%Z [0; 168]%Z in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
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

Notation F_printf_core_common__S_T1 := S_T1 (only parsing).
Notation F_printf_core_common__S_T2 := S_T2 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 LINK_627 LINK_648 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 memset_callZ"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_T2 := (F_printf_core_common__S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common__S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T2 : S_T2.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 LINK_627 LINK_648 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ"] Lemma L_T1 : S_T1.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_627 joff_648 e_fwritex e_memset CODE BASE4 BASER D_627 E_627 D_648 E_648 LINK_627 LINK_648 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw Hfl0.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
ienter. zs. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB segs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
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
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mqe.

Module Mqf.

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
Variables (joff_655 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_655 : decode_any (Z_to_bv 32 w_655) = Some (Jal 1 joff_655, 4%Z).
Hypothesis E_655 : is_ecall (Z_to_bv 32 w_655) = false.
Hypothesis LINK_655 : gw_anch (base + 2620 + bv_signed joff_655)%Z (e_fwritex + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
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
Definition out_postq : ltac:(gw_rebind_ty (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.out_postq segs got_ssp ssp_guard) out_postq gw_tbl_10).
#[global] Arguments out_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft fc%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope S%_Z_scope bs%_list_scope m%_function_scope _ _ _.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_11)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_12)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_13)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_14)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_15).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition tinv : ltac:(gw_rebind_ty (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv gw_tbl_16).
#[global] Arguments tinv {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope m%_function_scope st k%_Z_scope i4%_Z_scope args%_list_scope fuel%_nat_scope PFXA%_Z_scope fl%_Z_scope n%_Z_scope pl%_Z_scope pq%_Z_scope BA%_Z_scope prefix%_list_scope body%_list_scope alo%_bv_scope ahi%_bv_scope j128%_list_scope digs%_list_scope pad%_list_scope.
Definition S_T3 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T3 gw_tbl_17).
#[global] Arguments S_T3 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 gw_tbl_18).
#[global] Arguments S_T2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition out_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.out_callq) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.out_callq)).
#[global] Arguments out_callq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope TOK HOUT q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope LO GLO QHI TQ SEP_F SEP_B HAP BS0 ra'%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope Ft fc%_bv_scope m%_function_scope st S%_Z_scope L%_Z_scope bs%_list_scope _ _ _ _ _ _ _ _ _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_T2 := S_T2 (only parsing).
Notation F_printf_core_common__S_T3 := S_T3 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_655 E_655 LINK_655 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_T3 := (F_printf_core_common__S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (F_printf_core_common__S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T3 : S_T3.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_655 e_fwritex CODE BASE4 BASER D_655 E_655 LINK_655 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ"] Lemma L_T2 : S_T2.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_655 e_fwritex CODE BASE4 BASER D_655 E_655 LINK_655 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ St Fp B BS SINK TOPOK OUT OUTFP SFR ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K5; [ exfalso; lia | ]). clear FLC.
zs. zs. zs. zs.
out_call.
1:{ apply HPFX. exact MI. }
1:{ exact PRNG. }
1:{ rewrite Hpl. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T3 fuel HH) as NX3.
jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mqf.

Module Mqg.

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
Variables (joff_668 joff_689 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_fwritex e_memset : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_668 : decode_any (Z_to_bv 32 w_668) = Some (Jal 1 joff_668, 4%Z).
Hypothesis E_668 : is_ecall (Z_to_bv 32 w_668) = false.
Hypothesis D_689 : decode_any (Z_to_bv 32 w_689) = Some (Jal 1 joff_689, 4%Z).
Hypothesis E_689 : is_ecall (Z_to_bv 32 w_689) = false.
Hypothesis LINK_668 : gw_anch (base + 2672 + bv_signed joff_668)%Z (e_memset + 0)%Z.
Hypothesis LINK_689 : gw_anch (base + 2756 + bv_signed joff_689)%Z (e_fwritex + 0)%Z.
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
Definition S_T4 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T4 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T4 gw_tbl_18).
#[global] Arguments S_T4 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T3 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@QROt.Mq0.S_T3 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T3 gw_tbl_19).
#[global] Arguments S_T3 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Hypothesis memset_callZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq2.gw_all) (@Q91D.Mq2.memset_callZ) (base + 3940)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_20))) in let T := gw_fold_pcs T base (3940)%Z [0; 168]%Z in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_20)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
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

Notation F_printf_core_common__S_T3 := S_T3 (only parsing).
Notation F_printf_core_common__S_T4 := S_T4 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_memset CODE BASE4 BASER D_668 E_668 D_689 E_689 LINK_668 LINK_689 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 memset_callZ"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_T4 := (F_printf_core_common__S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (F_printf_core_common__S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T4 : S_T4.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_668 joff_689 e_fwritex e_memset CODE BASE4 BASER D_668 E_668 D_689 E_689 LINK_668 LINK_689 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ"] Lemma L_T3 : S_T3.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_668 joff_689 e_fwritex e_memset CODE BASE4 BASER D_668 E_668 D_689 E_689 LINK_668 LINK_689 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+ rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
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
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mqg.

Module Mqh.

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
Variables (joff_729 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_729 : decode_any (Z_to_bv 32 w_729) = Some (Jal 1 joff_729, 4%Z).
Hypothesis E_729 : is_ecall (Z_to_bv 32 w_729) = false.
Hypothesis LINK_729 : gw_anch (base + 2916 + bv_signed joff_729)%Z (e_fwritex + 0)%Z.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
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
Definition out_postq : ltac:(gw_rebind_ty (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.out_postq segs got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.out_postq segs got_ssp ssp_guard) out_postq gw_tbl_10).
#[global] Arguments out_postq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope ra'%_bv_scope Ft fc%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope S%_Z_scope bs%_list_scope m%_function_scope _ _ _.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_11)).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_12)).
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_13)).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QROt.Mq0.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_14)).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition S_HEAD : ltac:(gw_rebind_ty (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_HEAD segs base got_ssp GLOBALS_TOP ssp_guard) S_HEAD gw_tbl_15).
#[global] Arguments S_HEAD {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope fuel%_nat_scope.
Definition tinv : ltac:(gw_rebind_ty (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv gw_tbl_16).
#[global] Arguments tinv {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope m%_function_scope st k%_Z_scope i4%_Z_scope args%_list_scope fuel%_nat_scope PFXA%_Z_scope fl%_Z_scope n%_Z_scope pl%_Z_scope pq%_Z_scope BA%_Z_scope prefix%_list_scope body%_list_scope alo%_bv_scope ahi%_bv_scope j128%_list_scope digs%_list_scope pad%_list_scope.
Definition S_T6 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T6 gw_tbl_17).
#[global] Arguments S_T6 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T5 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T5 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T5 gw_tbl_18).
#[global] Arguments S_T5 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition out_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.out_callq) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.out_callq)).
#[global] Arguments out_callq {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope TOK HOUT q%_Z_scope gp%_bv_scope tp%_bv_scope lo%_Z_scope canary%_bv_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope LO GLO QHI TQ SEP_F SEP_B HAP BS0 ra'%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope s0%_bv_scope s1%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope Ft fc%_bv_scope m%_function_scope st S%_Z_scope L%_Z_scope bs%_list_scope _ _ _ _ _ _ _ _ _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_T5 := S_T5 (only parsing).
Notation F_printf_core_common__S_T6 := S_T6 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER D_729 E_729 LINK_729 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

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
Local Notation S_T6 := (F_printf_core_common__S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (F_printf_core_common__S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T6 : S_T6.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_729 e_fwritex CODE BASE4 BASER D_729 E_729 LINK_729 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI"] Lemma L_T5 : S_T5.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_729 e_fwritex CODE BASE4 BASER D_729 E_729 LINK_729 RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI St Fp B BS SINK TOPOK OUT OUTFP SFR ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K5; [ exfalso; lia | ]). clear FLC.
zs. zs. zs. zs.
out_call.
1:{ exact BODY. }
1:{ exact BRNG. }
1:{ rewrite Hn. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T6 fuel HH) as NX6.
jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

End G.
End Mqh.

Module Mqi.

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
Variables (joff_742 joff_762 : bv 21).
Variables (G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_197bc e_fwritex e_memset : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis D_742 : decode_any (Z_to_bv 32 w_742) = Some (Jal 1 joff_742, 4%Z).
Hypothesis E_742 : is_ecall (Z_to_bv 32 w_742) = false.
Hypothesis D_762 : decode_any (Z_to_bv 32 w_762) = Some (Jal 1 joff_762, 4%Z).
Hypothesis E_762 : is_ecall (Z_to_bv 32 w_762) = false.
Hypothesis LINK_742 : gw_anch (base + 2968 + bv_signed joff_742)%Z (e_memset + 0)%Z.
Hypothesis LINK_762 : gw_anch (base + 3048 + bv_signed joff_762)%Z (e_fwritex + 0)%Z.
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
Definition S_T6 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T6 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T6 gw_tbl_18).
#[global] Arguments S_T6 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Hypothesis memset_callZ : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq2.gw_all) (@Q91D.Mq2.memset_callZ) (base + 3940)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_19))) in let T := gw_fold_pcs T base (3940)%Z [0; 168]%Z in exact T).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition implM_eq_ms : ltac:(gw_ctx_fold_ty (@QROt.Mq0.implM_eq_ms) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.implM_eq_ms)).
#[global] Arguments implM_eq_ms {St}%_type_scope {X}%_type_scope c s Q%_function_scope ms ms' _ _.
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Definition out_callq : ltac:(gw_ctx_fold_ty (@QROt.Mq0.out_callq) constr:(gw_tbl_19)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.out_callq)).
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

Notation F_printf_core_common__S_T6 := S_T6 (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__out_callq := out_callq (only parsing).
Notation F_printf_core_common__out_postq := out_postq (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_197bc e_fwritex e_memset CODE BASE4 BASER D_742 E_742 D_762 E_762 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778 memset_callZ"] Lemma gw_all : True. Proof. exact I. Qed.

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

Local Notation S_T6 := (F_printf_core_common__S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_742 E_742 D_762 E_762 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ"] Lemma L_T6 : S_T6.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 joff_742 joff_762 e_fwritex e_memset CODE BASE4 BASER D_742 E_742 D_762 E_762 LINK_742 LINK_762 RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP memset_callZ BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ St Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF FRM0 A0 VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.

apply (rw_cells_split_CB segs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. (brf K5; [ exfalso; lia | ]). clear FLC.
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
lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
zs.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells segs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app segs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | gw_expose ssp_guard; unfold lo_cells; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.
End PrintfCore.

End G.
End Mqi.

Module Mqj.

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
Definition S_TAIL : ltac:(gw_rebind_ty (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq0.S_TAIL segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_TAIL gw_tbl_15).
#[global] Arguments S_TAIL {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition tinv : ltac:(gw_rebind_ty (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@QROt.Mq0.tinv segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) tinv gw_tbl_16).
#[global] Arguments tinv {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope m%_function_scope st k%_Z_scope i4%_Z_scope args%_list_scope fuel%_nat_scope PFXA%_Z_scope fl%_Z_scope n%_Z_scope pl%_Z_scope pq%_Z_scope BA%_Z_scope prefix%_list_scope body%_list_scope alo%_bv_scope ahi%_bv_scope j128%_list_scope digs%_list_scope pad%_list_scope.
Definition S_T2 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@QROt.Mq0.S_T2 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T2 gw_tbl_17).
#[global] Arguments S_T2 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.
Definition S_T1 : ltac:(gw_rebind_ty (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@QROt.Mq0.S_T1 segs base got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) S_T1 gw_tbl_18).
#[global] Arguments S_T1 {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope ra%_bv_scope q%_Z_scope gp%_bv_scope tp%_bv_scope s0e%_bv_scope s1e%_bv_scope s2e%_bv_scope s3e%_bv_scope s4e%_bv_scope s5e%_bv_scope s6e%_bv_scope s7e%_bv_scope s8e%_bv_scope s9e%_bv_scope s10e%_bv_scope s11e%_bv_scope F fc0%_bv_scope m0%_function_scope lo%_Z_scope canary%_bv_scope A%_Z_scope fmt%_list_scope AP%_Z_scope VA%_Z_scope slots%_list_scope nla%_bv_scope nlt%_bv_scope.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

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
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).
Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- QlEo_c1.Mq0.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Ql2m.Mq3.implM segs c s Q ms) | _ => idtac end.

Notation F_printf_core_common__S_T1 := S_T1 (only parsing).
Notation F_printf_core_common__S_T2 := S_T2 (only parsing).
Notation F_printf_core_common__S_TAIL := S_TAIL (only parsing).
Notation F_printf_core_common__finv := finv (only parsing).
Notation F_printf_core_common__implM_eq_ms := implM_eq_ms (only parsing).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
Notation F_printf_core_common__sink_call := sink_call (only parsing).
Notation F_printf_core_common__sink_store := sink_store (only parsing).
Notation F_printf_core_common__tinv := tinv (only parsing).

#[using="G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 G_11778 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP RNG_G_11778.

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

Local Notation body_loc := (QROt.Mq0.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common__S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (QROt.Mq0.tregs Fp q gp tp A).
Local Notation tinv := (F_printf_core_common__tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Local Notation S_T2 := (F_printf_core_common__S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common__S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Ltac zlg := lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => idtac | nat => idtac | N => idtac | _ => fail end | _ => idtac end; zl.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zlg | progress f_equal | (progress (rewrite ?Z.shiftl_0_l, ?Z.shiftr_0_l); lia) ].

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

Hypothesis HS_T1 : S_T1.
Hypothesis HS_T2 : S_T2.

#[using="Type"] Lemma conv_tail_k : forall (a1 a2 a3 a4 a5 a6 : M St unit) (v : Z) (k : Z -> M St Z) s Q ms,
implM segs (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; k v) s Q ms ->
implM segs (x <- (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; mret v) ;; k x) s Q ms.
Proof. clear - segs St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0 HS_T1 HS_T2.
clear - segs. intros a1 a2 a3 a4 a5 a6 v k s Q ms H.
Ltac kstep H := apply implM_assoc; eapply implM_bind_ext; [ | exact H ]; cbv beta;
let x := fresh "x" in let s' := fresh "s'" in let ms' := fresh "ms'" in let H' := fresh "H" in
intros x s' ms' H'.
kstep H. kstep H0. kstep H1. kstep H2. kstep H3. kstep H4. apply implM_ret_l. exact H5.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_T1 HS_T2 HVA LO QHI SEP_B SEP_F SFR VAHI"] Lemma L_TAIL : S_TAIL.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP BS0 GLO HA HAP HS_T1 HS_T2 HVA LO QHI SEP_B SEP_F SFR VAHI St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 A0.
intros fuel HH x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p prefix body BA PFXA s2s za plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BLOC BHI BIM HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. gw_expose ssp_guard; unfold lo_cells in LOW. unfold body_loc in BLOC.
pose proof (bytes_at_bound _ _ _ _ BODY) as BB. pose proof (zb_length body) as LB. rewrite LB in BB.
set (n := Z.of_nat (length body)) in *. set (pl := Z.of_nat (length prefix)) in *.
unfold conv_tail. unfold zlength. fold n. fold pl. cbv zeta.
ienter.
zs. rewrite (sextw_small p) by lia. zs. replace (BA + n - BA)%Z with n by lia. zs. zs. zs.
brf K1; [ | zs ].

all: zs; try rewrite (sextw_small p) by lia; fixr; zs; zs; fixr; zs; brf K2;
[ replace (INT_MAX - pl <? Z.max p n)%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - pl <? Z.max p n)%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; fixr; zs; zs; zs; brf K3; [ | zs ].

all: zs; brf K4;
[ replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; lia); ileave; apply implM_unr_l
| replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia) ].

all: zs; zs; zs; zs; brf K5.
all: ileave; apply conv_tail_k.
all: match goal with
| K : Z.land ?flv 73728 <> 0%Z |- _ =>
unfold mpad at 1; change (Z.lor LEFT_ADJ ZERO_PAD) with 73728%Z; rewrite (proj2 (Z.eqb_neq _ 0) K); cbn [negb orb]; apply implM_ret_l;
stmt (HS_T2 fuel HH) as NX2;
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ]
| K : Z.land ?flv 73728 = 0%Z |- _ =>
stmt (HS_T1 fuel HH) as NX1;
jumpM (eapply NX1 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia | exact K ]
end.
Qed.
End PrintfCore.

End G.
End Mqj.

Module Mqk.

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
Definition lo_cells : ltac:(gw_rebind_ty (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QROt.Mq0.lo_cells ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QROt.Mq0.lo_cells ssp_guard) lo_cells gw_tbl_7).
Definition finv : ltac:(gw_rebind_ty (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@QROt.Mq0.finv segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@QROt.Mq0.finv segs got_ssp ssp_guard) finv gw_tbl_8).
Definition S_WLOOP : ltac:(gw_rebind_ty (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@QROt.Mq0.S_WLOOP segs base got_ssp ssp_guard) S_WLOOP gw_tbl_9).
Definition S_WIDTH : ltac:(gw_rebind_ty (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QROt.Mq0.S_WIDTH segs base got_ssp ssp_guard) S_WIDTH gw_tbl_10).

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Definition zbytes_read : ltac:(gw_ctx_fold_ty (@QROt.Mq0.zbytes_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.zbytes_read)).
Definition cb8_c8_in : ltac:(gw_ctx_fold_ty (@QROt.Mq0.cb8_c8_in) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.cb8_c8_in)).
Definition sink_store : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_store) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_store)).
#[global] Arguments sink_store {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR m%_function_scope st a%_Z_scope bs%_list_scope _ _ _ _ _.
Definition sink_call : ltac:(gw_ctx_fold_ty (@QROt.Mq0.sink_call) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.sink_call)).
#[global] Arguments sink_call {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope SFR Wc%_list_scope m%_function_scope m'%_function_scope st _ _ _ _ _.
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.

Notation F_printf_core_common__S_WIDTH := S_WIDTH (only parsing).
Notation F_printf_core_common__S_WLOOP := S_WLOOP (only parsing).
Definition F_printf_core_common__fmt_rng : ltac:(gw_ctx_fold_ty (@QROt.Mq0.fmt_rng) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm (@QROt.Mq0.fmt_rng)).
Notation F_printf_core_common__lo_cells := lo_cells (only parsing).
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
Local Notation lo_cells := (F_printf_core_common__lo_cells AP nla nlt).

Local Notation fmt_rng := (F_printf_core_common__fmt_rng fmt HF).

Local Notation sink_store := (F_printf_core_common__sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common__sink_call (St:=St) Fp B BS SINK SFR).

Local Notation S_WLOOP := (F_printf_core_common__S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (F_printf_core_common__S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF"] Lemma L_WLOOP : S_WLOOP.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. gw_expose ssp_guard; unfold lo_cells in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.

assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. (brf K; [ | exfalso; lia ]).
zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. (brf K3; [ | exfalso; lia ]).
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
-
assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

#[using="w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE HF"] Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof. clear - w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 GLOBALS_TOP CODE HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0.
intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hk1 G NE HK.
pose proof FI as FI'. dest_finv FI.
pose proof (fmt_rng k1 ltac:(zl)) as RG1.
zs. zs. zs. zs. brf K.
-
assert (ND : is_digit (znth fmt k1) = false).
{ destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
- assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
zs. zs.
stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.
End PrintfCore.

End G.
End Mqk.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR QfcC QDUx Q9Ay Qy5Y Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mql.

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

Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_71 w_72 w_98 : Z).
Variables (got_ssp STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (shgetc_code w_71 w_72 w_98).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 544.

Local Definition gw_tbl_0 := tt.

Definition ss_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QROt.Mq2.ss_cells STRING_READ) ss_cells (gw_ent (@Q8l1.Mq3.ss_cells STRING_READ) ss_cells (gw_ent (@QQRC.Mq3.ss_cells STRING_READ) ss_cells gw_tbl_0))).
Definition SHGETC := (base + 56)%Z.
Local Definition gw_tbl_2 := (gw_ent (@QROt.Mq2.SHGETC base) SHGETC (gw_ent (@QQRC.Mq3.SHGETC base) SHGETC gw_tbl_1)).
Definition UFLOW := (base + 256)%Z.
Local Definition gw_tbl_3 := (gw_ent (@QROt.Mq2.UFLOW base) UFLOW (gw_ent (@QQRC.Mq3.UFLOW base) UFLOW gw_tbl_2)).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_3)).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_4)).
Definition RFI : ltac:(gw_rebind_ty (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq3.RFI STRING_READ) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QQRC.Mq3.RFI STRING_READ) RFI gw_tbl_5).
Definition shgetc_post : ltac:(gw_rebind_ty (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QROt.Mq2.shgetc_post segs got_ssp STRING_READ ssp_guard) shgetc_post gw_tbl_6).

Notation rfj := G.T_rfj.rfj.

#[using="got_ssp STRING_READ ssp_guard CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
(sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ (J = ssJ /\ False))%Z.

Section RF.
Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
Hypothesis Hp : 0 <= p < zlength txt.
Hypothesis Hnul : znth txt p = 0.
Hypothesis T0 : 0 < T.
Hypothesis T1 : T + 2^41 <= 2^63.

Notation RFI := (RFJ T txt p true J).

#[using="Type"] Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
Proof. clear - T txt p J BYT Hp Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]. intros kmin c f (OK & _). exact OK. Qed.

#[using="Hp"] Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
Proof. clear - Hp T txt p J BYT Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct (sh_stdio f) eqn:ES; [destruct (SS eq_refl) as (N1 & N2 & _); lia | destruct (NS eq_refl) as (N1 & N2 & N3); lia].
Qed.

#[using="Hp"] Lemma rf_getc_fast : forall kmin c f, RFI kmin c f ->
T + sh_rpos f <> rf_rend T p true f ->
sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
Proof. clear - Hp T txt p J BYT Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). rewrite N1.
destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
- reflexivity.
Qed.

#[using="Hp"] Lemma rf_getc_fast_lt : forall kmin c f, RFI kmin c f -> c <> 0 ->
T + sh_rpos f <> rf_rend T p true f -> 0 <= sh_rpos f < zlength txt.
Proof. clear - Hp T txt p J BYT Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & _). lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). lia.
Qed.

#[using="Hp T1"] Lemma rf_getc_slow : forall kmin c f, RFI kmin c f ->
T + sh_rpos f = rf_rend T p true f ->
sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = p /\ 0 <= sh_cnt0 f <= sh_rpos f.
Proof. clear - Hp T1 T txt p J BYT Hnul T0. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) E. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). repeat split; try assumption; unfold M64 in E; lia.
- exfalso. unfold M64 in E. lia.
Qed.

Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
try lazymatch goal with |- (_ -> _) => intro end).

#[using="BYT Hp Hnul"] Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
Proof. clear - BYT Hp Hnul T txt p J T0 T1. first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
assert (R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256).
{ intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply Qy5Y.znth_In'. unfold zlength. lia. }
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct st; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). subst n.
destruct (Z.eqb_spec rpos p) as [E|NE]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
+ unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
+ pose proof (R0 rpos ltac:(lia)).
assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). subst sn. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
Qed.

#[using="Hp"] Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
Proof. clear - Hp T txt p J BYT Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac].
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hk. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
- destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). specialize (N3 eq_refl). crush.
+ destruct (NS eq_refl) as (N1 & _). discriminate N1.
- specialize (KM eq_refl). destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). crush.
+ destruct (NS eq_refl) as (N1 & N2 & N3). crush.
Qed.

#[using="Type"] Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
Proof. clear - T txt p J BYT Hp Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
#[using="Type"] Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
Proof. clear - T txt p J BYT Hp Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
#[using="Type"] Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
Proof. clear - T txt p J BYT Hp Hnul T0 T1. first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.

Open Scope bv_scope.

#[using="Type"] Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells segs m Fp (rf_cells T p true f J) ->
RFJ T txt p true J kmin c f ->
(T + sh_rpos f = rf_rend T p true f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at segs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk segs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom segs)).
Proof. clear - segs got_ssp ssp_guard.
intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
pose proof RJ as RJ'. destruct RJ' as (OK & Rc & CC & KM & NS & SS).
assert (Hp2 : (0 <= p < zlength txt)%Z).
{ destruct TXT as (Htxt & _ & _ & _ & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
destruct (rf_getc_slow T txt p J Hp2 T1 kmin c f RJ SLOW) as (ST0 & EJ & Hn & Hrp & Hc0).
exfalso. destruct (SS ST0) as (X1 & X2 & X3 & X4 & [X5 FF]). exact FF.
Qed.

End G.
End Mql.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QM7w QXxF Q8QT QCa8 QDXD QkTt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqm.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0.
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
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import QROt.Mq3.
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
Notation gw_tbl_1 := (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_usage_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_usage_read) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_usage_read)).

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rsmall_cnt_bytes : list byte :=
[Z_to_bv 8 30; Z_to_bv 8 30; Z_to_bv 8 30; Z_to_bv 8 31; Z_to_bv 8 15; Z_to_bv 8 15; Z_to_bv 8 20; Z_to_bv 8 10; Z_to_bv 8 10; Z_to_bv 8 31; Z_to_bv 8 15; Z_to_bv 8 7; Z_to_bv 8 25; Z_to_bv 8 12; Z_to_bv 8 6; Z_to_bv 8 21; Z_to_bv 8 10; Z_to_bv 8 5; Z_to_bv 8 18; Z_to_bv 8 8; Z_to_bv 8 4; Z_to_bv 8 31; Z_to_bv 8 15; Z_to_bv 8 7; Z_to_bv 8 28; Z_to_bv 8 14; Z_to_bv 8 6].
Definition rmed_cnt_bytes : list byte :=
[Z_to_bv 8 28; Z_to_bv 8 24; Z_to_bv 8 20; Z_to_bv 8 32].

#[using="RNG_RDEBRUIJN ROM_RSMALL_CNT"] Lemma rsmall_cnt_ro : forall m, mem_inv segs m -> ro_cells segs m (RDEBRUIJN + 128) [CB 27 rsmall_cnt_bytes].
Proof. clear - RNG_RDEBRUIJN ROM_RSMALL_CNT segs RDEBRUIJN.
intros m MI. pose proof RNG_RDEBRUIJN as RNG_; unfold gw_br in RNG_. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_RSMALL_CNT].
Qed.
#[using="RNG_RDEBRUIJN ROM_RMED_CNT"] Lemma rmed_cnt_ro : forall m, mem_inv segs m -> ro_cells segs m (RDEBRUIJN + 155) [CB 4 rmed_cnt_bytes].
Proof. clear - RNG_RDEBRUIJN ROM_RMED_CNT segs RDEBRUIJN.
intros m MI. pose proof RNG_RDEBRUIJN as RNG_; unfold gw_br in RNG_. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_RMED_CNT].
Qed.

#[using="RNG_RDEBRUIJN ROM_RSMALL_CNT"] Lemma rsmall_cnt_read : forall m sc i, mem_inv segs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
ov_read_bytes segs m (wa ((RDEBRUIJN + 128) + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof. clear - RNG_RDEBRUIJN ROM_RSMALL_CNT segs RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros m sc i MI Hsc Hi.
destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
replace ((RDEBRUIJN + 128) + 3 * sc + i) with ((RDEBRUIJN + 128) + (3 * sc + i)) by lia.
rewrite (bytes_at_read segs m (RDEBRUIJN + 128) rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
unfold small_cnt. rewrite !Nat2Z.id.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

#[using="RNG_RDEBRUIJN ROM_RMED_CNT"] Lemma rmed_cnt_read : forall m i, mem_inv segs m -> 0 <= i < 4 ->
ov_read_bytes segs m (wa ((RDEBRUIJN + 155) + i)) 1 = Some [b8 (med_cnt i)].
Proof. clear - RNG_RDEBRUIJN ROM_RMED_CNT segs RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros m i MI Hi.
destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read segs m (RDEBRUIJN + 155) rmed_cnt_bytes i 1 B) by (cbn; lia).
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ"] Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv segs m ->
evt segs (fun ms' => exists a2' a3',
ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x2a4)) fc None m (seg_rom segs))
(MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x290)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ segs base usage size UR. first [clear UR | gw_hide UR | idtac]; try gw_hide size; first [clear usage | gw_hide usage | idtac].
induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
- cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
- cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
step. rewrite (unsigned_lit (size * cnt)) by lia.
step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
+
rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
rewrite (QDUx.Mq9.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| gw_exact MI].
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
+ rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof. clear - cnt.
intros H.
assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.eq_dec n 1) as [->|NE].
- change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
- replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE UR"] Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv segs m ->
evt segs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x290)) fc None m (seg_rom segs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x268)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE UR segs base usage size SZ. first [clear SZ | gw_hide SZ | idtac]; first [clear size | gw_hide size | idtac]; try gw_hide usage.
induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
- change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
- cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; gw_exact EV).

step. rewrite (wz_unsigned cnt), (Z.shiftl_mul_pow2 cnt) by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
+
replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
step. apply evt_done. do 2 eexists. reflexivity.
+ replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).

step. rewrite (wz_unsigned cnt) by lia. rewrite (QDUx.Mq9.srliw_small cnt 1) by lia.
step. rewrite (wz_unsigned cnt) by lia. step.
assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.

step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; gw_exact K2).
assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
{ rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| gw_exact EV2| gw_exact MI].
*
step.
assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; gw_exact K2).
replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
apply evt_done. do 2 eexists. reflexivity.
Qed.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE UR"] Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv segs m ->
evt segs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x290)) fc None m (seg_rom segs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x260)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE UR segs base usage size SZ. first [clear SZ | gw_hide SZ | idtac]; first [clear size | gw_hide size | idtac]; try gw_hide usage.
intros until m; intros CR C32 MI; unfold rcnt_regs.

step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
-
assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; gw_exact K).
replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
step. step. apply evt_done. do 2 eexists. reflexivity.
- assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; gw_exact K).
destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
apply rhalve_even_loop; [lia| lia| gw_exact EV| gw_exact MI].
Qed.
End HALVE2.

Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof. clear - SC st m sc MR UR u size cnt0. try gw_hide cnt0; try gw_hide size; try gw_hide u; first [clear UR | gw_hide UR | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide sc; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
unfold cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
- pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

#[using="RGOT_SSP ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_130 hi_136 hi_148 lo_131 lo_137 lo_149 CODE D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 ANCH_131 ANCH_137 ANCH_149 RNG_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT RC__ MR SC UR"] Lemma rcount_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
mem_inv segs m ->
evt segs (fun ms' => exists a2' a3' a4',
ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 (RATP + 131696)) s5 (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x2a4)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 (RATP + 131696)) s5 (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc))
(wz (size_class sc)) (Z_to_bv 64 (RDEBRUIJN + 32)) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x204)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_130 hi_136 hi_148 lo_131 lo_137 lo_149 CODE D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 ANCH_131 ANCH_137 ANCH_149 RNG_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT RC__ MR SC UR segs base RATP RDEBRUIJN st m sc u size cnt0. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide cnt0; try gw_hide size; try gw_hide u; try gw_hide sc; try gw_hide m; try gw_hide st.
intros until fc. intros MI.
pose proof (size_class_range sc SC) as SZR.
pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
pose proof rcnt0_range as C0R.
(gw_expose_fam RATP; gw_expose_fam RDEBRUIJN; unfold rcnt_regs in *).

pose proof (rmrep_usage_read st m sc (wa ((RATP + 132432) + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
step. clear RDU.

step. step. step. step. rewrite (wz_unsigned (size_class sc)), (Z.shiftl_mul_pow2 (size_class sc)) by lia. change (2 ^ 4) with 16.
fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).

step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
-
apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].

step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. gw_expose_fam RDEBRUIJN.
step. clear RDM. rewrite zxb_b8 by lia.

eapply evt_cut.
{ eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| gw_exact MI]. }
cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
eapply evt_mono.
{ eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| gw_exact MI]. }
cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
-
assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; gw_exact H| lia]).
unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.

step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. gw_expose_fam RDEBRUIJN.
replace (wa ((RDEBRUIJN + 128) + 3 * sc + 0)) with (Z_to_bv 64 ((RDEBRUIJN + 128) + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
step. clear RD0. rewrite zxb_b8 by lia.

step. rewrite (wz_unsigned (small_cnt sc 0)), (Z.shiftl_mul_pow2 (small_cnt sc 0)) by lia. change (2 ^ 2) with 4.
step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
{ replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. gw_expose_fam RDEBRUIJN.
replace (wa ((RDEBRUIJN + 128) + 3 * sc + 1)) with (Z_to_bv 64 ((RDEBRUIJN + 128) + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
step. clear RD1. rewrite zxb_b8 by lia.
step. rewrite (wz_unsigned (small_cnt sc 1)), (Z.shiftl_mul_pow2 (small_cnt sc 1)) by lia. change (2 ^ 2) with 4.
step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
{ replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. gw_expose_fam RDEBRUIJN.
replace (wa ((RDEBRUIJN + 128) + 3 * sc + 2)) with (Z_to_bv 64 ((RDEBRUIJN + 128) + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
step. clear RD2. rewrite zxb_b8 by lia. step.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.

Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ C0"] Lemma rcnt2_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (if big then (base + 0x2cc) else (base + 0x310))) fc None m (seg_rom segs))
(MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (base + 0x2a4)) fc None m (seg_rom segs)).
Proof. clear - w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE SZ C0 segs base u size cnt0 cnt1 big. try gw_hide big; try gw_hide cnt1; try gw_hide cnt0; try gw_hide size; first [clear u | gw_hide u | idtac].
intros until m. intros MI. unfold rcnt_regs.
assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.

step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.

step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
-
assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; gw_exact K); reflexivity).

step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
-
step. rewrite ?unsigned_lit by lia. step. step.
assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
{ unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
{ rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
rewrite EV. clear EV.
assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).

step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.

End RC__1.

End G.
End Mqm.

Module Mqn.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QROt.Mq3.
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
Notation gw_tbl_1 := (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10))))))))))).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry rmmap_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry"] Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk segs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
evt segs (fun ms' => exists (a1' a2' : word),
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom segs)
/\ stk segs m lo (bv_unsigned sp))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x860)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE rmmap_entry segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR' MI FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
(gw_expose_fam RATP; unfold alloc_ceiling, rta_frame in *).

step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

step. step. step. step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 2 eexists. split; [reflexivity| gw_exact ST].
Qed.

End RC__1.

End G.
End Mqn.

Module Mqo.

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
Let ralloc_slot_entry := (base + 0)%Z.
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

Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))))))))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_set_active : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_active) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_active)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_active_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_active_read) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_active_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).

Definition rconc_meta_inj : ltac:(gw_ctx_fold_ty2 (@QQRC.Mqc.rconc_meta_inj) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mqc.rconc_meta_inj)).
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
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH];
[ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
| reflexivity | cbn; tauto]);
clear MUq WMq CH end.
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
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_slot_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 lo_15 lo_19 CODE D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 ANCH_15 ANCH_19 LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry MR SC CLO AMS"] Lemma ras_entry_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
a0 = Z_to_bv 64 sc ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' : word) m' junk,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 rc_canary a1' (pw st (active st sc)) a3 a4 a5 a6 a7
a1 s3 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (match active st sc with None => (base + 0x1e0) | Some _ => (base + 0x64) end)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ stk segs m' lo (bv_unsigned sp + -144)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep st m')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 lo_15 lo_19 CODE D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 ANCH_15 ANCH_19 LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry MR SC CLO AMS segs base RATP RGOT_SSP st m sc lo. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear lo | gw_hide lo | idtac]; try gw_hide sc; try gw_hide m; try gw_hide st.
intros until fc. intros HA ST LO MI. subst a0.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _). unfold wz in G4.
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold ralloc_slot_entry, alloc_ceiling in *).

step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.

step. step. step. step. step. step. step. step. step. step.
rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [gw_exact MR| gw_exact MU| gw_exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]) end.
pose proof (rmrep_active_read st _ sc (wa ((RATP + 132048) + 8 * sc)) MR1 SC eq_refl) as RDA.
step. clear RDA.

step.
replace ((RATP + 131960) + sc * 8 + 88) with ((RATP + 132048) + 8 * sc) by lia.
replace ((RATP + 131960) + sc * 8) with ((RATP + 131960) + 8 * sc) by lia.
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.

step. if_cases K; zify_cond K.
- destruct (active st sc) as [g|] eqn:HA.
{ exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _).
unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [gw_exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
- destruct (active st sc) as [g|] eqn:HA.
2:{ exfalso. apply K. reflexivity. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [gw_exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 ((RATP + 132048) + 8 * sc))
(Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 ((RATP + 131960) + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL AVR"] Lemma rt1_fin_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr <> 0 -> mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1a0)) fc None m (seg_rom segs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL AVR segs base RATP st m g sc G mr SC FRR. gw_expose_fam RATP. first [clear FRR | gw_hide FRR | idtac]; first [clear SC | gw_hide SC | idtac]; try gw_hide mr; try gw_hide G; first [clear sc | gw_hide sc | idtac]; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros AVNZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
pose proof (sxv_range (m_avail mr)) as RA.

step. rewrite sx32_wz_sxv by lia.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
{ exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). gw_exact K. }
step. step.
apply evt_done. reflexivity.
Qed.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL"] Lemma rt1_deq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr = 0 -> mem_inv segs m ->
evt segs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL segs base RATP st m g sc G mr SC AVR FRR. gw_expose_fam RATP. first [clear FRR | gw_hide FRR | idtac]; first [clear AVR | gw_hide AVR | idtac]; first [clear SC | gw_hide SC | idtac]; try gw_hide mr; try gw_hide G; first [clear sc | gw_hide sc | idtac]; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. unfold pw, wz. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry MR MSL SC FRR"] Lemma rt1_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc8)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (set_active sc (m_next mr) st) m')
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry MR MSL SC FRR segs base RATP st m g sc G mr AVR. gw_expose_fam RATP. first [clear AVR | gw_hide AVR | idtac]; try gw_hide mr; try gw_hide G; try gw_hide sc; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
pose proof (munch_refl [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
pose proof (sxv_range (m_freed mr)) as RF.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. step.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
{ exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). gw_exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st) sc (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.

step.
apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption| gw_exact MR2].
Qed.
End T1.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry MR MSL SC"] Lemma rdeq_self_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_next mr = Some g -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1e0)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry MR MSL SC segs base RATP st m g sc G mr HA AV0 FR0. gw_expose_fam RATP. first [clear FR0 | gw_hide FR0 | idtac]; first [clear AV0 | gw_hide AV0 | idtac]; first [clear HA | gw_hide HA | idtac]; try gw_hide mr; try gw_hide G; try gw_hide sc; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
gw_expose_fam RATP.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st) sc (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR1; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (pw st None)) MU WM SOK.
set (st1 := set_active sc None st) in MR1.
assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; gw_exact MSL).

rmeta_open G MUg WMg.
rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
st1. st1.
rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.

pose proof (rmrep_active_read _ _ sc (wa ((RATP + 132048) + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption| gw_exact MR2].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry MR MSL SC HA"] Lemma rdeq_other_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
mem_inv segs m ->
let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
let st3 := set_active sc (Some nx) st2 in
let st4 := put_meta g (clr mr) st3 in
evt segs (fun ms' => exists (a1' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc8)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep st4 m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ralloc_slot_entry MR MSL SC HA segs base RATP st m g sc G mr AV0 FR0. gw_expose_fam RATP. first [clear FR0 | gw_hide FR0 | idtac]; first [clear AV0 | gw_hide AV0 | idtac]; try gw_hide mr; try gw_hide G; try gw_hide sc; try gw_hide g; try gw_hide m; try gw_hide st.
intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _).
assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [gw_exact MR| gw_exact MSL| gw_exact MSn| gw_exact E]).
gw_expose_fam RATP.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. gw_exact K. } clear K.

rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
step. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmchunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; gw_exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; gw_exact MSn).

rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. step. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmchunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; gw_exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa ((RATP + 132048) + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.

step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; gw_exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. clear CH. step.

pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st2) sc (wa ((RATP + 132048) + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
fold st3 in MR3.
assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; gw_exact MSg2).

rmeta_open G MUg WMg.
rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
replace (get_meta_rec st3 g) with mr in CH.
2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; gw_exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; gw_exact E). reflexivity. }
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.

pose proof (rmrep_active_read _ _ sc (wa ((RATP + 132048) + 8 * sc)) MR4 SC eq_refl) as RDA.
change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption| gw_exact MR4].
Qed.
End DEQ.

Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

#[using="RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL FRR MW"] Lemma rm_act_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
full_skip st g = false -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf4)) fc None m (seg_rom segs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc8)) fc None m (seg_rom segs)).
Proof. clear - RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved ralloc_slot_entry RC__ MR MSL FRR MW segs base RATP st m g sc G mr f SC. gw_expose_fam RATP. first [clear SC | gw_hide SC | idtac]; try gw_hide f; try gw_hide mr; try gw_hide G; first [clear sc | gw_hide sc | idtac]; try gw_hide g; try gw_hide m; try gw_hide st.
intros until fc. intros NSK MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{  apply evt_done. do 2 eexists. reflexivity. }

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
{ apply evt_done. do 2 eexists. reflexivity. }
exfalso. unfold full_skip in NSK. fold mr f in NSK.
assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|gw_exact K2]).
rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry f MR MSL SC FRR MW"] Lemma rm_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xf4)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xc8)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved ralloc_slot_entry f MR MSL SC FRR MW segs base RATP st m g sc G mr. gw_expose_fam RATP. try gw_hide mr; try gw_hide G; try gw_hide sc; try gw_hide g; try gw_hide m; try gw_hide st.
intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
pose proof (munch_refl [((RATP + 132048) + 8 * sc, (RATP + 132048) + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
gw_expose_fam RATP.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.

step. clear CH.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok segs _ _ (actives st) sc (Z_to_bv 64 ((RATP + 132048) + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; gw_expose_fam RATP end.
rraw_store_finish0 ((RATP + 132048) + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; gw_exact MSn).
rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
step. rewrite sx32_wz_sxv by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption| gw_exact MR2].
Qed.
End M.

End RC__1.

End G.
End Mqo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE Q4vs Q6y7 QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqp.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 Qy5Y.Mq4 QlQE.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3 QWTl.Mq4 QDUx.Mqa Q9Ay.Mqb QXxF.Mq4 Q4vs Q6y7.
Import QFkE.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QCa8.Mq4.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import QROt.Mq6.
Import Q8l1.Mq9.
Import QROt.Mq7.
Import QROt.Mq8.
Import Q8l1.Mqa.
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

Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_0)).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QROt.Mq8.rfree_fp RATP) (@rfree_fp) (gw_ent (@QROt.Mq7.rfree_fp RATP) (@rfree_fp) (gw_ent (@Q8l1.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QROt.Mq6.rfree_fp RATP) (@rfree_fp) (gw_ent (@QQRC.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_1))))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq6.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq6.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq6.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq6.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq6.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq6.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq6.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq6.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq6.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq6.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QROt.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@QROt.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QROt.Mq6.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_12))))))))).
Definition rqpath_post : ltac:(gw_rebind_ty (@QQRC.Mq9.rqpath_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq9.rqpath_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq9.rqpath_post segs base RATP RGOT_SSP ref_reserved RC__) (@rqpath_post) gw_tbl_13).
Definition rfg_post : ltac:(gw_rebind_ty (@QROt.Mq6.rfg_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QROt.Mq6.rfg_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QROt.Mq6.rfg_post segs base RATP RGOT_SSP ref_reserved RC__) (@rfg_post) gw_tbl_14).
Definition rat9c_post : ltac:(gw_rebind_ty (@Q8l1.Mq9.rat9c_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq9.rat9c_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Q8l1.Mq9.rat9c_post segs base RATP RGOT_SSP ref_reserved RC__) (@rat9c_post) gw_tbl_15).
Definition rat00_post : ltac:(gw_rebind_ty (@Q8l1.Mq9.rat00_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q8l1.Mq9.rat00_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Q8l1.Mq9.rat00_post segs base RATP RGOT_SSP ref_reserved RC__) (@rat00_post) gw_tbl_16).
Definition rnest_call_post : ltac:(gw_rebind_ty (@QROt.Mq8.rnest_call_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QROt.Mq8.rnest_call_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@QROt.Mq8.rnest_call_post segs base RATP RGOT_SSP ref_reserved RC__) (@rnest_call_post) gw_tbl_17).
Definition rget_meta_post : ltac:(gw_rebind_ty (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@QROt.Mq8.rget_meta_post segs) (@rget_meta_post) (gw_ent (@QCa8.Mq4.rget_meta_post segs) (@rget_meta_post) gw_tbl_18)).
Definition rntf_ret_post : ltac:(gw_rebind_ty (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@QROt.Mq8.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) (gw_ent (@QROt.Mq7.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) (gw_ent (@Qy8Z.Mq9.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) (gw_ent (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) gw_tbl_19)))).
Definition RAT : ltac:(gw_rebind_ty (@Q8l1.Mqa.RAT segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Q8l1.Mqa.RAT segs) constr:(gw_tbl_20)).
Notation gw_tbl_21 := (gw_ent (@Q8l1.Mqa.RAT segs) (@RAT) gw_tbl_20).
Definition rentry_cases : ltac:(gw_rebind_ty (@Q8l1.Mqa.rentry_cases segs base RATP) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Q8l1.Mqa.rentry_cases segs base RATP) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@Q8l1.Mqa.rentry_cases segs base RATP) (@rentry_cases) gw_tbl_21).
Definition rntf_frame : ltac:(gw_rebind_ty (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_22)).
Notation gw_tbl_23 := (gw_ent (@Q8l1.Mqa.rntf_frame RC__) (@rntf_frame) (gw_ent (@QROt.Mq8.rntf_frame RC__) (@rntf_frame) (gw_ent (@QROt.Mq7.rntf_frame RC__) (@rntf_frame) (gw_ent (@Qy8Z.Mq9.rntf_frame RC__) (@rntf_frame) gw_tbl_22)))).
Definition rentry_post : ltac:(gw_rebind_ty (@Q8l1.Mqa.rentry_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Q8l1.Mqa.rentry_post segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)).
Notation gw_tbl_24 := (gw_ent (@Q8l1.Mqa.rentry_post segs base RATP RGOT_SSP ref_reserved RC__) (@rentry_post) gw_tbl_23).
Hypothesis meta_word_pg : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.meta_word_pg) (base + -732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (-732)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).
Hypothesis rget_meta_walk : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.rget_meta_walk) (base + -272)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (-272)%Z [0; 244]%Z in exact T).
Hypothesis meta_word_sc2 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.meta_word_sc2) (base + -732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (-732)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_evt) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_evt)).
#[global] Arguments rimplT_evt {R}%_type_scope o t s Q%_function_scope P%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_del_group : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_del_group) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_del_group)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_mono : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_mono) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_mono)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Definition rimplT_guard : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_guard) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_guard)).
#[global] Arguments rimplT_guard {R}%_type_scope o t%_Z_scope c%_bool_scope k bail s Q%_function_scope ms _%_function_scope.
Definition rimplT_rd8 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd8) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd8)).
#[global] Arguments rimplT_rd8 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.
Definition rimplT_rd16 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd16) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd16)).
#[global] Arguments rimplT_rd16 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.

Definition rmrep_grp_del_eq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_grp_del_eq) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_grp_del_eq)).

Definition rntf_aor : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq9.rntf_aor) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq9.rntf_aor)).

Definition rconc_meta_inj : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq9.rconc_meta_inj) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq9.rconc_meta_inj)).
Definition rntf_qpath : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq9.rntf_qpath) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq9.rntf_qpath)).

Definition rntf_fg : ltac:(gw_ctx_fold_ty2 (@QROt.Mq6.rntf_fg) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq6.rntf_fg)).

Definition rntf_deqself : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq9.rntf_deqself) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq9.rntf_deqself)).
Definition rntf_deq : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq9.rntf_deq) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq9.rntf_deq)).
Definition rntf_postdeq : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq9.rntf_postdeq) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq9.rntf_postdeq)).

Definition rntf_top : ltac:(gw_ctx_fold_ty2 (@QROt.Mq7.rntf_top) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq7.rntf_top)).

Definition rntf_nest_call : ltac:(gw_ctx_fold_ty2 (@QROt.Mq8.rntf_nest_call) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq8.rntf_nest_call)).
Definition rntf_nest_ret : ltac:(gw_ctx_fold_ty2 (@QROt.Mq8.rntf_nest_ret) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq8.rntf_nest_ret)).

Definition rntf_entry : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mqa.rntf_entry) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mqa.rntf_entry)).

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ meta_word_pg rget_meta_walk meta_word_sc2"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
(st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ rmrep st' m'
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
/\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

#[using="Type"] Lemma rpres_except_entry st lo (sp : word) m m1 :
munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono segs m m1 -> lo <= bv_unsigned sp - 96 ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof. clear - segs st lo sp m m1.
intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved o m m' st lo sp mw RATP. gw_expose_fam RATP.
intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
rewrite (OK rid r q h Hr Hk Hq M8 Hc).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
unfold alloc_ceiling in *.
symmetry. apply (PE (r_base r + q)); [lia|].
intros [[A|[A|A]]|[A|A]].
- lia.
- gw_expose_fam RATP. lia.
- destruct A as (rid' & r' & Hr' & Hk' & Hin).
destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
- destruct A as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
Z.div_mod_to_equations. lia.
- destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
destruct (N.eq_dec rid' rid) as [->|NE].
+ rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

#[using="Type"] Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof. clear - st st' lo sp sp' a.
intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

#[using="Type"] Lemma rfree_fp_same st st' lo (sp : Z) a :
s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof. clear - st st' lo sp a. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| gw_exact H]. Qed.

#[using="RIMG_HI LAY_hi_RATP LAY_win_4"] Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof. clear - RIMG_HI LAY_hi_RATP LAY_win_4 st mw lo sp a RATP. gw_expose_fam RATP.
intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
unfold alloc_ceiling in *.
destruct H as [[A|[A|A]]|[A|A]].
- lia.
- gw_expose_fam RATP. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
Qed.

#[using="Type"] Lemma rknown_byte st m (q : aptr) r v :
rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
cell_read (get_shadow st (fst q)) (snd q) = Known v ->
bytes_at segs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof. clear - segs st m q r v.
intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

#[using="Type"] Lemma rimplT_queue {R} o h g st0 (k : mstate -> QUZl.M R) bail s Q ms :
(m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
rimplT o (queue h g st0 k bail) s Q ms.
Proof. clear - R o h g st0 k bail s Q ms.
intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); gw_exact H.
Qed.

#[using="Type"] Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. clear - junk s3 s2 s1 s0 ra. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved LO"] Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
(exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved LO Zs ra sp s0 s1 s2 s3 st stX st' m mX mi a0v a1v ms' gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc o LB lo. first [clear lo | gw_hide lo | idtac]; first [clear LB | gw_hide LB | idtac]; first [clear o | gw_hide o | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac].
intros RP PE FP KI ZI FR RES OOK MRX ER ES.
destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
unfold rntf_q. do 16 eexists. split; [reflexivity|].
split; [gw_exact MI'|]. split; [gw_exact ST'|]. split; [gw_exact MR'|].
split. { eapply rpres_except_trans; [gw_exact PE|]. eapply rpres_except_mono; [gw_exact PE'|]. gw_exact FP. }
split; [gw_exact KI|]. split; [gw_exact ZI|]. split; [gw_exact FR|]. split; [gw_exact RES|].
eapply oracle_ok_frame; [| gw_exact ER | gw_exact ES]. eapply roracle_ok_pres; [gw_exact OOK | gw_exact MRX | gw_exact LO | gw_exact PE'].
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_6 hi_26 hi_31 hi_93 lo_7 lo_27 lo_32 lo_94 CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 ANCH_7 ANCH_27 ANCH_32 ANCH_94 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_pg rget_meta_walk meta_word_sc2 LO"] Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> QUZl.M R) (bail : QUZl.M R)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
(st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
rmrep st m -> mem_inv segs m -> oracle_ok o m st ->
stk segs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
(forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 hi_6 hi_26 hi_31 hi_93 lo_7 lo_27 lo_32 lo_94 CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 ANCH_7 ANCH_27 ANCH_32 ANCH_94 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved meta_word_pg rget_meta_walk meta_word_sc2 LO segs base RATP gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc o LB lo. gw_expose_fam RATP. try gw_hide lo; try gw_hide LB; try gw_hide o; try gw_hide fc; try gw_hide F; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; try gw_hide s7; try gw_hide s6; try gw_hide s5; try gw_hide s4; try gw_hide tp; try gw_hide gp.
induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
{ cbn [nontrivial_free]. apply rimplT_undef. }
rewrite ntf_unfold. cbv zeta.
pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
pose proof (go_slot _ _ _ GO) as MSL.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
set (ms0 := MS _ _ _ _ _ _ _).

assert (ENTRY : entry_hyps st g i ->
evt segs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
{ intros EH. subst ms0. eapply rntf_entry; eauto. }

assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
(G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
(G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
entry_hyps st g i).
{ intros. constructor; auto.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- pose proof (go_sc _ _ _ GO). lia.
- intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
- intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
- split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
destruct (ntf_cond st g i) eqn:HC.
-

assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
rfg_post ra sp gp tp s0 (Z_to_bv 64 (RATP + 131696)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
(m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
(forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
wmono segs m m2 -> oracle_ok o m2 stX ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
{ intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
set (stU := fg_usage_st stX g) in *.
assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).

assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
{ destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
try lia; try gw_exact HALL.
- exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
- destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
- destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; gw_exact LPX).
assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; gw_exact GNX)).
rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
[ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
| pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; gw_exact Hj) ltac:(rewrite RU; apply ALLFREE; [gw_exact Hj| gw_exact NE])) as FC;
rewrite RU in FC; gw_exact FC ])).
fold stG in GD. destruct GD as (KIG & NGM & NSL).
assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; gw_exact MR3).
assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; gw_exact FRX).
assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).

pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
-
assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
rewrite free_meta_eq.
eapply rimplT_evt.
{ eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
first [gw_exact MRG | gw_exact MI3 | gw_exact MSG | gw_exact MWU | gw_exact MEMU | gw_exact MLNZ | gw_exact FR3 | gw_exact ST3 | gw_exact LO | gw_exact LOLE | reflexivity
| apply munch_refl | apply wmono_refl | idtac].
- pose proof (ki_cx _ _ _ KIG) as (SQ & _). gw_exact SQ.
- intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [gw_exact GNU| gw_exact Hhd]. }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try gw_exact RP.
+ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [gw_exact PE0|]];
(eapply rpres_except_mono; [gw_exact PE3| gw_exact FPX]).
+ intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | gw_exact Ha].
unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
+ eexists. apply KINV_fm; [apply KINV_seq; gw_exact KIG| | | |].
* unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [gw_exact MSG|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros [b Hb]. apply NGM. exists b. unfold hosts in *.
replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [gw_exact Hb|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [gw_exact GNU|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
* intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
+ apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; gw_exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+
pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
set (stS := record_seq _ (step_seq stG)) in *.
assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; gw_exact GNU).
unfold fm_st. apply frame_queue.
* apply frame_put_meta; [apply frame_seq; gw_exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
* apply links_put_meta0; [exact (ki_links _ _ _ KIS)| gw_exact GNS].
* cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| gw_exact NX'].
* right; exact (hosts_is_gm _ _ _ HOSTS).
+
pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [gw_exact SND| split]]]].
* unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
* exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
* intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; gw_exact MLNZ | gw_exact ALLFREE | gw_exact Hb' | gw_exact E].
+ eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [gw_exact OOK2 | gw_exact MRW | gw_exact LO | gw_exact PE3].
+ gw_exact MRG.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
+ pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
-
assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).

pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
clear NEST.
pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
assert (B1LT : snd b1 + 16 <= snd p).
{ rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
pose proof (go_stride _ _ _ GO1) as [S16 _].
assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; gw_exact HB1).
assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [gw_exact NEb1| gw_exact HB1U]).

pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
{ split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold UNIT, IB in *. lia. }
destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].

unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
{ intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
rewrite !ESH.
rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; gw_exact K4).
rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; gw_exact K3).
rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; gw_exact K2).
rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; gw_exact K1).
cbn [Z.eqb negb].
set (off16 := lo8 + 256 * hi8).
assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
{ unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
rewrite EB. unfold get_group.
replace (s_groups stG !! b1) with (s_groups stX !! b1).
2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.

assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.

assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
bytes_at segs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
{ intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; gw_exact Hr) Kr ltac:(cbn; lia)
ltac:(cbn; unfold get_shadow; rewrite ESU; gw_exact Hc)) as [B V].
cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; gw_exact Hr). cbn [snd] in B.
rewrite (conc_region' stU p r) by (rewrite ERU; gw_exact Hr). split; [| gw_exact V].
replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. gw_exact B. }
destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
assert (HDR : bytes_at segs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
{ change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
apply bytes_at_app. split; [gw_exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; gw_exact Y3|].
apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; gw_exact Y2|].
cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. gw_exact Y1. }

destruct HOSTSX as [aig Hghp].
eapply rimplT_evt.
{ eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
all: first [gw_exact MR3 | gw_exact MI3 | gw_exact MWU | gw_exact MLZ | gw_exact MEMU | gw_exact HDR | gw_exact FR3 | gw_exact ST3 | gw_exact LO | gw_exact LOLE
| gw_exact R3 | gw_exact R2 | gw_exact R1 | gw_exact AR1 | gw_exact G15 | apply rntf_frame_size | idtac].
all: try reflexivity.
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
all: rewrite ?EU1.
all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
try gw_exact G12; try gw_exact G13; try gw_exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
all: try (unfold stU; rewrite fg_usage_groups; first [gw_exact Hghp | gw_exact Hgh1]).
all: try (symmetry; gw_exact EB).
all: match goal with
| |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
| |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
| |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
fold off16 in G17; unfold UNIT in G17;
replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
rewrite Z.div_mul in G17 by lia; lia
| |- ?G => idtac "NCGOAL" G; fail
end. }
intros ms3 NC. unfold rnest_call_post in NC.
destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
fold stG in MR4.

pose proof (bv_unsigned_in_range _ sp) as SPR'.
assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (unfold alloc_ceiling in LO; rewrite unsigned_lit; lia).
rewrite V31. replace (conc stU g1) with (conc stG g1) by first [reflexivity | (cbn; lia)].
eapply (IH R _ bail s Q (Z_to_bv 64 (base + 0x288)) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
+ gw_exact KIG.
+ constructor.
* gw_exact HB1G.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. gw_exact I1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. gw_exact NF1.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
* change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
+ unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; gw_exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
+ gw_exact MR4.
+ gw_exact MI4.
+ apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [gw_exact OOK2 | gw_exact MRW | gw_exact LO |].
eapply rpres_except_trans; [gw_exact PE3|]. eapply rpres_except_mono; [gw_exact PE4|].
intros a Ha. eapply (rfree_fp_same stX stU); [gw_exact ERU | gw_exact ESU | unfold stU; apply fg_usage_groups | gw_exact Ha].
+ rewrite SPU. gw_exact ST4.
+ rewrite SPU. lia.
+
intros st3 mi ms5 NQ. rewrite free_meta_eq.
unfold rntf_q in NQ. rewrite SPU in NQ.
destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
try g_ret_pc_any.
assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
{ apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
assert (NGM3 : ~ is_gm st3 g).
{ intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). gw_exact Hb. }
eapply rimplT_evt.
{ eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
first [gw_exact MR5 | gw_exact MI5 | gw_exact LO | gw_exact LOLE | reflexivity | idtac].
- unfold meta_slot. rewrite (nf_areas _ _ FR35). gw_exact MSG.
- intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; gw_exact GNU| gw_exact Hhd].
- unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
- eapply rpres_except_rw_cells; [gw_exact PE5 | gw_exact FR4 |].
intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
- gw_exact ST5. }
intros ms6 RP. apply KH.
pose proof (frame_trans _ _ _ FRG FR35) as FR03.
pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try gw_exact RP.
* destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [gw_exact PE0|]];
(eapply rpres_except_trans; [eapply rpres_except_mono; [gw_exact PE3| gw_exact FPX]|]);
(eapply rpres_except_trans; [eapply rpres_except_mono; [gw_exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [gw_exact ERU | gw_exact ESU | unfold stU; apply fg_usage_groups | gw_exact Ha]]|]);
(eapply rpres_except_mono; [gw_exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [gw_exact FRG| lia| gw_exact Ha]]).
* intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [gw_exact FR03| lia| gw_exact Ha].
* exists c3. apply KINV_fm; [gw_exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); gw_exact MSG| gw_exact NGM3| rewrite RG3; gw_exact GNU|].
intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). gw_exact Hs.
* apply ZINV_fm. gw_exact ZI3.
* unfold fm_st. apply frame_queue.
-- apply frame_put_meta; [gw_exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
-- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; gw_exact GNU].
-- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; gw_exact GNU| gw_exact NX'].
-- right; exact (hosts_is_gm _ _ _ HOSTS).
* destruct mi as [[bb len]|]; [| gw_exact RES5].
destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
split; [gw_exact A1|]. split; [gw_exact LEN|]. split; [gw_exact SND|]. split; [exists rr; rewrite FS1; auto|].
intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
* gw_exact OOK5.
* gw_exact MR5.
* gw_exact FS1.
* gw_exact FS2. }

assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
(m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono segs m m4 -> mem_inv segs m4 ->
stk segs m4 lo (bv_unsigned sp + -96) -> rw_cells segs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
F (Z_to_bv 64 (base + 0x228)) fc None m4 (seg_rom segs) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
{ intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
eapply rimplT_evt.
{ eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
first [gw_exact MR4 | gw_exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | gw_exact USX | gw_exact FR4 | apply rntf_frame_size | gw_exact ST4 | gw_exact LO | gw_exact LOLE]. }
intros ms5 FGP.
eapply (FG2 stX m4 junk); [gw_exact KIX | gw_exact ZIX | gw_exact LPX | gw_exact FRX | gw_exact GNX | right; gw_exact PE4 | gw_exact FGP | | gw_exact WM4 | | gw_exact DATX | exists m4; gw_exact MR4].
- intros a Ha. eapply (rfree_fp_same st stX); eauto.
- apply (oracle_ok_frame o m4 st stX); [| gw_exact ERX | gw_exact ESX].
eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [gw_exact OOK | gw_exact MR | gw_exact LO | gw_exact PE4]. }
destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
+
apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
set (sc := m_sizeclass (get_meta_rec st g)) in *.
set (an := optr_eqb (active st sc) (Some g)).
set (stm := deq_mid (LActive sc) g st).
set (st1 := dequeue (LActive sc) g st).
assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; gw_exact ZI).
assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [gw_exact SBL1| gw_exact LP]).
assert (FR1' : ntf_frame st st1).
{ unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
destruct DS as (DSdata & GN1 & GP1 & _).

assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono segs m m2 ->
rat9c_post ra sp gp tp s0 (Z_to_bv 64 (RATP + 131696)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
(rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (match an, active st1 sc with
| true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
| _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
end) s Q ms2).
{ intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| gw_exact PE3]| eapply rpres_except_trans; [gw_exact PE0| gw_exact PE3]]. }

assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
{ pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). unfold alloc_ceiling in B1.
rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
- destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). unfold alloc_ceiling in C1.
unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). gw_exact E.
- unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
evt segs (rat00_post ra sp gp tp s0 (Z_to_bv 64 (RATP + 131696)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 (base + 0x1c4)) fc None m3 (seg_rom segs))).
{ intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
first [gw_exact MR3 | gw_exact MI3 | gw_exact HA3 | gw_exact FR3 | apply rntf_frame_size | gw_exact ST3 | gw_exact LO | gw_exact LOLE | idtac].
- eapply meta_slot_sbl; [gw_exact SBLm| gw_exact MSL].
- pose proof (go_sc _ _ _ GO). subst sc. lia.
- rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
split; [gw_exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [gw_exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [gw_exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
assert (AVK : forall a, an = true -> active st1 sc = Some a ->
rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 (base + 0x1c4)) fc None m3 (seg_rom segs))).
{ intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
set (stA := act_st st1 a (act_of st1 a)).
destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; gw_exact AV0|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX stA m4 junk); try reflexivity; try gw_exact MR4; try gw_exact MI4; try gw_exact ST4; try gw_exact FR4.
- unfold stA. apply KINV_act; [gw_exact KI1| gw_exact GMa| gw_exact AV0| apply act_of_nonneg].
- unfold stA. apply ZINV_act. gw_exact ZI1.
- unfold stA, act_st. apply LPRE_upd_other; [gw_exact NEa| gw_exact LP1].
- unfold stA. apply frame_act; [gw_exact FR1'| eapply (LG_frame st st1 a FR1'); left; gw_exact Na].
- unfold stA. rewrite act_st_rec_other by congruence. gw_exact GN1.
- unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
- unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
- unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
- unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
- unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [gw_exact PE03|]. eapply rpres_except_mono; [gw_exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| gw_exact WM4]. eapply wmono_trans; [gw_exact WM2| gw_exact WM3]. }
assert (NOACT : (an = false \/ active st1 sc = None) ->
rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 ((RATP + 131968) + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 (base + 0x1c4)) fc None m3 (seg_rom segs))).
{ intros NA.
eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
rewrite EP in MR4.
rewrite (conc_sbl _ _ g SBLm).
eapply (FGX st1 m4 junk); try reflexivity; try gw_exact MR4; try gw_exact MI4; try gw_exact ST4; try gw_exact FR4; try gw_exact KI1; try gw_exact ZI1; try gw_exact LP1; try gw_exact FR1'; try gw_exact GN1.
- apply DSdata.
- apply (sbl_regions _ _ SBL1).
- apply (sbl_shadow _ _ SBL1).
- apply (sbl_groups _ _ SBL1).
- intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
- eapply rpres_except_trans; [gw_exact PE03|]. eapply rpres_except_mono; [gw_exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
- eapply wmono_trans; [| gw_exact WM4]. eapply wmono_trans; [gw_exact WM2| gw_exact WM3]. }
destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| gw_exact SC48b]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); congruence).
*
destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx = g) by congruence.
eapply rimplT_evt.
{ eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL | gw_exact FR1 | apply rntf_frame_size | gw_exact ST1 | gw_exact LO | gw_exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- rewrite NX, Enx. reflexivity. }
intros ms2 AP. eapply (DQ2 m1 junk); [left; gw_exact MU| gw_exact WM| gw_exact AP].
*
destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
assert (Enx : nx' = nx) by congruence. subst nx'.
eapply rimplT_evt.
{ eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL | gw_exact NX | gw_exact PV | gw_exact NE | gw_exact MSnx | gw_exact MSpv | gw_exact FR1 | apply rntf_frame_size | gw_exact ST1 | gw_exact LO | gw_exact LOLE | reflexivity | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- apply NEpv. gw_exact NE.
- destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
intros ms2 AP. eapply (DQ2 m1 junk); [left; gw_exact MU| gw_exact WM| gw_exact AP].
+
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]];
try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
eapply (FGX st m1 junk); [gw_exact KI | gw_exact ZI | gw_exact LP | apply frame_refl | gw_exact NX | reflexivity | reflexivity | reflexivity | reflexivity
| | eapply rpres_except_entry; eauto | gw_exact WM | gw_exact MI1 | gw_exact ST1 | gw_exact FR1 | gw_exact MR1 | reflexivity].
intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
- destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
+
apply Z.eqb_eq in HM.
apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.

assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
(active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 (RATP + 131696)) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
rimplT o (k (aor_st stq g i) None) s Q ms2).
{ intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); gw_exact ZI).
assert (KIq : KINV stq LB c).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [gw_exact KI|].
apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
- intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
assert (FRq : ntf_frame st stq).
{ rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
unfold rqpath_post in QP. cbv beta in QP.
destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
rewrite <- (conc_sbl st stq g SBL).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
first [gw_exact MR2 | gw_exact MI2 | reflexivity | gw_exact FR2 | gw_exact ST2 | gw_exact LO | gw_exact LOLE | idtac].
- eapply meta_slot_sbl; [gw_exact SBL| gw_exact MSL].
- pose proof (go_li _ _ _ GO). lia.
- destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
intros ms3 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try gw_exact RP.
* eapply rpres_except_trans; [eapply rpres_except_entry; eauto| gw_exact PE2].
* intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [gw_exact FRq| lia| gw_exact Ha].
* exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
* apply ZINV_aor. gw_exact ZIq.
* apply frame_aor; [gw_exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
eapply (roracle_ok_pres o _ _ st lo _ m); [gw_exact OOK| gw_exact MR| gw_exact LO|].
eapply rpres_except_trans; [eapply rpres_except_entry; eauto| gw_exact PE2].
* gw_exact MR2.
* reflexivity.
* reflexivity. }
destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
{ destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia | gw_exact HAct]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL | gw_exact FR1 | apply rntf_frame_size | gw_exact ST1 | gw_exact LO | gw_exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- right. exists g. split; [gw_exact HAct| gw_exact MSL].
- intros NE. exfalso. exact (NE HAct).
- intros hd Hhd NE. exfalso. apply NE. congruence. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [gw_exact MU| gw_exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| gw_exact QP].
*
assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
{ intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
apply rimplT_queue. intros GN GPV.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence | lia]|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL | gw_exact FR1 | apply rntf_frame_size | gw_exact ST1 | gw_exact LO | gw_exact LOLE | idtac].
- pose proof (go_sc _ _ _ GO). lia.
- destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
- intros _. split; assumption.
- intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
split; [gw_exact Shd|]. exists pv. split; [gw_exact Ppv|]. split; [| gw_exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
eapply (QTAIL m1 junk); [gw_exact MU| gw_exact WM| reflexivity| intros _; split; assumption| gw_exact QP].
+
apply Z.eqb_neq in HM.
eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
eapply rimplT_evt.
{ eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
first [gw_exact MR1 | gw_exact MI1 | gw_exact MSL | reflexivity | gw_exact FR1 | gw_exact ST1 | gw_exact LO | gw_exact LOLE | idtac].
- pose proof (go_li _ _ _ GO). lia.
- exact (go_freed _ _ _ GO). }
intros ms2 RP. apply KH.
eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try gw_exact RP.
* eapply rpres_except_entry; eauto.
* auto.
* exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
* apply ZINV_aor. gw_exact ZI.
* apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
* exact eq_refl.
* eapply (roracle_ok_pres o _ _ st lo _ m); [gw_exact OOK| gw_exact MR| gw_exact LO| eapply rpres_except_entry; eauto].
* gw_exact MR1.
* reflexivity.
* reflexivity.
Qed.
End NTF.

End RC__1.

End G.
End Mqp.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import StepGenSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_ecall ::= g_step_ecall. Local Ltac mkr__step_ecall_2 := g_step_ecall.
Local Ltac sys_nret ::= g_sys_nret. Local Ltac mkr__sys_nret_3 := g_sys_nret.
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
Notation gw_tbl_1 := (gw_ent (@QROt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_0)))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QROt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_1)))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QROt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2)))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QROt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3)))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QROt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_4)))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QROt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_5)))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QROt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_6)))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QROt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7)))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QROt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8)))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QROt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9)))))))))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrw_cells_agree) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrw_cells_agree)).
Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Notation RMallocKit_B__rrw_cells_agree := rrw_cells_agree (only parsing).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x144)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
st1. rewrite bv_eqb_refl. cbv iota.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (rid : N) (off : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
(Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x12c)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until off. intros MR CNT BRK C0 C1b.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1. st1. st1.
apply evt_done. reflexivity.
Qed.

Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_brk0_node :
impl segs (at_node segs) (enode (NBrk 0) dec_brk0)
(epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 (base + 0x148)) fc None m (seg_rom segs) /\ 0 <= r < 2^64))
(MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 (base + 0x144)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m. first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear x1 | gw_hide x1 | idtac].
unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace ((base + 0x144) + 4)%Z with (base + 0x148)%Z by first [reflexivity | (cbn; lia)].
apply evt_done. split; [reflexivity| gw_exact Hr].
Qed.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_brk_node_at (pc : Z) :
(pc = (base + 0x12c) \/ pc = (base + 0x168)) -> forall cur req, req <> 0 ->
impl segs (at_node segs) (enode (NBrk req) (dec_brk cur req))
(epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom segs)))
(MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base pc x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m. first [clear m | gw_hide m | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a6 | gw_hide a6 | idtac]; first [clear a5 | gw_hide a5 | idtac]; first [clear a4 | gw_hide a4 | idtac]; first [clear a3 | gw_hide a3 | idtac]; first [clear a2 | gw_hide a2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear t1 | gw_hide t1 | idtac]; first [clear t0 | gw_hide t0 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear x1 | gw_hide x1 | idtac].
intros Hpc cur req NZ. unfold rbrk_regs.
destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
[ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
| rewrite apply_mem_none ];
apply evt_done; reflexivity).
Qed.
End BRKNODES.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry"] Lemma ram_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
(m : word -> option byte) (cur : Z),
0 < cur < 2^64 -> cur mod 4096 = 0 ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 q2] -> mem_inv segs m ->
evt segs (fun ms' => exists a2' m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x168)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' ((RATP + 132880)) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x148)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until cur. intros CR CAL TC MI.
pose proof (munch_refl [((RATP + 132888), (RATP + 132896))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (land_neg_aligned cur CR CAL) as AL.
assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; gw_exact AL).
change (cur mod 4096 = 0) with (pgal cur) in CAL.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in TC. change ((RATP + 132888)) with (RATP + 132888) in MU. change ((RATP + 132896)) with (RATP + 132896) in MU.

st1. st1. rewrite ?AL, ?AL'. st1. st1.
replace (0 + cur) with cur by lia.

st1. st1. st1. st1.
replace (8192 + cur) with (cur + 8192) by lia.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. gw_exact TC.
Qed.

#[using="w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 CODE D_98 E_98 LINK_98 rmmap_entry rmprotect_entry"] Lemma ram_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
(m : word -> option byte) (cur : Z),
0 < cur -> cur + 8192 < 2^64 ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
evt segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 (base + 0x18c)) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
(Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x16c)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_98 CODE D_98 E_98 LINK_98 rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until cur. intros C0 C1b TC.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in TC.

st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry"] Lemma ram_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells segs m (RATP + 131968) [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 q2] -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x218)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132008), (RATP + 132016)); ((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (RATP + 131968) [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells segs m' ((RATP + 132880)) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x18c)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until nw. intros NW HC TC MI.
pose proof (munch_refl [((RATP + 132008), (RATP + 132016)); ((RATP + 132888), (RATP + 132896))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in TC.
change ((RATP + 132008)) with (RATP + 132008) in MU. change ((RATP + 132016)) with (RATP + 132016) in MU. change ((RATP + 132888)) with (RATP + 132888) in MU. change ((RATP + 132896)) with (RATP + 132896) in MU.

st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
apply evt_done. eexists. split; [reflexivity|]. split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact HC| gw_exact TC].
Qed.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry"] Lemma ram_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
0 <= nw < 2^64 ->
rw_cells segs m (RATP + 131968) [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 q2] -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x218)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132008), (RATP + 132016)); ((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (RATP + 131968) [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
/\ rw_cells segs m' ((RATP + 132880)) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x130)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until nw. intros NW HC TC MI.

st1. rewrite bv_eqb_refl. cbv iota.
eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
rmrep st m0 -> munch [((RATP + 132888), (RATP + 132896))]%Z m0 m -> wmono segs m0 m ->
c_avail_meta_area_count (ctx st) = 0 ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1a0)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
lazymatch type of C1 with rw_cells _ _ _ ?cs =>
assert (C1' : rw_cells segs m (RATP + 131968) cs)
by (eapply RMallocKit_B__rrw_cells_agree; [gw_exact C1| | gw_exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
rewrite wa_unsigned by (gw_expose_fam RATP; lia); gw_expose_fam RATP; cbn; lia) end.
clear C1.
pose proof (munch_refl [((RATP + 132888), (RATP + 132896))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in TC.
change ((RATP + 132888)) with (RATP + 132888) in MU, MU0. change ((RATP + 132896)) with (RATP + 132896) in MU, MU0.

st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
{ eapply (rmrep_ctx_frameW st _ m0 _ [((RATP + 132888), (RATP + 132896))]%Z MR); try reflexivity.
- gw_expose_fam RATP. first [gw_exact MU0 | eapply munch_trans; [gw_exact MU0| gw_exact MU]].
- first [gw_exact WM0 | eapply wmono_trans; [gw_exact WM0| gw_exact WM]].
- intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_tail_cells, brk_word). cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change ((RATP + 132880)) with (RATP + 132880).
replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
lazymatch goal with H : rw_cells segs ?mX (RATP + 132880) _ |- _ => exact H end. }
apply evt_done. eexists. split; [reflexivity|]. split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. gw_exact MR'.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
F fc (m : word -> option byte) (st : mstate) (old : Z),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x130)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until old. intros MR CNT O0 O1 MI.
pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.

st1.
assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
rewrite CF; clear CF.
st1.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl segs m) CNT C6 eq_refl eq_refl MI).
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
rmrep st m0 -> munch [((RATP + 132888), (RATP + 132896))]%Z m0 m -> wmono segs m0 m ->
c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
rw_cells segs m ((RATP + 132880)) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv segs m ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None m' (seg_rom segs)
/\ munch [((RATP + 132888), (RATP + 132896))]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rmrep (upd_ctx (set_brk BrkDead) st) m')
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x16c)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.

st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
{ apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
rewrite CF; clear CF.
eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End RC__1.

End G.
