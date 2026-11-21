(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed L_b84, L_bec, ffp_entry and 1 more; added FILE_cells4, cur_reg, file_cells4 and 7 more. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memset_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_memcpy_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fwritex_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_pad_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_frexpl_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_divtf3_main_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFp_split.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFp_splitR.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFp_splitH.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import FmtFp_facts_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import FmtFp_facts2_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_lib_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_calls_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_pre_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_pre2_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_pre3_u.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fmt_fp_pre4_u.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import StoreFast.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFpNF.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require F_fmt_fp_u.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* U/ twin of CJ/F10/F_fmt_fp_nf.v -- see the note there.  Several Require'd
   modules each declare their own [Definition rsegs], so [hyp]'s [constr_eq]
   rejects a convertible-but-not-syntactically-equal hypothesis.  Shadowed once
   rather than at fifteen call sites; [hyp0] keeps the original first. *)
Ltac hyp0 := hyp.
Ltac hyp := first [hyp0 | assumption].
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "Corelib.Init.Datatypes.option"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.mem_inv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.rsegs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.ro_bytes_at"; "Corelib.Numbers.BinNums.Zpos"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.zb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.INF_LC"; "Corelib.Init.Datatypes.nil"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Corelib.Init.Datatypes.list"; "Stdlib.micromega.VarMap.Empty"; "Corelib.Numbers.BinNums.Z"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEc"; "Corelib.Numbers.BinNums.Z0"; "Stdlib.micromega.RingMicromega.OpLe"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Logic.eq_refl"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.eq"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.micromega.ZifyClasses.mkrel"; "Corelib.Init.Logic.iff_refl"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.micromega.ZifyClasses.inj"; "Stdlib.micromega.ZifyInst.Inj_Z_Z"; "Stdlib.micromega.ZifyClasses.mkapp"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.True"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "Corelib.Init.Datatypes.comparison"; "Stdlib.ZArith.BinInt.Z.compare"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.EnvRing.PEpow"; "Corelib.Init.Datatypes.length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Image.ro_bytes_b_sound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Image.ro_bytes_b"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Arr.u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.NAN_LC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.INF_UC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.NAN_UC"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.SoftFloat.f128_le"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_INF_u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_NAN_u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_inf_u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_nan_u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_addr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.nf_str"; "Corelib.Init.Logic.and"; "Stdlib.micromega.Tauto.AND"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_frexpl_u.f128_le_cases"; "Corelib.Init.Logic.or"; "Corelib.Numbers.BinNums.Zneg"; "Corelib.Numbers.BinNums.xH"; "Corelib.Init.Logic.iff"; "Corelib.Init.Logic.eq_ind_r"; "Corelib.Init.Logic.conj"; "Corelib.Init.Logic.eq_ind"; "Corelib.Init.Logic.False"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Logic.I"; "Corelib.Init.Logic.False_ind"; "Corelib.Init.Datatypes.list_ind"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.lor_nonneg"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Corelib.Numbers.BinNums.N"; "stdpp.bitvector.definitions.bv_modulus"; "stdpp.bitvector.definitions.bv_unsigned_in_range"; "Stdlib.ZArith.BinInt.Z.shiftl_nonneg"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.bits_inj'"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.testbit"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.eqb_spec"; "Corelib.Init.Datatypes.reflect"; "Corelib.Init.Datatypes.false"; "Stdlib.Bool.Bool.orb_false_r"; "Stdlib.ZArith.BinInt.Z.testbit_neg_r"; "Stdlib.micromega.EnvRing.PEsub"; "Stdlib.micromega.RingMicromega.OpLt"; "Corelib.Init.Logic.not"; "Stdlib.Bool.Bool.andb_false_r"; "Stdlib.ZArith.BinInt.Z.pow2_bits_eqb"; "Stdlib.ZArith.BinInt.Z.shiftl_spec"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.EnvRing.PEX"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.lor_spec"; "Stdlib.ZArith.BinInt.Z.land_spec"; "Stdlib.ZArith.BinInt.Z.ones"; "stdpp.tactics.f_equal_help"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mod_small"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.ZArith.BinInt.Z.land_ones"; "Stdlib.ZArith.BinInt.Z.land_comm"; "Stdlib.ZArith.BinInt.Z.land_assoc"; "stdpp.bitvector.definitions.bv_wrap"; "Corelib.Lists.ListDef.firstn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.lor_shl8_land32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.bytes_le_to_Z_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.land_mod_pow2_small"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.Z_to_bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.O"; "stdpp.bitvector.definitions.bv_extract"; "Corelib.Numbers.BinNums.N0"; "Stdlib.ZArith.BinInt.Z.of_N"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.w4_core"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.extract_low_mod"; "Stdlib.NArith.BinNat.N.lt"; "Stdlib.ZArith.Znat.N2Z.inj_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.unsigned_lit"; "LinuxProcessSemantics.Riscv.Prelude.zext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.zext_small"; "stdpp.bitvector.definitions.bv_signed"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.LiaTuning.zify_done"; "Stdlib.micromega.RingMicromega.OpEq"; "Stdlib.ZArith.Zdiv.Zminus_mod_idemp_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.signed_of_extract"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.unsigned_lit_wrap"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.sext_small"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.Fp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.MS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.mkR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.Wfp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.FP.frm0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fwritex_u.wfile"; "Corelib.Init.Nat.sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_pad_u.ssp_cells"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.CB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.C8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.hi_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_pad_u.got_ssp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_pad_u.ssp_guard"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.finv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.b2z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFp_split.ffp_sign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.yv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.fmt_fp_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.SoftFloat.hi64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.SoftFloat.lo64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_memcpy_u.rsegs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fwritex_u.FILE_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_word"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.fmt_fp_nf"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.leb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.fpclassifyl"; "Corelib.Init.Datatypes.app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.zsub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.PREFIX_STR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_step"; "LinuxProcessSemantics.Riscv.Prelude.TNode"; "LinuxProcessSemantics.Riscv.Prelude.TEmpty"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.lift_result"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.interp_eff0"; "LinuxProcessSemantics.Riscv.Sem.exec"; "LinuxProcessSemantics.Riscv.Instr.OpImm"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "stdpp.bitvector.definitions.BV"; "stdpp.bitvector.definitions.Z_to_bv_obligation_1"; "LinuxProcessSemantics.Riscv.Sem.Core"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addi"; "stdpp.bitvector.definitions.bv_add"; "Stdlib.ZArith.BinInt.Z.add_0_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.unsigned_Z_to_bv_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.lit_add_lit"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_addi"; "LinuxProcessSemantics.Riscv.Prelude.tset"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_set"; "LinuxProcessSemantics.Riscv.Prelude.tget"; "LinuxProcessSemantics.Riscv.Sem.w0"; "LinuxProcessSemantics.Riscv.Sem.core"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.step_gen"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.Riscv.Instr.Jal"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_addsext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_cut"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.fpclassifyl_postv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.fpclassifyl_callv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.ivl"; "Corelib.Init.Logic.eq_sym"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc_even"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.Znat.Nat2Z.inj_lt"; "Stdlib.ZArith.Znat.Nat2Z.is_nonneg"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.w0_lit"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Prelude.bv_lts"; "LinuxProcessSemantics.Riscv.Instr.Branch"; "LinuxProcessSemantics.Riscv.Instr.BC_GE"; "Stdlib.ZArith.BinInt.Z.ltb"; "Corelib.Init.Logic.proj1"; "Stdlib.Bool.Bool.negb_true_iff"; "Stdlib.ZArith.BinInt.Z.ltb_ge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SFModel.signed_of_Z"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.fpclassifyl_range"; "Stdlib.micromega.EnvRing.PEopp"; "Stdlib.ZArith.BinInt.Z.opp"; "Corelib.Init.Logic.proj2"; "Stdlib.ZArith.BinInt.Z.leb_le"; "Stdlib.Bool.Bool.andb_true_iff"; "Stdlib.micromega.Tauto.X"; "Corelib.Init.Logic.f_equal"; "Corelib.BinNums.PosDef.Pos.add"; "Stdlib.ZArith.BinInt.Z.pos_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.zsub_length"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.ZArith.Znat.Nat2Z.inj_le"; "Stdlib.Arith.PeanoNat.Nat.add"; "Stdlib.ZArith.Znat.Nat2Z.inj_add"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "Stdlib.ZArith.BinInt.Z.max_spec"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.Tauto.OR"; "Corelib.Init.Logic.iff_sym"; "Stdlib.ZArith.Znat.Nat2Z.inj_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.nf_str_length"; "Stdlib.Lists.List.length_app"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_andi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_andi"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.leaf1_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.letf2_callv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.rw_cells_transport"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.disjoint_from"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cells_size"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_transport_disjoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_weaken"; "Stdlib.micromega.Tauto.TT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.outside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.sub_fp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_addr_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Tac.rw_cells_merge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cells_bytes"; "LinuxProcessSemantics.Riscv.Instr.Load"; "LinuxProcessSemantics.Riscv.Instr.SZ4"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineFault"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineUnmodeled"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_cb_split"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cb_split_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cb_split"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_read_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.csize"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.wa"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.wa_of_Z_to_bv"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Instr.BC_NE"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.inr64_unsigned_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_land_lit"; "Stdlib.ZArith.BinInt.Z.eqb_neq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.w4_bit5"; "Stdlib.micromega.Tauto.NOT"; "Stdlib.Bool.Bool.negb_false_iff"; "Stdlib.ZArith.BinInt.Z.eqb_eq"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.le8"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.load_u64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.bytes_at_slice"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre2_u.prefix_u8ro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.zb_length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.bytes_at"; "Stdlib.ZArith.Znat.Z2Nat.id"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.zb_zsub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_split"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fwritex_u.fwritex_postZ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.fwritex_callR"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.bytes_at_transport"; "Stdlib.micromega.ZifyClasses.and_morph"; "Stdlib.micromega.ZifyClasses.or_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_merge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.w4s_bit5"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.nfs_u8ro"; "Stdlib.Arith.PeanoNat.Nat.sub"; "Stdlib.ZArith.Znat.Nat2Z.inj_sub_max"; "Stdlib.Lists.List.length_skipn"; "LinuxProcessSemantics.Riscv.Instr.Lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_lui"; "stdpp.bitvector.definitions.bv_concat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_lui"; "LinuxProcessSemantics.Riscv.Instr.Op"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_and"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_and"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "LinuxProcessSemantics.Riscv.Instr.BC_LTU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_lit"; "Stdlib.ZArith.BinInt.Z.ltb_lt"; "Stdlib.ZArith.BinInt.Z.add_assoc"; "LinuxProcessSemantics.Riscv.Instr.BC_EQ"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.Z_to_bv_lit_self"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_release"; "LinuxProcessSemantics.Riscv.Instr.Jalr"; "stdpp.bitvector.definitions.bv_and"; "stdpp.bitvector.definitions.bv_not"; "LinuxProcessSemantics.Riscv.Sem.w1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc_fold"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.w1_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_done"; "Corelib.Init.Logic.ex_intro"; "LinuxProcessSemantics.Riscv.Prelude.tree"; "Stdlib.Lists.List.app_assoc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_pre4_u.zb_app"; "Stdlib.Lists.List.skipn_skipn"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"; "OSSVerify.jsoncons.fuzz_json_cursor.images.Ubsan.Ubsan_loaded_segments"; "LinuxProcessSemantics.Riscv.Instr.ShiftImm"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_slli"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_slli"; "LinuxProcessSemantics.Riscv.Instr.BC_LT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.bv_lts_zero_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.unsigned_lit_land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_eq"; "Stdlib.ZArith.BinInt.Z.leb_gt"; "LinuxProcessSemantics.Riscv.Instr.Auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.unsigned_Z_to_bv_add_r"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_auipc"; "Corelib.Classes.Morphisms.subrelation_proper"; "Corelib.Classes.Morphisms.respectful"; "Corelib.Classes.Morphisms_Prop.not_iff_morphism"; "Corelib.Program.Basics.impl"; "Corelib.Classes.Morphisms.subrelation_respectful"; "Corelib.Classes.Morphisms.subrelation_refl"; "Corelib.Classes.Morphisms.iff_impl_subrelation"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.le_land0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.lo64_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.hi64_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.signbitl_postv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.signbitl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.signbitl_callv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA.SFW1_lemmas.land_W64_small"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.signbitl_range"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.shl52_land64"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_store_ok_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.mem_inv_store_cbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_store_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_write"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell_upd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.StoreFast.rw_cells_frame_n"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.StoreFast.munch_write_n"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.inside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_write"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.StoreFast.stk_write_n"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.L_bec"; "Stdlib.ZArith.BinInt.Z.lxor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.F128_SIGNBIT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.PAD_POS"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.RingMicromega.PsatzC"; "Stdlib.micromega.EnvRing.PEmul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.land_bit11"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.MARK_POS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.le8_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.store_bytes_8'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_mod_any"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sltiu"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLTU"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sltiu"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_lib_u.land_bit0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.v_sltiu_b2z"; "stdpp.bitvector.definitions.bv_eq"; "LinuxProcessSemantics.Riscv.Instr.ALU_XOR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_xor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_xor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.lo64_flip_sign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_calls_u.hi64_flip_sign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.Z_to_bv_bv_unsigned"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA.SFW1_lemmas.lo64_words"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA.SFW1_lemmas.hi64_words"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_carve"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Tac.rw_cells_split_CB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Tac.mk_CB_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fwritex_u.rw_cells_app"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_of_rw_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.le4"; "LinuxProcessSemantics.Riscv.Sem.low32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.store_bytes_4'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.FmtFp.L_b84"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_u.FMT_FP_DEPTH"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_u.fmt_fp_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_mono"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.fmt_fp_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.NF.ffp_entry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.fmt_fp_nf_stmt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.nonfinite"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_u.fmt_fp_facts"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.fmt_fp'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.fmt_fp_facts'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.nonfinite_dec"; "Corelib.Init.Specif.sumbool"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.fmt_fp'_nonfinite"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.fmt_fp_nf_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.fmt_fp_nf_w"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec.FmtFp.fmt_fp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10.FmtFpNF.fmt_fp'_finite"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_u.fmt_fp_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10.F_fmt_fp_nf_u.fmt_fp'_stmt"].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.

Module NF.

Lemma nfs_inf_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 71905 (zb INF_LC).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "U29;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;o6;Y16;18e1;A1;k7;k8;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#4;A2;k25;#10;o19;A2;o27;i28;o29;A4;k26;r1;r3;cv#13;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;N3;A1;k36;#15;A2;k35;#4;#16;Y1;0;A1;o6;#18;A1;o6;#0;A2;k37;#19;#20;A1;o6;Y1;1;A2;k35;#4;#22;A2;k33;#23;#21;Lx;Ri13;r1;A2;k46;o22;#19;P~RA2;k33;o22;#20;A2;k46;o22;#21;A2;k33;o22;#19;Lm;RP~RA1;i0;#1;A1;i2;#3;LMI;RA2;k3;k4;r1;cdA8;k5;k4;r2;#4;#5;r1;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A2;o21;i13;o22;o23;#11;o24;#12;#14;A2;k33;o22;#4;r1;cdA4;k34;A2;k33;#17;#21;#24;A12;k38;i13;i13;k33;#25;k33;Lx;Ri13;Ly;Ri13;A1;k39;A2;k33;r2;r1;#17;#23;A18;k40;i13;i13;i13;i13;i13;i13;k35;#25;#25;#25;k35;Ln;Ri13;Lm;Ri13;A2;o27;i13;A4;k41;i13;i13;k42;A2;k35;r2;r1;#4;#4;A2;o27;i13;#4;#16;#22;A12;k43;i44;i13;i13;i13;k36;k36;#25;#25;Lx;Ri44;A2;o27;i13;A1;k36;r1;#15;#22;A2;o27;i13;#22;#21;#21;A2;o27;i13;#21;E__sat1;RA2;k45;#19;#20;P~R#26;#27;E__sat0;RLHa;R#28;L~Ri47;A3;k48;#19;#20;r2;PHa;R#28;P~Ri47;A2;k33;o22;#21;E__sat1;RA1;r2;cdA2;o27;i49;A2;k50;o22;#19;#26;#27;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A3;o51;i13;#11;A2;o21;i13;#22;o23;A3;o52;i13;A2;o21;i13;#19;#1;o24;#12;#14;#24;r1;A2;k33;A2;k35;#4;A1;k36;A2;k53;#3;#5;#21;A4;k54;k4;#5;#4;cv#13;A3;i30;i28;A3;k55;k4;#4;#5;o29;A4;k56;k4;r2;#4;#5;").
Qed.
Lemma nfs_nan_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 79511 (zb NAN_LC).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S29;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;o6;Y16;3697;A1;k7;k57;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#4;A2;k25;#10;o19;A2;o27;i28;o29;A4;k26;r1;r3;cv#13;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;N3;A1;k36;#15;A2;k35;#4;#16;Y1;0;A1;o6;#18;A1;o6;#0;A2;k37;#19;#20;A1;o6;Y1;1;A2;k35;#4;#22;A2;k33;#23;#21;Lx;Ri13;r1;A2;k46;o22;#19;P~RA2;k33;o22;#20;A2;k46;o22;#21;A2;k33;o22;#19;Lm;RP~RA1;i0;#1;A1;i2;#3;LMI;RA2;k3;k4;r1;cdA8;k5;k4;r2;#4;#5;r1;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A2;o21;i13;o22;o23;#11;o24;#12;#14;A2;k33;o22;#4;r1;cdA4;k34;A2;k33;#17;#21;#24;A12;k38;i13;i13;k33;#25;k33;Lx;Ri13;Ly;Ri13;A1;k39;A2;k33;r2;r1;#17;#23;A18;k40;i13;i13;i13;i13;i13;i13;k35;#25;#25;#25;k35;Ln;Ri13;Lm;Ri13;A2;o27;i13;A4;k41;i13;i13;k42;A2;k35;r2;r1;#4;#4;A2;o27;i13;#4;#16;#22;A12;k43;i44;i13;i13;i13;k36;k36;#25;#25;Lx;Ri44;A2;o27;i13;A1;k36;r1;#15;#22;A2;o27;i13;#22;#21;#21;A2;o27;i13;#21;E__sat1;RA2;k45;#19;#20;P~R#26;#27;E__sat0;RLHa;R#28;L~Ri47;A3;k48;#19;#20;r2;PHa;R#28;P~Ri47;A2;k33;o22;#21;E__sat1;RA1;r2;cdA2;o27;i49;A2;k50;o22;#19;#26;#27;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A3;o51;i13;#11;A2;o21;i13;#22;o23;A3;o52;i13;A2;o21;i13;#19;#1;o24;#12;#14;#24;r1;A2;k33;A2;k35;#4;A1;k36;A2;k53;#3;#5;#21;A4;k54;k4;#5;#4;cv#13;A3;i30;i28;A3;k55;k4;#4;#5;o29;A4;k56;k4;r2;#4;#5;").
Qed.
Lemma nfs_INF_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 74459 (zb INF_UC).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S29;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;o6;Y16;22db;A1;k7;k58;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#4;A2;k25;#10;o19;A2;o27;i28;o29;A4;k26;r1;r3;cv#13;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;N3;A1;k36;#15;A2;k35;#4;#16;Y1;0;A1;o6;#18;A1;o6;#0;A2;k37;#19;#20;A1;o6;Y1;1;A2;k35;#4;#22;A2;k33;#23;#21;Lx;Ri13;r1;A2;k46;o22;#19;P~RA2;k33;o22;#20;A2;k46;o22;#21;A2;k33;o22;#19;Lm;RP~RA1;i0;#1;A1;i2;#3;LMI;RA2;k3;k4;r1;cdA8;k5;k4;r2;#4;#5;r1;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A2;o21;i13;o22;o23;#11;o24;#12;#14;A2;k33;o22;#4;r1;cdA4;k34;A2;k33;#17;#21;#24;A12;k38;i13;i13;k33;#25;k33;Lx;Ri13;Ly;Ri13;A1;k39;A2;k33;r2;r1;#17;#23;A18;k40;i13;i13;i13;i13;i13;i13;k35;#25;#25;#25;k35;Ln;Ri13;Lm;Ri13;A2;o27;i13;A4;k41;i13;i13;k42;A2;k35;r2;r1;#4;#4;A2;o27;i13;#4;#16;#22;A12;k43;i44;i13;i13;i13;k36;k36;#25;#25;Lx;Ri44;A2;o27;i13;A1;k36;r1;#15;#22;A2;o27;i13;#22;#21;#21;A2;o27;i13;#21;E__sat1;RA2;k45;#19;#20;P~R#26;#27;E__sat0;RLHa;R#28;L~Ri47;A3;k48;#19;#20;r2;PHa;R#28;P~Ri47;A2;k33;o22;#21;E__sat1;RA1;r2;cdA2;o27;i49;A2;k50;o22;#19;#26;#27;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A3;o51;i13;#11;A2;o21;i13;#22;o23;A3;o52;i13;A2;o21;i13;#19;#1;o24;#12;#14;#24;r1;A2;k33;A2;k35;#4;A1;k36;A2;k53;#3;#5;#21;A4;k54;k4;#5;#4;cv#13;A3;i30;i28;A3;k55;k4;#4;#5;o29;A4;k56;k4;r2;#4;#5;").
Qed.
Lemma nfs_NAN_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 78713 (zb NAN_UC).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S29;Y6;00;A1;o1;#0;Y3;0;A1;i0;A1;o1;#2;A1;o6;Y16;3379;A1;k7;k59;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#4;A2;k25;#10;o19;A2;o27;i28;o29;A4;k26;r1;r3;cv#13;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;N3;A1;k36;#15;A2;k35;#4;#16;Y1;0;A1;o6;#18;A1;o6;#0;A2;k37;#19;#20;A1;o6;Y1;1;A2;k35;#4;#22;A2;k33;#23;#21;Lx;Ri13;r1;A2;k46;o22;#19;P~RA2;k33;o22;#20;A2;k46;o22;#21;A2;k33;o22;#19;Lm;RP~RA1;i0;#1;A1;i2;#3;LMI;RA2;k3;k4;r1;cdA8;k5;k4;r2;#4;#5;r1;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A2;o21;i13;o22;o23;#11;o24;#12;#14;A2;k33;o22;#4;r1;cdA4;k34;A2;k33;#17;#21;#24;A12;k38;i13;i13;k33;#25;k33;Lx;Ri13;Ly;Ri13;A1;k39;A2;k33;r2;r1;#17;#23;A18;k40;i13;i13;i13;i13;i13;i13;k35;#25;#25;#25;k35;Ln;Ri13;Lm;Ri13;A2;o27;i13;A4;k41;i13;i13;k42;A2;k35;r2;r1;#4;#4;A2;o27;i13;#4;#16;#22;A12;k43;i44;i13;i13;i13;k36;k36;#25;#25;Lx;Ri44;A2;o27;i13;A1;k36;r1;#15;#22;A2;o27;i13;#22;#21;#21;A2;o27;i13;#21;E__sat1;RA2;k45;#19;#20;P~R#26;#27;E__sat0;RLHa;R#28;L~Ri47;A3;k48;#19;#20;r2;PHa;R#28;P~Ri47;A2;k33;o22;#21;E__sat1;RA1;r2;cdA2;o27;i49;A2;k50;o22;#19;#26;#27;E__arith;RE__wit;R#6;#7;E__varmap;R#8;#9;E__ff;RA7;o15;#10;k17;i18;i18;o19;A4;o20;i13;A3;o51;i13;#11;A2;o21;i13;#22;o23;A3;o52;i13;A2;o21;i13;#19;#1;o24;#12;#14;#24;r1;A2;k33;A2;k35;#4;A1;k36;A2;k53;#3;#5;#21;A4;k54;k4;#5;#4;cv#13;A3;i30;i28;A3;k55;k4;#4;#5;o29;A4;k56;k4;r2;#4;#5;").
Qed.
Definition nfs_addr (y1 t : Z) : Z := ltac2:(Rpl.RP.run_k (rplG ()) 2 "S1;A2;k60;A2;k62;r2;r2;o22;Ly1;Ri13;Lt;Ri13;m28;RNL~Ri28;i13;A2;k60;A2;k61;r1;A1;o6;Y5;00;o22;2;m28;RNL~Ri28;i13;#0;2;A1;o6;Y16;22db;A1;o6;Y16;3379;m28;RNL~Ri28;i13;#0;2;A1;o6;Y16;18e1;A1;o6;Y16;3697;").
Lemma nfs_u8ro : forall m y1 t, mem_inv rsegs m -> u8ro rsegs m (nfs_addr y1 t) (zb (nf_str y1 t)).
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S9;Y3;0;Y5;00;A2;k60;A2;k62;r5;r5;o22;A1;o6;Y16;22db;A1;o6;Y16;3379;A1;o6;Y16;18e1;A1;o6;Y16;3697;A1;i11;i13;A2;k60;A2;k62;r4;r4;o22;Lm;RP~RA1;i0;A1;o1;Y6;00;A1;i2;A1;i0;A1;o1;#0;Ly1;Ri13;Lt;Ri13;LMI;RA2;k3;k4;r3;cdEb;RA2;k60;A2;k61;r2;A1;o6;#1;o22;i28;m28;RNLb;Ri28;A4;k56;k4;r6;m28;RNL~Ri28;i13;r1;2;m28;RNL~Ri28;i13;#2;2;#3;#4;m28;RNL~Ri28;i13;#2;2;#5;#6;A1;k7;m28;RNL~Ri28;#7;r1;2;m28;RNL~Ri28;#7;#2;2;k58;k59;m28;RNL~Ri28;#7;#2;2;k8;k57;r1;2;Eb;R#8;i28;m28;RNLb;Ri28;A4;k56;k4;r7;m28;RNL~Ri28;i13;r1;2;#3;#4;A1;k7;m28;RNL~Ri28;#7;r1;2;k58;k59;r1;2;A2;k63;r6;r3;A2;k64;r6;r3;Eb;R#8;i28;m28;RNLb;Ri28;A4;k56;k4;r7;m28;RNL~Ri28;i13;r1;2;#5;#6;A1;k7;m28;RNL~Ri28;#7;r1;2;k8;k57;r1;2;A2;k65;r6;r3;A2;k66;r6;r3;A4;k56;k4;r4;A2;k67;r3;r2;A1;k7;A2;k68;r3;r2;").
Qed.
Lemma nfs_addr_range : forall y1 t, (71905 <= nfs_addr y1 t <= 79511)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S23;A1;o6;Y16;18e1;A2;k60;A2;k62;r4;r4;o22;A1;o6;Y16;22db;A1;o6;Y16;3379;A1;o6;Y16;3697;m28;RNL~Ri28;i13;r1;2;m28;RNL~Ri28;i13;#1;2;#2;#3;m28;RNL~Ri28;i13;#1;2;#0;#4;A2;k60;A2;k62;r3;r3;o22;m28;RNL~Ri28;i13;r1;2;#2;#3;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#0;A2;o21;i13;#2;A2;o21;i13;#4;A2;k25;#12;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A2;o21;i13;#3;m28;RNL~Ri28;i13;r1;2;#0;#4;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#13;o23;#15;o24;A2;k33;#0;#4;A2;k67;r2;r1;Ly1;Ri13;Lt;Ri13;cdEb;RA2;k60;A2;k61;r1;A1;o6;Y5;00;o22;i28;m28;RNLb;Ri28;A2;i69;A2;k33;#0;#5;A2;k33;#5;#4;r1;2;Eb;R#6;i28;m28;RNLb;Ri28;A2;i69;A2;k33;#0;#7;A2;k33;#7;#4;r1;2;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o70;#12;k17;i18;i18;o19;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#13;o23;#14;o24;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#14;o23;#15;o24;#16;#17;A2;i69;A2;k33;#0;#2;A2;k33;#2;#4;r1;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o70;#12;k17;i18;i18;o19;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#13;o23;#18;o24;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#18;o23;#15;o24;#16;#17;A2;i69;A2;k33;#0;#3;A2;k33;#3;#4;r1;Eb;R#6;i28;m28;RNLb;Ri28;A2;i69;A2;k33;#0;#19;A2;k33;#19;#4;r1;2;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o70;#12;k17;i18;i18;o19;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#13;o23;#13;o24;#20;#16;#17;A2;i69;A2;k33;#0;#0;#21;r1;E__arith;RE__wit;R#8;#9;E__varmap;R#10;#11;E__ff;RA7;o70;#12;k17;i18;i18;o19;#20;A7;o15;#12;k17;i18;i18;o19;A4;o20;i13;#15;o23;#15;o24;#16;#17;A2;i69;#21;A2;k33;#4;#4;r1;A2;i69;A2;k33;#0;#22;A2;k33;#22;#4;").
Qed.

Lemma le_land0 : forall a b, (Z.land (f128_le a b) 18446744073709551615 = 0 <-> f128_le a b = 0)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S21;A2;k62;r2;r1;A1;o73;o74;A1;o6;o74;A2;k62;r3;r2;A2;k62;r4;r3;A1;o6;Y63;7fffffffffffffff;A3;i30;i13;#4;o22;Lz;Ri13;A2;k75;A3;i30;i13;A2;k61;r1;#5;o22;A3;i30;i13;r1;o22;A3;i30;i13;#5;o22;A3;i30;i13;#1;o22;Le;Ri13;m13;RNLz;Ri13;pr1;3;i79;L~Ri80;i47;L~Ri80;i79;A2;k62;r5;r4;A2;k62;r6;r5;A3;i30;i13;#12;o22;A3;i30;i13;o22;o22;Px;R#14;#14;LH;R#14;A2;o27;i13;o22;A2;k62;r7;r6;A3;i30;i13;#2;o22;Px;R#18;#18;LH;R#18;EH0;RA6;k78;i13;#2;#10;o81;o22;r1;i79;A2;k82;#18;r1;La;Ri13;Lb;Ri13;Eo;RA2;k71;r2;r1;A2;i72;A3;i30;i13;#0;#1;A2;i72;A3;i30;i13;#0;o22;A3;i30;i13;#0;#2;m72;RNL~RA2;i72;A3;i30;i13;#3;#1;A2;i72;A3;i30;i13;#3;o22;A3;i30;i13;#3;#2;A2;k75;A3;i30;i13;A2;k61;#4;#5;o22;#6;r1;2;L~RA3;i30;i13;#3;#1;A1;LE;RA3;i30;i13;#4;#1;A6;k76;i13;#1;#7;cvA4;o77;Px;R#8;#9;Px;R#9;#8;LH;R#8;EH0;RA6;k78;i13;#5;#10;o81;o22;r1;i79;A2;k82;#9;r1;LH;R#9;EH0;RA6;k78;i13;#1;Le;Ri13;m13;RNLz;Ri13;pr1;3;i79;L~Ri80;i79;L~Ri80;i47;o81;o22;r1;i79;A2;k82;#8;r1;A2;k75;A3;i30;i13;A2;k61;#1;#5;o22;#9;#11;r1;r1;L~RA2;i72;A3;i30;i13;#3;o22;A3;i30;i13;#3;#2;A1;LH;RA2;i72;#6;A3;i30;i13;#4;#2;m72;RNL~RA2;i72;A3;i30;i13;#11;o22;A3;i30;i13;#11;#2;A2;k75;A3;i30;i13;A2;k61;#12;#5;o22;#13;r1;2;L~RA3;i30;i13;#11;o22;A1;LE;R#13;A6;k76;i13;o22;#7;cvA4;o77;#15;#15;#16;#16;A2;k75;A3;i30;i13;A2;k61;o22;#5;o22;#14;#17;r1;r1;L~RA3;i30;i13;#11;#2;A1;LE;RA3;i30;i13;#12;#2;A6;k76;i13;#2;#7;cvA4;o77;#19;#19;#20;#20;A2;k75;A3;i30;i13;A2;k61;#2;#5;o22;#18;#17;r1;r1;r1;").
Qed.
Ltac nfs_eq y1 t Kn := unfold nfs_addr; rewrite ?le_land0 in Kn; destruct (Z.eqb_spec (Z.land t 32) 0); destruct (Z.eqb_spec (f128_le y1 y1) 0); try lia; reflexivity.

Ltac nf_mseq := cbv delta [mkR]; repeat first [ reflexivity | lia | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ nf_mseq | .. ].

Lemma bytes_le_to_Z_nonneg : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S18;Y3;0;A1;o1;#0;A1;i0;#1;A1;i11;#2;A2;k33;o22;A1;k84;r1;A1;i16;i13;A2;o21;i13;o22;A2;k33;o22;r3;A2;k33;o22;r2;A2;i69;#7;#8;P~RA2;i69;#8;A2;k33;o22;r1;A2;k33;o22;A2;k85;r3;r2;A2;k87;#1;r4;A1;o6;#0;A2;k88;A1;k84;r3;#12;A1;i0;r1;A2;k87;r2;r1;A2;k33;o22;#15;P~R#8;A2;k33;o22;A2;k88;r3;r2;Lbs;R#3;A5;k83;#2;Lbs;R#3;#4;cdE__arith;RE__wit;RA1;o9;i10;A1;i11;i10;E__varmap;RA1;o12;i13;A1;i14;i13;E__ff;RA7;o15;#5;k17;i18;i18;o19;A4;o20;i13;#6;o23;#6;o24;A2;k25;#5;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A2;k33;o22;o22;r1;A2;k33;o22;A1;k84;A1;o9;#2;Lb;R#2;Lbs;R#3;LIH;R#4;cdEH;RLa;Ri13;Lb;Ri13;m69;RNL~RA2;i69;P~RA2;k33;o22;A2;k85;r2;r1;#9;#10;P~R#9;A2;k33;o22;A2;k85;r4;r3;A2;k86;r2;r1;1;L~RP~RA2;k33;o22;A2;k85;r2;r1;#9;L~RP~RA2;i69;A2;k33;o22;r3;A2;k33;o22;r2;A2;k33;o22;A2;k85;r4;r3;r1;Pa;Ri13;Pb;Ri13;#10;A3;r1;#11;#13;A4;o77;A2;k33;o22;#11;A2;k33;o22;#13;EH;RLn;Ri89;Lb;R#14;m69;RNL~RA2;i69;#16;A2;k46;#15;A1;k90;r2;A2;k33;o22;A2;k87;r3;r2;A2;k91;r2;r1;1;L~R#16;L~RA2;k46;A2;k87;r3;r2;A1;k90;r3;r2;Pn;Ri89;Pb;R#14;#16;A2;r1;#1;r5;EH;RLa;Ri13;Ln;Ri13;m69;RNL~RA2;i69;P~RA2;k33;o22;A2;k88;r2;r1;#7;#17;P~R#7;A2;k33;o22;A2;k88;r4;r3;A2;k92;r2;r1;1;L~RP~RA2;k33;o22;A2;k88;r2;r1;#7;L~RP~RA2;k33;o22;r3;A2;k33;o22;A2;k88;r4;r3;r1;Pa;Ri13;Pn;Ri13;#17;A3;r1;A1;k84;r4;#12;r3;A2;k33;o22;A1;k84;A3;o93;#2;r3;r2;r1;").
Qed.
Lemma lor_shl8_land32 : forall x y, (0 <= x < 256)%Z -> (0 <= y)%Z -> Z.land (Z.lor x (Z.shiftl y 8)) 32 = Z.land x 32.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S38;A2;k33;o22;r2;Y3;0;A1;o6;#1;Y5;00;A1;o6;#3;A2;k33;o22;r1;A2;k88;r5;#2;A2;k85;r6;#6;A2;k96;#7;r2;A2;k96;#4;r2;A2;k96;r6;r2;A2;k96;#4;r3;A2;k96;#6;r2;A2;k96;r7;r3;A2;k95;#13;#11;A2;k98;r2;#2;A1;o6;Y2;1;A2;k60;#16;r2;A2;k96;r10;r6;A2;k97;#18;A2;k96;r9;A2;k98;r6;#2;A3;i30;i13;#16;r5;A2;k96;r12;r2;A2;k33;o22;#16;A2;k96;r12;#16;A2;k95;#23;o29;A2;k96;r11;#16;A2;k98;#16;#2;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;#16;A2;o21;i13;o22;A2;k25;#31;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;Y1;0;A7;o15;#31;k17;i18;i18;o19;A4;o20;i13;#33;o23;A2;o112;i13;o74;o24;Lx;Ri13;Ly;Ri13;LHx;RA2;i69;#0;A2;k46;r2;A1;o6;Y8;00;LHy;R#0;A3;k94;A2;k61;A2;k85;r4;A2;k88;r3;#2;#4;A2;k61;r4;#4;Ln;Ri13;LHn;R#5;A6;k76;i28;A2;k95;#8;#9;Lb;Ri28;A3;i30;i28;r1;A2;k96;A2;k61;r7;#4;r3;A6;k76;i28;A2;k95;#10;#9;Lb;Ri28;A3;i30;i28;A2;k95;A2;k96;A2;k85;r7;A2;k88;r6;#2;r3;#11;r1;A6;k76;i28;A2;k97;#10;#12;Lb;Ri28;A3;i30;i28;A2;k95;r1;#11;#14;A6;k76;i28;A2;k96;r5;#15;Lb;Ri28;A3;i30;i28;A2;k95;A2;k97;#13;r1;#11;#14;A6;k76;i28;#17;Lb;Ri28;A3;i30;i28;A2;k95;A2;k97;#13;A2;k96;r6;A2;k98;r3;#2;r1;A2;k95;#13;r1;Er;RA2;k99;#16;r2;A2;i100;A3;i30;i13;#16;r2;#17;Eb;RA2;k60;#16;r3;i28;m100;RNLb;Ri28;Lr;RA2;i100;A3;i30;i13;#16;r5;r1;A3;i30;i28;A2;k95;#19;r2;A2;k95;#18;r2;r2;2;Le;RA3;i30;i13;#16;r4;A1;Le;R#20;A7;k78;i13;#16;Ln;Ri13;PHn;R#5;A3;i30;i28;A2;k95;A2;k97;#21;A2;k96;r11;#15;o29;A2;k95;#21;o29;LHn;R#22;A6;k76;i28;o101;Lb;Ri28;A3;i30;i28;A2;k95;A2;k97;#23;r1;o29;#24;A6;k76;i28;#25;Lb;Ri28;A3;i30;i28;A2;k95;r1;o29;#24;A2;o27;i28;A2;k95;#25;o29;A2;k97;#25;o101;A1;k102;#25;A2;k96;r10;#26;A3;k103;r10;#26;E__arith;RE__wit;R#27;#28;E__varmap;R#29;#30;E__ff;RA7;o15;#31;k17;i18;i18;o19;A4;o20;i13;A3;o104;i13;#32;A2;o21;i13;#2;o105;#33;o24;#34;#35;A2;k46;#26;o22;r1;r6;r1;r5;r1;Ln;RA1;k106;A3;i30;i13;#16;r4;A1;LN5;RA1;k106;#20;A6;k76;i28;o101;Lb;Ri28;A3;i30;i28;r1;A2;k95;A2;k96;r11;r7;o101;A6;k76;i28;o101;Lb;Ri28;A3;i30;i28;o101;r1;A2;o27;i28;o101;A2;k95;#18;o101;A1;k107;#18;A2;k95;#19;o101;A1;k107;#19;r1;A2;k96;A2;k37;A1;o6;#36;#16;r2;A3;k108;#16;r2;E__arith;RE__wit;R#27;#28;E__varmap;R#29;#30;E__ff;RA7;o15;#31;k17;i18;i18;o19;A4;o20;i13;#33;o23;#32;o24;#34;#35;#22;r1;#12;A4;k109;r5;#2;r2;E__arith;RL__x1;Ri13;E__wit;R#27;#28;E__varmap;RA2;o110;i13;r2;#30;E__ff;RA8;o111;#31;k17;i18;i18;o19;#37;A1;o113;i18;#37;#34;#35;P__x1;Ri13;P~R#5;#0;A2;r1;r3;r2;#8;A3;k114;r6;#6;r2;A2;k96;A2;k61;r6;#4;r2;A3;k115;r6;#4;r2;A2;k96;A2;k61;#7;#4;r2;A3;k115;#7;#4;r2;").
Qed.
Lemma land_mod_pow2_small : forall v k m, (0 <= k)%Z -> (0 <= m < 2^k)%Z -> Z.land (v mod 2^k) m = Z.land v m.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S32;A2;k33;o22;r2;Y1;0;A1;o6;#1;A1;k116;r4;A2;k61;r5;#3;A2;k61;r6;r4;A2;k61;#3;r3;A1;k61;r5;A2;k61;r3;#3;Lz;Ri13;A3;i30;i13;r1;r4;A2;k37;#2;r4;A2;k45;#2;r4;A2;k46;o22;#2;P~R#12;P~RA2;k33;o22;r5;A2;k46;o22;A2;k37;#2;r6;A2;k33;o22;#2;LHa;R#14;L~Ri47;A3;k48;#2;r7;r2;A2;k37;#2;r7;PHa;R#14;P~Ri47;A2;k33;o22;#16;A1;r2;cdA2;o27;i49;A2;k50;o22;#2;#12;P~RA2;k33;o22;r6;A2;k46;o22;#16;A1;o9;i10;A1;i11;i10;A1;i14;i13;A1;i16;i13;A2;o112;i13;o74;A7;o15;#23;k17;i18;i18;o19;A4;o20;i13;A2;o21;i13;o22;o23;#24;o24;A7;o70;#23;k17;i18;i18;o19;#25;A7;o15;#23;k17;i18;i18;o19;A4;o20;i13;#24;o105;A2;o112;i13;#1;o24;A1;o113;i18;A2;k25;#23;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A2;k33;o22;r1;E__sat1;R#11;#13;E__sat0;R#15;#17;E__sat1;R#18;#19;E__arith;RL__x1;Ri13;E__wit;R#20;#21;E__varmap;RA2;o110;i13;r2;#22;E__ff;RA8;o111;#23;k17;i18;i18;o19;#25;#27;#25;#28;#29;P__x1;Ri13;P~R#30;#0;A2;r1;r8;r6;Lv;Ri13;Lk;Ri13;Lm;Ri13;LHk;R#0;LHm;RA2;i69;#0;A2;k46;r2;A2;k37;#2;r3;A6;k78;i13;#4;Lz;Ri13;A3;i30;i13;A2;k61;r1;r4;#5;A6;k78;i13;A2;k61;r5;#6;Lz;Ri13;A3;i30;i13;r1;#5;A8;k117;i13;i13;#7;#7;#6;r3;A2;o27;P~Ri13;i13;#7;A6;k76;i13;#8;#9;A6;k76;i13;A2;k118;r3;#10;#9;A3;k119;r3;#10;E__sat1;R#11;#13;E__sat0;R#15;#17;E__sat1;R#18;#19;E__arith;RL__x2;Ri13;L__x1;Ri13;E__wit;R#20;#21;E__varmap;RA4;o120;i13;A2;o110;i13;r3;r2;A1;o12;i13;#22;E__ff;RA8;o111;#23;k17;i18;i18;o19;#26;#27;#26;#28;#29;P__x2;Ri13;P__x1;Ri13;P~RA2;i69;#30;A2;k46;r1;r2;A2;i69;#0;A2;k46;r2;r3;A3;r1;A2;k37;#2;r8;r7;r5;#8;A3;k121;r3;r4;#31;#6;A2;k122;#3;r3;A2;k61;#4;r3;A3;k123;r5;#3;r3;A2;k118;r5;#10;A3;k121;r5;r4;#31;").
Qed.
Lemma w4_core : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S36;Y3;0;A1;o1;#0;A1;i0;#1;Y6;00;A1;o1;#3;N3;A3;k125;#2;#5;r1;A3;o93;#2;r2;#6;A1;k84;#7;A2;k124;#4;#8;Y5;00;A1;o6;#10;A2;k61;A2;k87;#1;r3;#11;A2;k61;#8;#11;A2;k87;#1;r2;A1;o9;i10;A1;i11;i10;A1;i14;i13;A1;i16;i13;A2;o21;i13;o22;A2;o112;i13;o74;A1;o6;Y8;00;A7;o70;#18;k17;i18;i18;o19;A7;o15;#18;k17;i18;i18;o19;A4;o20;i13;#19;o23;#20;o24;A7;o15;#18;k17;i18;i18;o19;A4;o20;i13;#20;o105;A2;o21;i13;#21;o24;A2;k25;#18;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A2;k61;#14;#11;Y1;0;A1;o6;#26;A1;o6;#3;A2;k37;#27;#28;A1;o12;i13;A2;k33;o22;#28;A2;k46;o22;#27;P~R#31;A2;k46;o22;#29;A2;k33;o22;#27;A2;o21;i13;#11;Lb;R#2;Ll;RA1;i11;#2;cdcdA6;k76;i13;#9;Lz;Ri13;A3;i30;i13;A2;k61;r1;#11;#12;cdA6;k76;i13;#13;Lz;Ri13;A3;i30;i13;r1;#12;cdA4;k126;#14;A1;k84;#6;ER;RA2;k91;#1;r2;A2;i69;A2;k33;o22;#14;A2;k46;#14;A1;k90;#1;E__arith;RL__x1;Ri13;E__wit;R#15;#16;E__varmap;RA2;o110;i13;r2;#17;E__ff;RA8;o111;#18;k17;i18;i18;o19;#22;A1;o113;i18;#22;#23;#24;P__x1;Ri13;P~RA2;i69;A2;k33;o22;r1;A2;k46;r1;#21;A2;i69;A2;k33;o22;r2;A2;k46;r2;#21;A2;r1;A2;k87;#1;r4;r2;A1;k127;#6;A3;i30;i13;#13;#25;A2;k61;A2;k118;#8;#29;#11;A5;k128;#8;#28;#11;E__arith;RE__wit;R#15;#16;E__varmap;R#30;#17;E__ff;RA7;o15;#18;k17;i18;i18;o19;A4;o20;i13;#19;o23;A2;o21;i13;#28;o24;#23;#24;#31;r1;E__sat1;RA2;k45;#27;#28;P~R#32;#33;E__sat0;RLHa;R#34;L~Ri47;A3;k48;#27;#28;r2;PHa;R#34;P~Ri47;A2;k33;o22;#29;E__sat1;RA1;r2;cdA2;o27;i49;A2;k50;o22;#27;#32;#33;E__arith;RE__wit;R#15;#16;E__varmap;R#30;#17;E__ff;RA7;o70;#18;k17;i18;i18;o19;A7;o15;#18;k17;i18;i18;o19;A4;o20;i13;#19;o23;#35;o24;A7;o15;#18;k17;i18;i18;o19;A4;o20;i13;#35;o105;A3;o52;i13;A2;o21;i13;#27;#4;o24;#23;#24;A2;i69;A2;k33;o22;#11;A2;k46;#11;#29;r1;A3;i30;i13;A2;k61;#9;#11;#25;A2;k87;#4;A2;k129;#4;#8;A2;k130;#4;#8;A3;i30;i13;A2;k61;A2;k87;#4;A1;k131;#7;#11;#25;A3;i30;i13;A2;k61;A2;k87;#4;A1;k131;A3;k125;#2;N4;A3;k132;#2;o133;A3;o93;#2;r2;r1;#11;#25;").
Qed.
Lemma w4_bit5 : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (zext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S48;Y3;0;A1;o1;#0;A1;i0;#1;Y6;00;A1;o1;#3;A1;i0;#4;Y5;00;A1;o1;#6;N4;A1;k131;A3;k125;#2;#8;A3;k132;#2;o133;A3;o93;#2;r2;r1;A4;k134;#4;o135;#7;#9;A2;k87;#7;#10;A2;k129;#4;#11;A1;o6;#6;A2;k61;A2;k87;#1;r3;#13;Lz;Ri13;A3;i30;i13;A2;k61;r1;#13;#14;A2;k87;#4;#9;Y1;0;A1;o6;#17;A2;k37;#18;#13;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o21;i13;o22;A2;o21;i13;#13;A7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#25;o23;#26;o24;A2;k25;#24;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A2;k33;o22;#13;A2;k45;#18;#13;A2;k46;o22;#18;P~R#30;A2;k46;o22;#19;P~R#32;#33;A2;k33;o22;#18;LHa;R#35;L~Ri47;A3;k48;#18;#13;r2;PHa;R#35;P~Ri47;A2;k33;o22;#19;cdA2;o27;i49;A2;k50;o22;#18;#32;A1;r2;#38;A2;o21;i13;#18;A3;o52;i13;#40;#7;A2;k46;o22;#13;A1;o6;#3;A2;k37;#18;#43;P~RA2;k33;o22;#43;A2;k46;o22;#44;A2;o112;i13;o74;A7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#25;o23;#46;o24;Lb;R#2;Ll;RA1;i11;#2;A6;k76;#5;#12;Lb;R#5;A3;i30;i13;A2;k61;A2;k87;#4;r1;#13;#14;A6;k76;i13;#11;#15;A6;k76;i13;A2;k118;#16;A2;k37;#18;A1;k136;#7;#15;A6;k76;i13;A2;k61;#16;#13;Lz;Ri13;A3;i30;i13;r1;#14;A2;k137;r2;r1;A2;k61;A2;k118;#16;#19;#13;A5;k128;#16;#13;#13;E__arith;RE__wit;R#20;#21;E__varmap;R#22;#23;E__ff;R#27;#28;#29;#30;r1;E__sat1;R#31;#34;E__sat0;R#36;#37;E__sat1;R#39;#33;E__arith;RE__wit;R#20;#21;E__varmap;R#22;#23;E__ff;RA7;o70;#24;k17;i18;i18;o19;#27;A7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#26;o105;#41;o24;#28;#29;A2;i69;#30;A2;k46;#13;#19;r1;#11;A3;k138;#7;#9;A4;k34;A2;k139;o135;#7;#42;A12;k38;i89;i13;k139;k136;k46;k140;o135;o22;A2;o27;i13;o22;#7;#13;A2;o27;i13;#13;E__arith;RE__wit;R#20;#21;E__varmap;R#22;#23;E__ff;RA7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#25;o105;#26;o24;#28;#29;#42;r1;A2;k87;#4;#12;A2;k141;#11;ER;RA2;k91;#7;#10;A2;i69;A2;k33;o22;#11;A2;k46;#11;A1;k90;#7;E__sat3;R#31;#34;E__sat2;R#36;#37;E__sat1;RA2;k45;#18;#43;P~R#32;#45;E__sat0;RLHa;R#35;L~Ri47;A3;k48;#18;#43;r2;PHa;R#35;P~Ri47;A2;k33;o22;#44;E__sat1;R#39;#45;E__sat3;RA1;r5;#38;#33;E__arith;RL__x1;Ri13;E__wit;R#20;#21;E__varmap;RA2;o110;i13;r2;#23;E__ff;RA8;o111;#24;k17;i18;i18;o19;A7;o70;#24;k17;i18;i18;o19;#47;A7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#46;o105;#41;o24;A1;o113;i18;A7;o70;#24;k17;i18;i18;o19;#47;A7;o15;#24;k17;i18;i18;o19;A4;o20;i13;#46;o105;A3;o52;i13;#40;#4;o24;#28;#29;P__x1;Ri13;P~RA2;i69;A2;k33;o22;r1;A2;k46;r1;#19;A2;i69;A2;k33;o22;r2;A2;k46;r2;#44;A2;r1;A2;k87;#7;A4;k134;#4;o135;#7;A1;k131;A3;k125;#2;#8;A3;k132;#2;o133;A3;o93;#2;r10;r9;r8;A3;k142;#7;#4;#10;A2;k143;#7;#10;").
Qed.
Lemma w4s_bit5 : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S72;Y3;0;A1;o1;#0;A1;i0;#1;Y6;00;A1;o1;#3;A1;i0;#4;Y5;00;A1;o1;#6;N4;A1;k131;A3;k125;#2;#8;A3;k132;#2;o133;A3;o93;#2;r2;r1;A4;k134;#4;o135;#7;#9;A2;k144;#7;#10;A2;k129;#4;#11;A1;o6;#6;A2;k61;A2;k87;#1;r3;#13;Y1;0;A1;o6;#15;A1;o6;#3;A2;k37;#16;#17;A2;k118;#11;#18;A2;k61;r1;#13;Lz;Ri13;A3;i30;i13;#20;#14;A2;k87;#4;#9;A2;k145;#7;r1;A2;k37;#16;#13;A2;k118;#23;#24;A2;k146;#24;#16;A2;k35;r1;#26;A2;k98;#27;#26;A2;k118;r2;#24;P~Ri13;i13;A2;k87;#4;A1;k131;A3;k125;#2;#8;A3;k132;#2;o133;A3;o93;#2;r3;r2;A3;i30;i13;r1;#31;cdA2;o27;i13;#31;#32;A2;k45;#16;#13;A2;k46;o22;#16;A2;k33;o22;#13;P~R#36;A2;k46;o22;#24;P~R#35;#37;A2;k33;o22;#16;LHa;R#39;L~Ri47;A3;k48;#16;#13;r2;A2;k33;o22;#24;PHa;R#39;P~Ri47;#41;A3;i30;i13;#16;o22;A2;k118;#24;#16;A2;i69;A2;k33;o22;#44;A2;k46;#44;#16;A2;k154;#24;#16;cdA2;o27;i49;A2;k50;o22;#16;#35;A1;o9;i10;A1;i11;i10;A1;o12;i13;A1;i14;i13;A1;i16;i13;A2;o112;i13;o74;A2;o112;i13;#15;A2;k25;#52;o19;A4;k26;r1;r3;cvA2;o27;i28;o29;A3;i30;i28;A2;k31;r1;r3;o29;A3;k32;i13;o22;r2;A3;i30;i13;A2;k118;r1;#24;#25;A2;k61;A2;k87;#1;r5;#13;A2;k87;#4;A1;k131;A3;k125;#2;#8;A3;k132;#2;o133;A3;o93;#2;r4;r3;A3;i30;i13;r2;#59;cdA2;o27;i13;#59;#60;A2;o21;i13;o22;A2;o21;i13;#13;A7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#62;o23;#63;o24;E__arith;RE__wit;R#48;#49;E__varmap;R#50;#51;E__ff;R#64;#55;#56;#36;r1;A1;r2;#47;A2;o21;i13;#16;E__sat1;R#34;#38;E__sat0;R#40;#42;E__sat1;R#66;#37;E__arith;RE__wit;R#48;#49;E__varmap;R#50;#51;E__ff;RA7;o70;#52;k17;i18;i18;o19;#64;A7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#63;o105;A3;o52;i13;#67;#7;o24;#55;#56;A2;i69;#36;A2;k46;#13;#24;r1;A2;k46;o22;#13;A2;k33;o22;#17;P~R#70;A2;k46;o22;#18;Lb;R#2;Ll;RA1;i11;#2;A6;k76;#5;#12;Lb;R#5;A3;i30;i13;A2;k61;A2;k87;#4;r1;#13;#14;A6;k76;i13;#19;#21;A6;k76;i13;A2;k61;#11;#13;Lz;Ri13;A3;i30;i13;r1;#14;A6;k76;i13;A2;k145;#7;#22;#21;Ev;R#22;i13;A6;k78;i13;A2;k61;#25;#13;Lz;Ri13;A3;i30;i13;r1;A2;k61;A2;k87;#1;r4;#13;EH;RcdA6;k76;i13;A2;k118;#28;#24;Lz;Ri13;A3;i30;i13;#29;r1;A8;k117;i13;i13;A1;k118;r1;A1;k118;#28;#24;#24;A8;k117;i13;#30;k118;k118;r1;#28;A2;o27;P~Ri13;#30;k118;Eheq_v;R#33;#32;E__sat2;R#34;#38;E__sat1;R#40;#42;E__sat0;RA2;k147;#24;#16;P~R#41;P~R#39;A2;k33;o22;#26;EH;RA2;k148;#24;#16;P~RA1;k106;#43;A3;i30;i13;#24;A2;k35;A2;k149;#16;#26;#44;EH0;RA2;k150;#24;#16;P~R#35;#45;EH1;RA2;k151;#24;#16;P~RA2;k46;#16;o22;A2;i69;A2;k46;#16;#44;A2;k33;#44;o22;EH2;RA2;k152;#24;#16;P~R#43;A3;i30;i13;#26;o22;EH3;RA2;k153;#24;#16;P~R#43;A3;i30;i13;#44;#24;EH4;Rcdo81;#46;#46;cdEH0;RA1;r5;#47;#45;Ezh;Rr2;i47;E__sat1;RLa;R#39;A2;r11;r1;r2;Pa;R#39;#41;E__sat2;RA1;r12;#47;#37;E__arith;RL__x2;Ri13;L__x1;Ri13;E__wit;R#48;#49;E__varmap;RA4;o120;i13;A2;o110;i13;r3;r2;#50;#51;E__ff;RA7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#53;o155;A3;o104;i13;A3;o51;i13;#53;#54;#54;o24;#55;#56;P__x2;Ri13;P__x1;Ri13;A3;i30;i13;r1;A2;k98;A2;k35;r1;r2;r2;A2;r1;#26;r16;A3;i30;i13;r11;A2;k98;A2;k35;r11;#26;#26;A2;o27;i13;#24;A2;k118;A2;k98;A2;k118;#27;#24;#26;#24;A3;k156;#27;#26;#24;#57;#57;A6;k78;i13;#29;Lz;Ri13;A3;i30;i13;#20;#58;A6;k76;i13;A2;k61;r2;#13;Lz;Ri13;A3;i30;i13;r1;#58;A2;k137;r4;r3;A2;k61;#29;#13;A5;k128;r2;#13;#13;Eheq_v;R#61;#60;#65;Eheq_v;R#61;#60;#68;A2;k118;A2;k145;#7;r2;#24;r1;A2;k61;#23;#13;A5;k128;#23;#13;#13;Eheq_v;R#33;#32;#65;Eheq_v;R#33;#32;#68;#11;A3;k157;#7;#9;A4;k34;A2;k139;o135;#7;#69;A12;k38;i89;i13;k139;k136;k46;k140;o135;o22;A2;o27;i13;o22;#7;#13;A2;o27;i13;#13;E__arith;RE__wit;R#48;#49;E__varmap;R#50;#51;E__ff;RA7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#62;o105;#63;o24;#55;#56;#69;r1;A2;k61;#19;#13;A5;k128;#11;#17;#13;E__arith;RE__wit;R#48;#49;E__varmap;R#50;#51;E__ff;RA7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#62;o23;A2;o21;i13;#17;o24;#55;#56;#70;r1;E__sat1;RA2;k45;#16;#17;P~R#35;#71;E__sat0;RLHa;R#39;L~Ri47;A3;k48;#16;#17;r2;PHa;R#39;P~Ri47;A2;k33;o22;#18;E__sat1;R#66;#71;E__arith;RE__wit;R#48;#49;E__varmap;R#50;#51;E__ff;RA7;o70;#52;k17;i18;i18;o19;#64;A7;o15;#52;k17;i18;i18;o19;A4;o20;i13;#63;o105;A3;o52;i13;#67;#4;o24;#55;#56;A2;i69;#36;A2;k46;#13;#18;r1;A2;k87;#4;#12;A1;k158;#11;A3;k159;#7;#4;#10;A2;k160;#7;#10;").
Qed.
Lemma rw_cells_retype_nf : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' EB ES. unfold rw_cells, cells_at. rewrite EB, ES. auto.
Qed.
Definition FILE_cells4 (fl0 b1 b2 b3 : byte) (j1r : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
  [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].
Lemma file_cells4 : forall m Fp fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw,
  rw_cells rsegs m Fp (FILE_cells fl0 (b1 :: b2 :: b3 :: j1r) WEND WPOS j2 lbfw) <->
  rw_cells rsegs m Fp (FILE_cells4 fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw).
Proof.
  intros. unfold FILE_cells, FILE_cells4.
  assert (E : cells_bytes [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]
              = cells_bytes [CB 1 [fl0]; CB 31 (b1 :: b2 :: b3 :: j1r); C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]).
  { cbn [cells_bytes cbytes app]. rewrite (le4_of_bytes [fl0; b1; b2; b3]) by reflexivity. reflexivity. }
  split; intros H.
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); cbn in W1; try lia; exact W2 | exact E | reflexivity].
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); try lia; exact W2 | symmetry; exact E | reflexivity].
Qed.

Lemma flags4_ferr : forall (fl0 b1 b2 b3 : byte), Z.land (bv_unsigned fl0) 32 = 0%Z ->
  Z.land (bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3])) 32 = 0%Z.
Proof.
  intros fl0 b1 b2 b3 H. rewrite StrFun.le_bytes_to_word4.
  pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1). pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
  unfold bv_modulus in *. cbn -[Z.add Z.mul Z.land bv_unsigned Z.le Z.lt] in *.
  change 32%Z with (2^5)%Z in H |- *. rewrite zb_land_pow2 in H |- * by lia.
  replace ((bv_unsigned fl0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 2 ^ 5)%Z
    with (bv_unsigned fl0 / 2^5 + (4 * bv_unsigned b1 + 1024 * bv_unsigned b2 + 262144 * bv_unsigned b3) * 2)%Z
    by (change (2^5)%Z with 32%Z; Z.to_euclidean_division_equations; lia).
  rewrite Z.mod_add by lia. exact H.
Qed.

Lemma land32_sx32 : forall ww : word, Z.land (bv_unsigned (sx32 ww)) 32 = Z.land (bv_unsigned ww) 32.
Proof.
  intros ww. transitivity (Z.land (Z.land (bv_unsigned (sx32 ww)) 63) 32). { rewrite <- Z.land_assoc. reflexivity. }
  change 63%Z with (2^6 - 1)%Z. rewrite land_sx32_mask by lia.
  transitivity (Z.land (Z.land (bv_unsigned ww) (2^6 - 1)) 32). 2:{ rewrite <- Z.land_assoc. reflexivity. }
  change (2^6 - 1)%Z with (Z.ones 6). rewrite Z.land_ones by lia. f_equal.
  pose proof (bv_unsigned_in_range 64 ww). Z.to_euclidean_division_equations. lia.
Qed.
Lemma zx32_le4 : forall fl0 b1 b2 b3 : byte, bv_unsigned (zx32 (le_bytes_to_word [fl0; b1; b2; b3])) = bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]).
Proof.
  intros. unfold zx32.
  assert (R : (0 <= bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]) < 2^32)%Z).
  { rewrite StrFun.le_bytes_to_word4. pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1).
    pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3). unfold bv_modulus in *. cbn -[Z.add Z.mul Z.le Z.lt bv_unsigned] in *. lia. }
  rewrite Z.mod_small by lia. apply unsigned_lit. lia.
Qed.

Lemma nf_strings : forall m, mem_inv rsegs m ->
  bytes_at rsegs m 71905 (zb INF_LC) /\ bytes_at rsegs m 79511 (zb NAN_LC)
  /\ bytes_at rsegs m 74459 (zb INF_UC) /\ bytes_at rsegs m 78713 (zb NAN_UC).
Proof.
  intros m MI. exact (conj (nfs_inf_u8ro m MI) (conj (nfs_nan_u8ro m MI) (conj (nfs_INF_u8ro m MI) (nfs_NAN_u8ro m MI)))).
Qed.

Ltac cur_reg R k :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
  eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end).


Section FmtFp.
  Variables (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (ya yb fw : word)
            (F : bvmap 5 word) (m0 : word -> option byte)
            (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
            (w p fl t : Z) (o0 o1 : list Z) (ret : Z).
  Definition yv : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S3;Y6;00;A1;o1;#0;Y1;0;A2;k35;A2;k87;#1;vya;A2;k149;A2;k37;A1;o6;#2;A1;o6;#0;A2;k87;#1;vyb;").
  Definition Fp : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A2;k87;A1;o1;Y6;00;vfw;").
  Definition usp : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A2;k87;A1;o1;Y6;00;vsp;").

  Hypothesis HM : fmt_fp_nf o0 yv w p fl t = Some (o1, ret).
  Hypothesis SPLO : (5152 <= bv_unsigned sp)%Z.
  Hypothesis SPHI : (bv_unsigned sp < 2^63)%Z.
  Hypothesis GLO : (1010296 <= bv_unsigned sp - 4640)%Z.
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  Hypothesis Hw : (0 <= w <= 1)%Z.
  Hypothesis Hp : (-2^31 <= p < 2^20)%Z.
  Hypothesis Hfl : (0 <= fl < 2^32)%Z.
  Hypothesis Ht : (0 <= t < 256)%Z.
  Hypothesis ROOM : (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis J256 : (length junk0 < 256)%nat.

  Definition ctx_all : unit := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S40;A1;i0;A1;o1;Y6;00;A2;i162;#0;#0;A2;i162;#1;#0;A2;i162;#2;#0;A2;i162;#3;#0;A2;i162;#4;#0;A2;i162;#5;#0;A2;i162;#6;#0;A2;i162;#7;#0;A2;i162;#8;#0;A2;i162;#9;#0;A2;i162;#10;#0;A2;i162;#11;#0;A2;i162;#12;#0;A2;i162;#13;#0;A2;i162;#14;#0;A2;i162;#15;#0;A2;i162;#16;#0;A2;i162;#17;#0;A2;k163;A1;o1;Y2;1;#0;A2;i162;#18;#19;Y3;0;A1;i0;A1;o1;#21;P~R#0;A1;i2;#22;A2;i162;#20;#23;A2;i162;#24;#22;A1;i11;#22;A2;i162;#25;#26;A2;i162;#27;#26;A2;i162;#28;#0;A2;i162;#29;i13;A2;i162;#30;#26;A2;i162;#31;#0;A2;i162;#32;i13;A2;i162;#33;i13;A2;i162;#34;i13;A2;i162;#35;i13;A1;i11;i13;A2;i162;#36;#37;A2;i162;#38;#37;E~RA4;o161;#39;i13;A4;o161;#38;#37;A4;o161;#36;#37;A4;o161;#35;i13;A4;o161;#34;i13;A4;o161;#33;i13;A4;o161;#32;i13;A4;o161;#31;#0;A4;o161;#30;#26;A4;o161;#29;i13;A4;o161;#28;#0;A4;o161;#27;#26;A4;o161;#25;#26;A4;o161;#24;#22;A4;o161;#20;#23;A4;o161;#18;#19;A4;o161;#17;#0;A4;o161;#16;#0;A4;o161;#15;#0;A4;o161;#14;#0;A4;o161;#13;#0;A4;o161;#12;#0;A4;o161;#11;#0;A4;o161;#10;#0;A4;o161;#9;#0;A4;o161;#8;#0;A4;o161;#7;#0;A4;o161;#6;#0;A4;o161;#5;#0;A4;o161;#4;#0;A4;o161;#3;#0;A4;o161;#2;#0;A4;o161;#1;#0;A4;o161;#0;#0;vra;vsp;vgp;vtp;vs0e;vs1e;vs2e;vs3e;vs4e;vs5e;vs6e;vs7e;vs8e;vs9e;vs10e;vs11e;vya;vyb;vfw;vF;vm0;vfl0;vj1;vj2;vlbfw;vB;vjunk0;vcanary;vw;vp;vfl;vt;vo0;vo1;vret;A2;i162;#39;i13;o24;").

  Definition Wfp : list (Z * Z) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S2;A2;i162;i13;i13;A2;k87;A1;o1;Y6;00;vsp;A3;o93;#0;A4;o161;i13;i13;A2;k98;#1;A1;o6;Y12;220;#1;A3;o93;#0;A4;o161;i13;i13;A2;k35;vB;A1;k36;A2;k53;i13;vo0;A2;k35;vB;A1;k36;A2;k53;i13;vo1;A3;o93;#0;A4;o161;i13;i13;A2;k35;k164;A1;o6;Y5;08;A2;k35;k164;A1;o6;Y5;10;A1;o9;#0;").

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S11;A1;o1;Y6;00;A1;i0;#0;Y3;0;A1;i0;A1;o1;#2;P~R#1;A1;i2;#3;Y2;1;A1;o1;#5;A2;k163;#6;#1;Y5;00;A1;i0;A1;o1;#8;A2;k87;#0;vsp;Lm;R#4;Lms';Ri165;A2;i166;#1;Lt0;R#1;A2;i166;#1;Lt1;R#1;A2;i166;#1;Lt2;R#1;A2;i166;#1;La1;R#1;A2;i166;#1;La2;R#1;A2;i166;#1;La3;R#1;A2;i166;#1;La4;R#1;A2;i166;#1;La5;R#1;A2;i166;#1;La6;R#1;A2;i166;#1;La7;R#1;A2;i166;#1;Lt3;R#1;A2;i166;#1;Lt4;R#1;A2;i166;#1;Lt5;R#1;A2;i166;#1;Lt6;R#1;A2;i166;#7;LFt;R#7;A2;i166;#9;Lfc';R#9;A2;i166;#4;Lm';R#4;A2;i69;A3;i30;i165;r18;A7;k167;A31;k168;vra;vsp;vgp;vtp;r17;r16;r15;vs0e;vs1e;A2;k129;#0;vret;r14;r13;r12;r11;r10;r9;r8;vs2e;vs3e;vs4e;vs5e;vs6e;vs7e;vs8e;vs9e;vs10e;vs11e;r7;r6;r5;r4;r3;A1;k169;vra;r2;A1;o113;#1;r1;A1;k170;k4;A2;i69;A3;k171;k172;r19;r1;A2;i69;A3;k173;k4;r19;r1;A2;i69;A2;k3;k4;r1;A2;i69;A1;k174;r2;A2;i69;A4;k175;k4;r1;A2;k98;#10;A1;o6;Y12;220;#10;A2;i69;A9;k176;r1;k164;vfl0;vj1;vj2;vlbfw;vB;A1;k7;vo1;A3;k132;#3;A2;k177;A2;k53;i13;vo1;A2;k53;i13;vo0;vjunk0;A2;i69;A2;k178;r1;vcanary;Pk;RA1;i0;#6;P~RA1;k106;A3;i30;i13;A2;k87;#6;r1;A1;o6;Y3;2;A3;i30;#1;A2;k179;r5;r2;A2;k179;vF;r2;").

  Definition hi_cells (pad256 : list byte) : list cell := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S0;Lpad256;RA1;i11;A1;i0;A1;o1;Y3;0;A3;o93;i180;A2;o181;N256;r1;A3;o93;i180;A1;o182;vcanary;A3;o93;i180;A1;o182;vs11e;A3;o93;i180;A1;o182;vs10e;A3;o93;i180;A1;o182;vs9e;A3;o93;i180;A1;o182;vs8e;A3;o93;i180;A1;o182;vs7e;A3;o93;i180;A1;o182;vs6e;A3;o93;i180;A1;o182;vs5e;A3;o93;i180;A1;o182;vs4e;A3;o93;i180;A1;o182;vs3e;A3;o93;i180;A1;o182;vs2e;A3;o93;i180;A1;o182;vs1e;A3;o93;i180;A1;o182;vs0e;A3;o93;i180;A1;o182;vra;A1;o9;i180;").

  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 2 "S5;A1;o1;Y6;00;Y3;0;A1;i0;A1;o1;#1;A2;k87;#0;vsp;A1;o9;i180;Lm;RP~RA1;i0;#0;A1;i2;#2;Lpad256;RA1;i11;#2;A2;i69;A2;k3;k4;r2;A2;i69;A3;k171;k172;vm0;r2;A2;i69;A3;k173;k4;vm0;r2;A2;i69;A4;k183;k4;r2;A2;k35;#3;A1;o73;Y8;70;A1;k184;r1;A2;i69;A4;k175;k4;r2;A2;k98;#3;A1;o6;Y12;220;A2;k35;#3;A1;o73;Y10;020;A2;i69;A4;k183;k4;r2;k185;A3;o93;i180;A1;o182;A2;k129;#0;k186;#4;A4;k183;k4;r2;k186;A3;o93;i180;A1;o182;vcanary;#4;").
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; cbv delta [F_memcpy_u.rsegs] in FC, BUF; fold rsegs in FC, BUF.
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  Ltac prune := try clear HM.

  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

  Ltac clear_fat :=
    repeat match goal with
           | H : evt _ _ _ |- _ => clear H
           | H : forall _, _ |- _ => clear H
           | H : _ = Some _ |- _ => clear H
           | H : Some _ = _ |- _ => clear H
           | H : u32arr _ _ _ _ |- _ => clear H
           | H : rw_cells _ _ _ _ |- _ => clear H
           | H : wfile _ _ _ _ _ _ _ _ _ |- _ => clear H
           end.

  Ltac clear_logic :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ <-> _ |- _ => clear H
           | H : ~ _ |- _ => clear H
           | H : zboxed _ _ |- _ => clear H
           end.
  Local Ltac slia ::= first [ exact I | solve [clear_fat; clear_logic; lia] | solve [clear_fat; lia] | lia | split; [lia|exact I] ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  Lemma L_bec :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk80 jk8 jk3 jk12 jk37 jbig
      (y1 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells rsegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 80 jk80; C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); CB 8 jk8] ->
    rw_cells rsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk3] ->
    rw_cells rsegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells rsegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells rsegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (69009 + prefix)%Z ->
    ffp_sign yv fl = (y1, prefix, pl) ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 1010288) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0xae288) fc None m (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    (* [Hp] is not in this lemma's [Proof using] list (its callers' recorded terms apply it
       without that premise): keep [lia] from reading it. *)
    clear Hp.
    intros until pfx. intros FI FRM FRs E2 EB BF BIGb WF Hpre Hpl Hplz Hpfx HS. dest_finv FI. dest_wfile WF. pose_word_ranges.

    pose proof HM as HM'. unfold fmt_fp_nf in HM'. rewrite HS in HM'. cbv beta iota in HM'.
    zs. zs. zs. call fpclassifyl_callv. 1:{ hyp. }
    zs. zs. if_cases Kc; zify_cond Kc; rewrite signed_of_Z in Kc by (pose proof (fpclassifyl_range y1); lia).
    2:{ exfalso. rewrite (proj2 (Z.leb_gt _ _)) in HM' by lia. discriminate HM'. }
    rewrite (proj2 (Z.leb_le _ _) Kc) in HM'. rewrite (proj2 (Z.leb_le 0 w) (proj1 Hw)), (proj2 (Z.leb_le w 1) (proj2 Hw)) in HM'. cbn [andb] in HM'.
    injection HM' as Eo1 Eret. try clear HM'.
    assert (EL : (Z.of_nat (length o1) = Z.of_nat (length o0) + pl + 3)%Z) by (rewrite <- Eo1; try unfold out; rewrite !app_length, nf_str_length, (zsub_length PREFIX_STR) by (cbn; lia); lia).
    assert (LJ1 : length j1 = 31%nat) by (destruct FC as [[W _] _]; cbn in W; tauto).
    assert (EJ : exists b1 b2 b3 j1r, j1 = b1 :: b2 :: b3 :: j1r)
      by (destruct j1 as [|b1 [|b2 [|b3 j1r]]]; try (cbn in LJ1; discriminate LJ1); exists b1, b2, b3, j1r; reflexivity).
    destruct EJ as (b1 & b2 & b3 & j1r & EJ).
    set (c0 := zb o0) in *. assert (Lc0 : length c0 = length o0) by (subst c0; apply zb_length).
    set (pbs := zb (zsub PREFIX_STR prefix pl)) in *.
    assert (Lpx : length (zsub PREFIX_STR prefix pl) = Z.to_nat pl) by (apply zsub_length; cbn; lia).
    assert (Lpbs : length pbs = Z.to_nat pl) by (subst pbs; rewrite zb_length; exact Lpx).
    set (sbs := zb (nf_str y1 t)) in *.
    assert (Lsbs : length sbs = 3%nat) by (subst sbs; rewrite zb_length; apply nf_str_length).

    zs. zs. zs. zs. zs. zs. call letf2_callv. 1:{ hyp. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J640 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv rsegs mq -> bytes_at rsegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 1010296)%Z ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xae370) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (3 + pl)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 1010288) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0xae4d0) fc None mcur (seg_rom rsegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1.

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite zx32_le4, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe; zify_cond Kfe; [exfalso; lia|].

      zs. rewrite Hpfx. zs. zs.
      match goal with MIq : mem_inv _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (bytes_at_slice _ _ _ (Z.to_nat prefix) (Z.to_nat pl) (prefix_u8ro _ MIq) ltac:(rewrite zb_length; cbn; lia)) as SRC end.
      rewrite Z2Nat.id in SRC by lia. rewrite <- zb_zsub in SRC by lia. change (zb (zsub PREFIX_STR prefix pl)) with pbs in SRC.
      destruct (stk_split rsegs _ _ (bv_unsigned sp + -1056 - 64) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC
          | rewrite Lpbs, Z2Nat.id by lia; reflexivity
          | rewrite Lpbs; lia
          | exact STf
          | first [hyp | assumption]   (* same three-way [rsegs] shadow as :337 *)
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 64)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge rsegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC. try clear POST. clear FLG LBF Bpos Bhi SEPfb.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c0 ++ pbs) _ |- _ => dest_wfile X end.
      assert (LA : length (c0 ++ pbs) = (length c0 + Z.to_nat pl)%nat) by (rewrite app_length, Lpbs; reflexivity).
      assert (LK : length (skipn (length pbs) junk0) = (length junk0 - Z.to_nat pl)%nat) by (rewrite length_skipn, Lpbs; reflexivity).

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite land32_sx32, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe2; zify_cond Kfe2; [exfalso; lia|].

      zs. zs. zs.
      match goal with MIq : mem_inv _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (SBYf _ MIq) as SRC2 end.
      destruct (stk_split rsegs _ _ (bv_unsigned sp + -1056 - 64) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC2
          | rewrite Lsbs; reflexivity
          | rewrite Lsbs; lia
          | exact STf
          (* The U/ twin of CJ/F10/F_fmt_fp_nf.v:333, same three-way [rsegs] shadow:
             F_memset_u (:12), F_memcpy_u (:13) and F_fmt_fp_calls_u (:24) each
             declare their own [Definition rsegs], so [hyp]'s [constr_eq] rejects a
             convertible-but-not-syntactically-equal hypothesis.  [assumption]
             unifies up to conversion. *)
          | first [hyp | assumption]
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 64)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge rsegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC2. try clear POST.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ ((c0 ++ pbs) ++ sbs) _ |- _ => rename X into WF3 end.

      zs. zs. zs. zs.

      lazymatch goal with |- evt _ _ (MS ?R ?Fq _ ?fcq _ ?mq _) =>
      let y5 := cur_reg R 5%Z in let y6 := cur_reg R 6%Z in let y7 := cur_reg R 7%Z in
      let y10 := cur_reg R 10%Z in let y11 := cur_reg R 11%Z in let y12 := cur_reg R 12%Z in let y13 := cur_reg R 13%Z in
      let y14 := cur_reg R 14%Z in let y15 := cur_reg R 15%Z in let y16 := cur_reg R 16%Z in let y17 := cur_reg R 17%Z in
      let y18 := cur_reg R 18%Z in let y19 := cur_reg R 19%Z in
      let y28 := cur_reg R 28%Z in let y29 := cur_reg R 29%Z in let y30 := cur_reg R 30%Z in let y31 := cur_reg R 31%Z in
      assert (J6fc : evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xae508) SPv gp tp y5 y6 y7 sp (Z_to_bv 64 (3 + pl)) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 (Z_to_bv 64 1010288) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) y28 y29 y30 y31)
            Fq (Z_to_bv 64 0xae58c) fcq None mq (seg_rom rsegs)))
      end.
      { zs. if_cases Klt; zify_cond Klt; [exfalso; lia|].
        zs. zs. rewrite Eret. zs. zs. zs. if_cases Kcan; zify_cond Kcan; try (exfalso; clear -Kcan; apply Kcan; reflexivity).
        do 15 zs.

        release_frame BIGb ST (bv_unsigned sp + -544)%Z.
        release_frame FRs ST (bv_unsigned sp + -424)%Z.
        release_frame E2 ST (bv_unsigned sp + -417)%Z.
        release_frame EB ST (bv_unsigned sp + -405)%Z.
        release_frame BF ST (bv_unsigned sp + -368)%Z.
        release_frame FRhi ST (bv_unsigned sp)%Z.
        zs.
        apply evt_done. unfold fmt_fp_post.
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [ ms_eq | ].
        split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [hyp|]. split; [exact ST|].
        split. { replace (zb o1) with ((c0 ++ pbs) ++ sbs) by (subst c0 pbs sbs; rewrite <- Eo1; try unfold out; rewrite !zb_app, ?app_assoc; reflexivity).
                 replace (skipn (length o1 - length o0) junk0) with (skipn (length sbs) (skipn (length pbs) junk0)) by (rewrite skipn_skipn; f_equal; lia).
                 exact WF3. }
        split; [unfold ssp_cells, got_ssp, ssp_guard; split; hyp | intros k Hk; reflexivity ]. }
      if_cases Kzp; zify_cond Kzp; [ exact J6fc |].

      zs. if_cases Kw2; zify_cond Kw2; first [exact J6fc | exfalso; lia]. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J5c0 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv rsegs mq -> bytes_at rsegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 1010296)%Z ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xae370) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (Z.land t 32)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 1010288) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0xae450) fc None mcur (seg_rom rsegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1.
      zs. zs. try replace (bv_swrap 32 (pl + 3))%Z with (3 + pl)%Z by (rewrite swrap32_eq; mlia). replace (Z_to_bv 64 (pl + 3)) with (Z_to_bv 64 (3 + pl)) by (f_equal; lia).
      zs. if_cases Kla; zify_cond Kla; [ eapply J640; [exact SBYf | lia | lia] |].
      zs. if_cases Kw1; zify_cond Kw1; first [ eapply J640; [exact SBYf | lia | lia] | exfalso; lia ]. }

    zs. if_cases Kt; zify_cond Kt.
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn;
        [ | zs ];
        first [ apply (proj1 (F_frexpl_u.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl_u.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; rewrite Kt;
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia ]).
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn; zs;
        first [ apply (proj1 (F_frexpl_u.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl_u.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; replace (Z.land t 32 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kt));
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia ]).
  Qed.

  Lemma L_b84 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk jk1 jk2 jk3 jbig,
    finv m pad -> frm0 fc ->
    rw_cells rsegs m (bv_unsigned sp + -544) [C8 (Z_to_bv 64 0); CB 112 jk] ->
    rw_cells rsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk1] ->
    rw_cells rsegs m (bv_unsigned sp + -417) [CB 12 jk2] ->
    rw_cells rsegs m (bv_unsigned sp + -405) [CB 37 jk3] ->
    rw_cells rsegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 1010288) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 yv)) (Z_to_bv 64 (lo64 yv)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0xae220) fc None m (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    clear Hp.
    intros until jbig. intros FI FRM FRs E2 EB BF BIGb WF. dest_finv FI. dest_wfile WF. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (lo64_range yv) as Rylo. pose proof (hi64_range yv) as Ryhi.
    zs. zs. zs. call signbitl_callv. 1:{ hyp. }
    zs. if_cases Ks; zify_cond Ks; rewrite land_W64_small in Ks by (pose proof (signbitl_range yv); lia).
    -   zs. zs. zs. zs. if_cases Km; zify_cond Km; rewrite shl52_land64 in Km by lia.
      +
        zs. zs. zs. zs. zs.
        eapply L_bec with (prefix := 3%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
        unfold ffp_sign. cbv beta delta [MARK_POS]. rewrite land_bit11. decide_tests_b. reflexivity.
      + zs. rewrite land_bit0. zs. zs. if_cases Kp; zify_cond Kp.
        *
          rewrite Kp in FRs |- *. zs. zs. zs. zs. change (Z.b2z (0 <? 1)) with 1%Z. zs. zs.
          eapply L_bec with (prefix := 1%Z) (pl := 0%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
          unfold ffp_sign. cbv beta delta [MARK_POS PAD_POS]. rewrite land_bit11, land_bit0. decide_tests_b. reflexivity.
        *
          replace (fl mod 2)%Z with 1%Z in FRs |- * by lia.
          zs. zs. zs. zs. zs. change (Z.b2z (1 <? 1)) with 0%Z. zs. zs.
          eapply L_bec with (prefix := 6%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
          unfold ffp_sign. cbv beta delta [MARK_POS PAD_POS]. rewrite land_bit11, land_bit0. decide_tests_b. reflexivity.
    -
      zs. zs. zs. zs. zs. zs. zs. rewrite <- hi64_flip_sign.
      replace (Z_to_bv 64 (lo64 yv)) with (Z_to_bv 64 (lo64 (Z.lxor yv F128_SIGNBIT))) by (rewrite lo64_flip_sign; reflexivity).
      zs. zs. zs.
      eapply L_bec with (prefix := 0%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
      unfold ffp_sign. decide_tests_b. reflexivity.
  Qed.

  Lemma ffp_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
    stk rsegs m0 (bv_unsigned sp - 4640) (bv_unsigned sp) ->
    mem_inv rsegs m0 ->
    frm0 fc ->
    wfile m0 Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m0 canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e fw ya yb a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 0xae170) fc None m0 (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    clear Hp.
    intros until fc. intros ST MI FRM WF (GOT & SSP) -> -> -> -> Hps. dest_wfile WF.
    cbv delta [F_memcpy_u.rsegs] in GOT, SSP. fold rsegs in GOT, SSP.
    pose proof (munch_refl Wfp m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold Wfp in MU.
    pose_word_ranges. unfold got_ssp, ssp_guard in *.
    assert (Rya : (0 <= bv_unsigned ya < 2^64)%Z) by apply (zr_word ya).
    assert (Ryb : (0 <= bv_unsigned yb < 2^64)%Z) by apply (zr_word yb).
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).

    replace fw with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
    replace ya with (Z_to_bv 64 (lo64 yv)) by (unfold yv; rewrite lo64_words by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
    replace yb with (Z_to_bv 64 (hi64 yv)) by (unfold yv; rewrite hi64_words by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
    carve_frame 544%nat ST.
    zstep. zstep0. do 13 zstep. zstep.

    apply (rw_cells_split_CB rsegs _ _ [_] 432 _ _ [112; 4; 3; 12; 37; 256; 8]%nat) in FR; [ | reflexivity ].
    cbn [mk_CB_cells app] in FR.
    name_cb 112%nat FR. name_cb 4%nat FR. name_cb 3%nat FR. name_cb 12%nat FR. name_cb 37%nat FR. name_cb 256%nat FR. name_cb 8%nat FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [FRs FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [E2 FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [EB FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [BF FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    match type of E2 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -424)%Z in E2 by lia end.
    match type of EB with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -417)%Z in EB by lia end.
    match type of BF with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -405)%Z in BF by lia end.
    match type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -368)%Z in FRhi by lia end.
    do 7 zstep.
    zstep. zstep.   zstep.   zstep.
    zstep.
    zstep. if_cases Kps; zify_cond Kps.
    { exfalso. apply Hps. exact Kps. }
    zstep. zstep. zstep.
    do 4 zstep. replace (bv_unsigned sp + -544 - 512)%Z with (bv_unsigned sp + -1056)%Z by lia.
    zstep. zstep. replace (bv_unsigned sp + -544 - 4096)%Z with (bv_unsigned sp + -4640)%Z by lia.

    destruct (stk_split rsegs _ _ (bv_unsigned sp + -4632) _ ST ltac:(lia)) as [ST1 ST2]. clear ST.
    destruct (stk_carve rsegs _ _ _ 8 ST1 ltac:(cbn; lia)) as [_ [jp PROBE]]. clear ST1.
    match type of PROBE with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -4640)%Z in PROBE by lia end.
    zstep0.
    pose proof (stk_of_rw_cells rsegs _ _ _ PROBE) as ST1.
    match type of ST1 with stk _ _ _ ?A => replace A with (bv_unsigned sp + -4632)%Z in ST1 by (cbn; lia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_merge rsegs mm _ _ _ ST1 ST2 ltac:(lia)) as ST end. clear ST1 ST2 PROBE.
    zstep. if_cases Kpr; zify_cond Kpr.
    { exfalso. revert Kpr. rewrite !signed_of_Z by lia. lia. }
    zstep.
    carve_frame 512%nat ST. rename FR into BIGb.
    zstep0.
    replace (bv_unsigned sp + -4640)%Z with (bv_unsigned sp - 4640)%Z in ST by lia.
    eapply L_b84; [ | hyp | exact FRs | exact E2 | exact EB | exact BF | exact BIGb | mk_wfile ].
    mk_finv.
  Qed.

End FmtFp.
End NF.

Definition fmt_fp_nf_stmt : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S17;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;A1;i0;A1;o1;#5;A1;i11;#6;A1;i11;i13;Y1;0;A1;o6;#9;A2;i162;#8;i13;A2;k33;o22;r15;Y4;f;Y4;4;A2;k87;#1;r61;A3;i30;#2;r55;A2;k129;#1;r26;Pra;R#2;Psp;R#2;Pgp;R#2;Ptp;R#2;Pt0;R#2;Pt1;R#2;Pt2;R#2;Ps0;R#2;Ps1;R#2;Pa0;R#2;Pa1;R#2;Pa2;R#2;Pa3;R#2;Pa4;R#2;Pa5;R#2;Pa6;R#2;Pa7;R#2;Ps2;R#2;Ps3;R#2;Ps4;R#2;Ps5;R#2;Ps6;R#2;Ps7;R#2;Ps8;R#2;Ps9;R#2;Ps10;R#2;Ps11;R#2;Pt3;R#2;Pt4;R#2;Pt5;R#2;Pt6;R#2;PF;RA2;k163;A1;o1;#3;#2;Pfc;RA1;i0;A1;o1;#4;Pm;RP~R#2;A1;i2;#6;Pfl0;R#6;Pj1;R#7;Pj2;R#7;Plbfw;R#2;PB;Ri13;Pjunk0;R#7;Pcanary;R#2;Pw;Ri13;Pp;Ri13;Pfl;Ri13;Pt;Ri13;Po0;R#8;Po1;R#8;Pret;Ri13;Ey;RA2;k35;A2;k87;#1;r38;A2;k149;A2;k37;#10;A1;o6;#0;A2;k87;#1;r37;i13;EFp;RA2;k87;#1;r40;i13;P~RA3;i30;A1;i2;#11;A6;k199;r5;r2;r9;r8;r7;r6;A2;o200;#11;A4;o161;#8;i13;r4;r3;P~RA2;k33;A1;o6;Y12;420;A2;k87;#1;r50;P~RA2;k46;A2;k87;#1;r51;A2;k37;#10;A1;o6;Y5;1f;P~RA2;k33;A1;o6;Y19;76a78;A2;k98;A2;k87;#1;r52;k469;P~RA2;k33;A2;k87;#1;r53;r5;P~RA2;k33;A2;k87;#1;r54;r17;P~RA2;i69;#12;A2;k33;r15;A1;o6;o74;P~RA2;i69;A2;k33;A1;k263;A2;k37;#10;A1;o6;#13;r15;A2;k46;r15;A2;k37;#10;A1;o6;#14;P~RA2;i69;#12;A2;k46;r15;A2;k37;#10;A1;o6;#4;P~RA2;i69;#12;A2;k46;r15;A1;o6;Y8;00;P~RA2;k33;A1;k36;A2;k53;i13;r14;A2;k35;A1;k36;A2;k53;i13;r15;A1;k36;A2;k53;#6;r21;P~RA2;k247;A2;k53;#6;r22;N256;P~RA4;k175;k4;r29;A2;k98;#15;k469;#15;P~RA2;k3;k4;r30;P~RA1;k174;r32;P~RA9;k176;r32;r16;r31;r30;r29;r28;r27;A1;k7;r20;r26;P~RA2;k178;r33;r26;P~R#16;P~R#16;P~R#16;P~R#16;P~RA1;k106;A3;i30;i13;A2;k87;#1;r55;A1;o6;#3;A3;k192;k4;A29;k470;r72;r71;r70;r69;r65;r64;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r41;r23;r38;r37;r36;r35;r34;r27;r26;r33;r32;r25;r39;A7;k167;A31;k168;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;r42;r41;A2;k129;#1;A1;o6;Y19;2e170;r40;A1;o113;#2;r39;A1;k170;k4;").

Lemma fmt_fp_nf_spec : fmt_fp_nf_stmt.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S38;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;A1;i0;A1;o1;#5;A1;i11;#6;A1;i11;i13;A2;i162;#8;i13;Y1;0;A1;o6;#10;A3;i30;A1;i2;#9;A6;k199;r3;A2;k35;A2;k87;#1;r38;A2;k149;A2;k37;#11;A1;o6;#0;A2;k87;#1;r37;r7;r6;r5;r4;A2;o200;#9;A4;o161;#8;i13;r2;r1;A2;k33;A1;o6;Y12;420;A2;k87;#1;r48;A2;k46;A2;k87;#1;r49;A2;k37;#11;A1;o6;Y5;1f;A2;k33;A1;o6;Y19;76a78;A2;k98;A2;k87;#1;r50;k469;A2;k33;A2;k87;#1;r51;A2;k87;#1;r43;A2;k33;A2;k87;#1;r52;r15;A2;k33;o22;r13;A2;i69;#18;A2;k33;r13;A1;o6;o74;Y4;f;Y4;4;A2;i69;A2;k33;A1;k263;A2;k37;#11;A1;o6;#20;r13;A2;k46;r13;A2;k37;#11;A1;o6;#21;A2;i69;#18;A2;k46;r13;A2;k37;#11;A1;o6;#4;A2;i69;#18;A2;k46;r13;A1;o6;Y8;00;A2;k33;A1;k36;A2;k53;i13;r12;A2;k35;A1;k36;A2;k53;i13;r13;A1;k36;A2;k53;#6;r19;A2;k247;A2;k53;#6;r20;N256;A2;k87;#1;r59;A4;k175;k4;r27;A2;k98;#27;k469;#27;A2;k3;k4;r28;A1;k174;r30;A9;k176;r30;A2;k87;#1;r54;r29;r28;r27;r26;r25;A1;k7;r18;r24;A2;k178;r31;r24;A3;i30;#2;r53;A2;k129;#1;r24;A1;k106;A3;i30;i13;A2;k87;#1;r53;A1;o6;#3;A29;k470;r70;r69;r68;r67;r63;r62;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r39;A2;k87;#1;r61;r36;r35;r34;r33;r32;r25;r24;r31;r30;r23;r37;A7;k167;A31;k168;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;r42;r41;r40;r39;A2;k129;#1;A1;o6;Y19;2e170;r38;A1;o113;#2;r37;A1;k170;k4;A3;k192;k4;#35;#36;cdLra;R#2;Lsp;R#2;Lgp;R#2;Ltp;R#2;Lt0;R#2;Lt1;R#2;Lt2;R#2;Ls0;R#2;Ls1;R#2;La0;R#2;La1;R#2;La2;R#2;La3;R#2;La4;R#2;La5;R#2;La6;R#2;La7;R#2;Ls2;R#2;Ls3;R#2;Ls4;R#2;Ls5;R#2;Ls6;R#2;Ls7;R#2;Ls8;R#2;Ls9;R#2;Ls10;R#2;Ls11;R#2;Lt3;R#2;Lt4;R#2;Lt5;R#2;Lt6;R#2;LF;RA2;k163;A1;o1;#3;#2;Lfc;RA1;i0;A1;o1;#4;Lm;RP~R#2;A1;i2;#6;Lfl0;R#6;Lj1;R#7;Lj2;R#7;Llbfw;R#2;LB;Ri13;Ljunk0;R#7;Lcanary;R#2;Lw;Ri13;Lp;Ri13;Lfl;Ri13;Lt;Ri13;Lo0;R#8;Lo1;R#8;Lret;Ri13;cdLHM;R#12;LSPLO;R#13;LSPHI;R#14;LGLO;R#15;LAF;R#16;LAB;R#17;LHw;R#19;LHp;R#22;LHfl;R#23;LHt;R#24;LROOM;R#25;LJ256;R#26;LST;R#28;LMI;R#29;LFRM;R#30;LWF;R#31;LSSP;R#32;LHa3;R#33;LHa4;R#33;LHa5;R#33;LHa6;R#33;LHps;R#34;cdA6;k471;k4;A29;k472;r70;r69;r68;r67;r63;r62;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r61;r39;r36;r35;r34;r33;r32;r31;r30;r25;r24;r23;r37;#35;#36;A69;k473;r70;r69;r68;r67;r63;r62;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r60;r59;r61;r39;r37;r36;r35;r34;r33;r32;r31;r30;r29;r28;r27;r26;r25;r24;r23;r22;r21;r20;r19;r18;r17;r16;r14;r13;r12;r11;r66;r65;r64;r58;r57;r56;r55;r54;r43;r42;r41;r40;r38;r10;r9;r8;r7;r6;r5;r4;r3;r2;r1;Lms';Ri165;LH;RA30;k472;r71;r70;r69;r68;r64;r63;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r62;r40;r37;r36;r35;r34;r33;r32;r31;r26;r25;r24;r38;r1;r1;#37;P~R#12;P~R#13;P~R#14;P~R#15;P~R#16;P~R#17;P~R#19;P~R#22;P~R#23;P~R#24;P~R#25;P~R#26;P~R#28;P~R#29;P~R#30;P~R#31;P~R#32;P~R#33;P~R#33;P~R#33;P~R#33;P~R#34;#37;k474;").
Qed.

Definition fmt_fp_facts' (y fl p t : Z) : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 4 "S0;Ly;Ri13;Lfl;Ri13;Lp;Ri13;Lt;Ri13;A2;i72;A2;k475;r4;r3;A4;k476;r4;r3;r2;r1;").

Definition fmt_fp'_stmt : Prop := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S19;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;A1;i0;A1;o1;#5;A1;i11;#6;A1;i11;i13;Y1;0;A1;o6;#9;A2;i162;#8;i13;Y4;f;A2;k33;A1;k263;A2;k37;#10;A1;o6;#12;r16;Y4;4;A2;k33;o22;r16;A1;o6;#4;A2;k87;#1;r63;A3;i30;#2;r57;A2;k129;#1;r28;Pra;R#2;Psp;R#2;Pgp;R#2;Ptp;R#2;Pt0;R#2;Pt1;R#2;Pt2;R#2;Ps0;R#2;Ps1;R#2;Pa0;R#2;Pa1;R#2;Pa2;R#2;Pa3;R#2;Pa4;R#2;Pa5;R#2;Pa6;R#2;Pa7;R#2;Ps2;R#2;Ps3;R#2;Ps4;R#2;Ps5;R#2;Ps6;R#2;Ps7;R#2;Ps8;R#2;Ps9;R#2;Ps10;R#2;Ps11;R#2;Pt3;R#2;Pt4;R#2;Pt5;R#2;Pt6;R#2;PF;RA2;k163;A1;o1;#3;#2;Pfc;RA1;i0;A1;o1;#4;Pm;RP~R#2;A1;i2;#6;Pfl0;R#6;Pj1;R#7;Pj2;R#7;Plbfw;R#2;PB;Ri13;Pjunk0;R#7;Pcanary;R#2;Pw;Ri13;Pp;Ri13;Pfl;Ri13;Pt;Ri13;Po0;R#8;Po1;R#8;Pret;Ri13;Ey;RA2;k35;A2;k87;#1;r38;A2;k149;A2;k37;#10;A1;o6;#0;A2;k87;#1;r37;i13;EFp;RA2;k87;#1;r40;i13;P~RA3;i30;A1;i2;#11;A6;k477;r5;r2;r9;r8;r7;r6;A2;o200;#11;A4;o161;#8;i13;r4;r3;P~RA4;k478;r3;r8;r9;r7;P~RA2;k33;A1;o6;Y12;420;A2;k87;#1;r51;P~RA2;k46;A2;k87;#1;r52;A2;k37;#10;A1;o6;Y5;1f;P~RA2;k33;A1;o6;Y19;76a78;A2;k98;A2;k87;#1;r53;k469;P~RA2;k33;A2;k87;#1;r54;r6;P~RA2;k33;A2;k87;#1;r55;r18;P~RA2;i69;#13;A2;k33;r16;A1;o6;o74;P~RA2;i69;#13;A2;k46;r16;A2;k37;#10;A1;o6;#14;P~RA2;i69;#15;A2;k46;r16;A2;k37;#10;#16;P~RA2;i69;#15;A2;k46;r16;A1;o6;Y8;00;P~RA1;k106;A3;i30;i13;A2;k85;r17;#16;A1;o6;Y6;21;P~RA2;k33;A1;k36;A2;k53;i13;r16;A2;k35;A1;k36;A2;k53;i13;r17;A1;k36;A2;k53;#6;r23;P~RA2;k247;A2;k53;#6;r24;N256;P~RA4;k175;k4;r31;A2;k98;#17;k469;#17;P~RA2;k3;k4;r32;P~RA1;k174;r34;P~RA9;k176;r34;r18;r33;r32;r31;r30;r29;A1;k7;r22;r28;P~RA2;k178;r35;r28;P~R#18;P~R#18;P~R#18;P~R#18;P~RA1;k106;A3;i30;i13;A2;k87;#1;r57;A1;o6;#3;A3;k192;k4;A29;k470;r74;r73;r72;r71;r67;r66;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r43;r25;r40;r39;r38;r37;r36;r29;r28;r35;r34;r27;r41;A7;k167;A31;k168;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;A2;k129;#1;A1;o6;Y19;2e170;r42;A1;o113;#2;r41;A1;k170;k4;").

Lemma fmt_fp'_spec : fmt_fp'_stmt.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S63;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;A1;i0;A1;o1;#5;A1;i11;#6;A1;i11;i13;A2;i162;#8;i13;A1;i2;#9;A2;k87;#1;r38;Y1;0;A1;o6;#12;A2;k37;#13;A1;o6;#0;A3;i30;#10;A6;k477;r3;A2;k35;#11;A2;k149;#14;A2;k87;#1;r37;r7;r6;r5;r4;A2;o200;#9;A4;o161;#8;i13;r2;r1;A4;k478;A2;k35;A2;k87;#1;r39;A2;k149;#14;#11;r6;r7;r5;A2;k33;A1;o6;Y12;420;A2;k87;#1;r49;A2;k46;A2;k87;#1;r50;A2;k37;#13;A1;o6;Y5;1f;A2;k33;A1;o6;Y19;76a78;A2;k98;A2;k87;#1;r51;k469;A2;k33;A2;k87;#1;r52;A2;k87;#1;r44;A2;k33;A2;k87;#1;r53;r16;Y4;f;A2;k33;A1;k263;A2;k37;#13;A1;o6;#22;r14;A2;i69;#23;A2;k33;r14;A1;o6;o74;Y4;4;A2;i69;#23;A2;k46;r14;A2;k37;#13;A1;o6;#25;A2;k33;o22;r14;A1;o6;#4;A2;i69;#27;A2;k46;r14;A2;k37;#13;#28;A2;i69;#27;A2;k46;r14;A1;o6;Y8;00;A1;k106;A3;i30;i13;A2;k85;r15;#28;A1;o6;Y6;21;A2;k33;A1;k36;A2;k53;i13;r14;A2;k35;A1;k36;A2;k53;i13;r15;A1;k36;A2;k53;#6;r21;A2;k247;A2;k53;#6;r22;N256;A2;k87;#1;r61;A4;k175;k4;r29;A2;k98;#34;k469;#34;A2;k3;k4;r30;A1;k174;r32;A9;k176;r32;A2;k87;#1;r56;r31;r30;r29;r28;r27;A1;k7;r20;r26;A2;k178;r33;r26;A3;i30;#2;r55;A2;k129;#1;r26;A1;k106;A3;i30;i13;A2;k87;#1;r55;A1;o6;#3;A2;k87;#1;r62;A2;k35;#42;A2;k149;#14;#34;A2;k475;#43;r29;A2;k87;#1;r63;A2;k475;A2;k35;#45;A2;k149;#14;#42;r30;A2;k87;#1;r65;A2;k129;#1;A1;o6;Y19;2e170;A1;o113;#2;A1;k170;k4;A2;k87;#1;r64;A2;k475;A2;k35;#51;A2;k149;#14;#45;r31;A2;k35;#47;A2;k149;#14;#51;A6;k477;r30;#53;r34;r33;r32;r31;A4;o161;#8;i13;r30;r29;Lo;R#10;A3;i30;#10;r1;A2;o200;#9;#55;A6;k199;r30;#53;r34;r33;r32;r31;A2;o200;#9;A4;o161;#8;i13;r29;r28;A2;k87;#1;r66;A2;k35;#59;A2;k149;#14;#47;A6;k484;r30;#53;r34;r33;r32;r31;A2;k35;A2;k87;#1;r67;A2;k149;#14;#59;cdLra;R#2;Lsp;R#2;Lgp;R#2;Ltp;R#2;Lt0;R#2;Lt1;R#2;Lt2;R#2;Ls0;R#2;Ls1;R#2;La0;R#2;La1;R#2;La2;R#2;La3;R#2;La4;R#2;La5;R#2;La6;R#2;La7;R#2;Ls2;R#2;Ls3;R#2;Ls4;R#2;Ls5;R#2;Ls6;R#2;Ls7;R#2;Ls8;R#2;Ls9;R#2;Ls10;R#2;Ls11;R#2;Lt3;R#2;Lt4;R#2;Lt5;R#2;Lt6;R#2;LF;RA2;k163;A1;o1;#3;#2;Lfc;RA1;i0;A1;o1;#4;Lm;RP~R#2;A1;i2;#6;Lfl0;R#6;Lj1;R#7;Lj2;R#7;Llbfw;R#2;LB;Ri13;Ljunk0;R#7;Lcanary;R#2;Lw;Ri13;Lp;Ri13;Lfl;Ri13;Lt;Ri13;Lo0;R#8;Lo1;R#8;Lret;Ri13;cdLHM;R#15;LFACTS;R#16;LSPLO;R#17;LSPHI;R#18;LGLO;R#19;LAF;R#20;LAB;R#21;LHw;R#24;LHp;R#26;LHfl;R#29;LHt;R#30;LHta;R#31;LROOM;R#32;LJ256;R#33;LST;R#35;LMI;R#36;LFRM;R#37;LWF;R#38;LSSP;R#39;LHa3;R#40;LHa4;R#40;LHa5;R#40;LHa6;R#40;LHps;R#41;Es;RA2;k479;#43;r29;A2;i480;#44;A1;k106;#44;m480;RNLs;RA2;i480;#46;A1;k106;#46;A3;k192;k4;A29;k470;r74;r73;r72;r71;r67;r66;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r43;#47;r40;r39;r38;r37;r36;r29;r28;r35;r34;r27;r41;A7;k167;A31;k168;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;#48;r42;#49;r41;#50;r1;2;Ln;R#46;A1;LNF;R#52;EHM;RA6;k78;#10;#54;#56;r27;#57;A7;k481;r30;#53;r34;r33;r32;r31;r1;A3;i30;#10;#57;#58;A70;k482;r76;r75;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;r42;r41;r40;r39;r38;r37;r36;r35;r34;r33;r32;r31;r30;r29;r1;r26;r25;r24;r23;r22;A8;k483;r31;#60;r35;r34;r33;r32;#55;r1;r20;r19;r18;r16;r15;r14;r13;r12;r11;r10;r9;r8;r7;r6;r5;r1;Ln;RA1;k106;#46;A1;LFIN;RA1;k106;#52;EHM;RA6;k78;#10;#54;#56;r27;#61;A7;k485;r30;#53;r34;r33;r32;r31;r1;A3;i30;#10;#61;#58;m72;RNL~RA2;i72;A2;k475;#60;r33;A4;k476;#60;r33;r34;r32;A3;k192;k4;A29;k470;r77;r76;r75;r74;r70;r69;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r46;A2;k87;#1;r68;r43;r42;r41;r40;r39;r32;r31;r38;r37;r30;r44;A7;k167;A31;k168;r77;r76;r75;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;#48;r45;#49;r44;#50;r27;2;L~RA2;k475;#60;r33;A1;LNF;RA2;k475;#62;r34;A2;k82;A3;k192;k4;A29;k470;r78;r77;r76;r75;r71;r70;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r47;A2;k87;#1;r69;r44;r43;r42;r41;r40;r33;r32;r39;r38;r31;r45;A7;k167;A31;k168;r78;r77;r76;r75;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;#48;r46;#49;r45;#50;A1;r4;r1;r1;L~RA4;k476;#60;r33;r34;r32;A1;LFACTS;RA4;k476;#62;r34;r35;r33;A72;k486;r78;r77;r76;r75;r74;r73;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;r42;r41;r40;r39;r38;r37;r36;r35;r34;r33;r32;r31;r3;r1;r28;r27;r26;r25;r24;r23;r22;r21;r20;r19;r18;r17;r16;r15;r14;r13;r12;r11;r10;r9;r8;r7;r1;r1;P~R#15;P~R#16;P~R#17;P~R#18;P~R#19;P~R#20;P~R#21;P~R#24;P~R#26;P~R#29;P~R#30;P~R#31;P~R#32;P~R#33;P~R#35;P~R#36;P~R#37;P~R#38;P~R#39;P~R#40;P~R#40;P~R#40;P~R#40;P~R#41;A3;k192;k4;A29;k470;r72;r71;r70;r69;r65;r64;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r41;#45;r38;r37;r36;r35;r34;r27;r26;r33;r32;r25;r39;A7;k167;A31;k168;r72;r71;r70;r69;r68;r67;r66;r65;r64;r63;r62;r61;r60;r59;r58;r57;r56;r55;r54;r53;r52;r51;r50;r49;r48;r47;r46;r45;r44;r43;r42;r41;#48;r40;#49;r39;#50;k487;").
Qed.
