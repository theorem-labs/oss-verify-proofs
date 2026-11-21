(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed rmmap_anon_spec, rmmap_fixed_spec, rmprotect_spec and 1 more. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent Require Import F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10 Require Import F_syscalls RF_vm_wait RMallocRep.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Npos"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.option"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.range_ans"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.MS"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.mkR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.munmap_ret"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.seg_rom"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.F_syscalls.rsegs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Numbers.BinNums.Zpos"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Numbers.BinNums.Zneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.mmap_len"; "Corelib.Init.Datatypes.nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Logic.True"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.mem_inv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.C4"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.rg_errno"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Numbers.BinNums.xH"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Numbers.BinNums.Z0"; "Corelib.Init.Logic.eq_ind_r"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.impl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.node"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.at_node"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.Exc.exc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.enode"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.NMunmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_munmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.epost"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.rmunmap_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RMallocRep.rmunmap_entry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_refl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.mmap_len_ge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.impl_enode"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_carve"; "Stdlib.micromega.ZifyClasses.rew_iff_rev"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.micromega.ZifyClasses.mkrel"; "Corelib.Init.Logic.iff_refl"; "Corelib.Init.Logic.eq_refl"; "Stdlib.micromega.ZifyClasses.mkapp2"; "Stdlib.micromega.ZifyClasses.inj"; "Stdlib.micromega.ZifyInst.Inj_Z_Z"; "Stdlib.micromega.ZifyClasses.mkapp"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.pow_pos_nonneg"; "Stdlib.ZArith.BinInt.Z.pow_nonneg"; "Stdlib.micromega.ZMicromega.ZArithProof"; "Corelib.Init.Datatypes.list"; "Stdlib.micromega.VarMap.Branch"; "Stdlib.micromega.VarMap.Elt"; "Stdlib.micromega.VarMap.Empty"; "Stdlib.micromega.VarMap.t"; "Stdlib.micromega.Tauto.IMPL"; "Stdlib.micromega.RingMicromega.Formula"; "Stdlib.micromega.Tauto.eKind"; "Corelib.Init.Datatypes.unit"; "Stdlib.micromega.Tauto.isProp"; "Stdlib.micromega.Tauto.A"; "Stdlib.micromega.RingMicromega.Build_Formula"; "Stdlib.micromega.EnvRing.PEX"; "Stdlib.micromega.RingMicromega.OpLe"; "Stdlib.micromega.EnvRing.PEsub"; "Stdlib.micromega.EnvRing.PEc"; "Corelib.Init.Datatypes.tt"; "Stdlib.micromega.Tauto.BFormula"; "Stdlib.micromega.ZMicromega.ZTautoChecker_sound"; "Corelib.Init.Datatypes.true"; "Stdlib.micromega.ZMicromega.ZTautoChecker"; "Stdlib.micromega.VarMap.find"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.CB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.resp"; "Corelib.Init.Datatypes.Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ITree.nret"; "Stdlib.micromega.EnvRing.PEadd"; "Stdlib.micromega.RingMicromega.OpEq"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_step"; "LinuxProcessSemantics.Riscv.Prelude.TNode"; "LinuxProcessSemantics.Riscv.Prelude.TEmpty"; "Corelib.Init.Logic.conj"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.lift_result"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.interp_eff0"; "LinuxProcessSemantics.Riscv.Sem.exec"; "LinuxProcessSemantics.Riscv.Instr.OpImm"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "stdpp.bitvector.definitions.BV"; "stdpp.bitvector.definitions.Z_to_bv_obligation_1"; "LinuxProcessSemantics.Riscv.Sem.Core"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addi"; "stdpp.bitvector.definitions.bv_signed"; "stdpp.bitvector.definitions.bv_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.lit_add_lit"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "LinuxProcessSemantics.Riscv.Prelude.sext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_addi"; "LinuxProcessSemantics.Riscv.Prelude.tset"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_set"; "LinuxProcessSemantics.Riscv.Prelude.tget"; "LinuxProcessSemantics.Riscv.Sem.w0"; "LinuxProcessSemantics.Riscv.Sem.core"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Sem.reg_get"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.step_gen"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.wa"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.le8"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.Z_to_le_bytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineFault"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineUnmodeled"; "Stdlib.ZArith.BinInt.Z.add_assoc"; "Corelib.Init.Logic.eq_ind"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_cb_split"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cb_split_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cb_split"; "stdpp.tactics.f_equal_help"; "Corelib.Init.Logic.eq_sym"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.wa_of_Z_to_bv"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_store_ok_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.csize"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.store_bytes_8'"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.unsigned_Z_to_bv_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_addsext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_bound"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cells_size"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.mem_inv_store_cbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.C8"; "Corelib.Init.Logic.I"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_store_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cbytes"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_write"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Cells.cell_upd"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_frame"; "Stdlib.micromega.ZifyClasses.rew_iff"; "Stdlib.micromega.ZifyClasses.and_morph"; "Stdlib.micromega.ZifyClasses.eq_iff"; "Stdlib.micromega.Tauto.AND"; "Stdlib.micromega.Tauto.X"; "Stdlib.micromega.EnvRing.PEpow"; "Corelib.Init.Datatypes.length"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.length_le8"; "Stdlib.micromega.ZifyClasses.or_morph"; "Stdlib.micromega.ZMicromega.RatProof"; "Stdlib.micromega.RingMicromega.PsatzAdd"; "Stdlib.micromega.RingMicromega.PsatzIn"; "Corelib.Init.Datatypes.O"; "Stdlib.micromega.ZMicromega.DoneProof"; "Stdlib.micromega.Tauto.OR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_write"; "Corelib.Init.Logic.False"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.inside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_write"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_write"; "Stdlib.ZArith.BinInt.Z.add_0_r"; "LinuxProcessSemantics.Riscv.Instr.Jal"; "stdpp.bitvector.definitions.bv_unsigned_in_range"; "stdpp.bitvector.definitions.bv_modulus"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.stk_lo_nonneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.unsigned_lit"; "Stdlib.ZArith.BinInt.Z.of_N"; "Corelib.Numbers.BinNums.N"; "Stdlib.micromega.RingMicromega.OpLt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_cut"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_vm_wait.rvmwait_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_vm_wait.rvmwait_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.rw_cells_transport"; "Stdlib.micromega.Tauto.TT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.disjoint_from"; "Stdlib.micromega.RingMicromega.PsatzMulC"; "Stdlib.micromega.EnvRing.Pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.munch_weaken"; "Corelib.Init.Logic.not"; "Stdlib.micromega.Tauto.NOT"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.outside"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.sub_fp"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.wmono_trans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc_even"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.w0_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.evt_ecall"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.MSsvc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.areg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_munmap_Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.efferr"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.eff0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.RgErr"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_writes"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_unmaps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.F_syscalls.sysret_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.F_syscalls.sysret_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.sysret_val"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.sysret_errno"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.errno_of"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.errno_of_errno_ret"; "LinuxProcessSemantics.Riscv.Instr.OpImm32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_addiw"; "stdpp.bitvector.definitions.bv_swrap"; "LinuxProcessSemantics.Riscv.Sem.alu32"; "LinuxProcessSemantics.Riscv.Sem.low32"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.w_addiw"; "LinuxProcessSemantics.Riscv.Instr.Load"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "stdpp.bitvector.definitions.bv_extract"; "Corelib.Numbers.BinNums.N0"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.load_u64"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.rw_cells_read_at"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.Z_to_bv_lit_self"; "LinuxProcessSemantics.Riscv.Instr.Jalr"; "stdpp.bitvector.definitions.bv_and"; "stdpp.bitvector.definitions.bv_not"; "LinuxProcessSemantics.Riscv.Sem.w1"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.ret_pc_fold"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.MState.w1_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Frame.stk_release"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Exec.evt_done"; "Corelib.Init.Logic.ex_intro"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.apply_mem_none"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.nret_MSsvc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.RgDone"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.rw_cells_unmaps_other"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.stk_unmaps_other"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.munch_unmaps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.mem_inv_unmaps"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.errno_of_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.apply_mem_unmaps"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg"; "Stdlib.ZArith.BinInt.Z.div_mod"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.mod_pos_bound"; "Stdlib.ZArith.BinInt.Z.mod_neg_bound"; "Stdlib.omega.PreOmega.Z.div_0_r_ext"; "Stdlib.omega.PreOmega.Z.mod_0_r_ext"; "Stdlib.micromega.ZMicromega.CutProof"; "Stdlib.micromega.EnvRing.PEmul"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.land_m4096"; "Stdlib.ZArith.BinInt.Z.land_comm"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RMallocRep.RPAGE_SIZE"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.NMprotect"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mprotect"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.rmprotect_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RMallocRep.rmprotect_entry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.LiaTuning.zify_done"; "LinuxProcessSemantics.Riscv.Instr.Auipc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_auipc"; "Stdlib.ZArith.BinInt.Z.shiftl"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Step.unsigned_Z_to_bv_add_r"; "stdpp.bitvector.definitions.bv_concat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_auipc"; "LinuxProcessSemantics.Riscv.Instr.Op"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_add"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_add"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_sub"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_sub"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_and"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_and"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.rmprotect_args"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mprotect_Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.mmap_len_aligned"; "Stdlib.micromega.RingMicromega.PsatzMulE"; "Stdlib.micromega.RingMicromega.PsatzC"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RMallocRep.ref_ro_addr_false"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Mem.ro_addr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.rw_cells_zeros_other"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.stk_zeros"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.munch_zeros"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.wmono_zeros"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.mem_inv_zeros"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.rw_cells_zeros_new"; "Corelib.Init.Nat.add"; "Stdlib.ZArith.BinInt.Z.max"; "Stdlib.Arith.PeanoNat.Nat.add"; "Stdlib.ZArith.Znat.Nat2Z.inj_add"; "Stdlib.micromega.ZifyInst.of_nat_to_nat_eq"; "Stdlib.ZArith.BinInt.Z.max_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.apply_mem_zeros"; "Stdlib.ZArith.BinInt.Z.mod_small"; "Stdlib.ZArith.BinInt.Z.ones"; "Stdlib.ZArith.BinInt.Z.land_ones"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.mmap_ans"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.mmap_fix_errno"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.mmap_raw"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.mmap_addr_ok"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.RunP.alloc_ceiling"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Nodes.NMmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mmap_none"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mmap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.rmmap_anon_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RMallocRep.rmmap_entry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.RunP.alloc_ceiling_range"; "LinuxProcessSemantics.Riscv.Instr.ShiftImm"; "LinuxProcessSemantics.Riscv.Instr.ALU_SLL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_slli"; "LinuxProcessSemantics.Riscv.Prelude.zext"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_slli"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Instr.Branch"; "LinuxProcessSemantics.Riscv.Instr.BC_EQ"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.eqb_eq"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_srli"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_srli"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "LinuxProcessSemantics.Riscv.Instr.BC_LTU"; "Stdlib.ZArith.BinInt.Z.ltb"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.inr64_unsigned_lit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_lit"; "Stdlib.ZArith.BinInt.Z.ltb_lt"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_andi"; "stdpp.bitvector.definitions.bv_wrap"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_andi"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Instr.BC_NE"; "Corelib.Init.Logic.proj1"; "Stdlib.Bool.Bool.negb_true_iff"; "Stdlib.ZArith.BinInt.Z.eqb_neq"; "Corelib.Init.Logic.False_ind"; "Stdlib.Bool.Bool.negb_false_iff"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mmap_none_Some"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.MmErr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.MmOk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.dec_mmap_Some"; "Stdlib.ZArith.BinInt.Z.lxor"; "LinuxProcessSemantics.Riscv.Instr.ALU_XOR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_xori"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_xori"; "Stdlib.ZArith.BinInt.Z.lor"; "LinuxProcessSemantics.Riscv.Instr.ALU_OR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.alu_or"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_word"; "stdpp.bitvector.definitions.bv_eq"; "Stdlib.ZArith.BinInt.Z.lor_0_l"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zb_lxor_ones"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.SysStep.unsigned_errno_ret"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.mmap_addr_ok_true"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.Decode.avoids"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.unsigned_lit_land"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.land_ones64"; "LinuxProcessSemantics.Riscv.Instr.Lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.v_lui"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PropExec.b_lui"; "Stdlib.ZArith.BinInt.Z.ltb_ge"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Agent.F_mm_syscalls.fixed_shape"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Pm10.RF_mm_syscalls.CEIL_WRAP_1.rmmap_fixed_post"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_lor"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib.ZBridge.zr_lxor"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Stdlib.ZArith.BinInt.Z.lor_eq_0_iff"].

Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop := ltac2:(Rpl.RP.run_k (rplG ()) 24 "U12;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;P~R#2;A1;i4;A1;i0;A1;o1;#5;A2;i19;i3;i3;A2;k22;#1;r39;A2;k24;A2;k22;#1;r37;A1;o25;Y7;24;Y2;0;A3;k28;k16;r19;r2;Lra;R#2;Lsp;R#2;Lgp;R#2;Ltp;R#2;Ls0;R#2;Ls1;R#2;Ls2;R#2;Ls3;R#2;Ls4;R#2;Ls5;R#2;Ls6;R#2;Ls7;R#2;Ls8;R#2;Ls9;R#2;Ls10;R#2;Ls11;R#2;LF;RA2;k2;A1;o1;#3;#2;Lfc;RA1;i0;A1;o1;#4;LA;Ri3;LL;Ri3;Lerrv;R#2;Llo;Ri3;Lm;R#6;La;Ri5;Lms';Ri6;A2;i7;#2;Lt0;R#2;A2;i7;#2;Lt1;R#2;A2;i7;#2;Lt2;R#2;A2;i7;#2;La1;R#2;A2;i7;#2;La2;R#2;A2;i7;#2;La3;R#2;A2;i7;#2;La4;R#2;A2;i7;#2;La5;R#2;A2;i7;#2;La6;R#2;A2;i7;#2;La7;R#2;A2;i7;#2;Lt3;R#2;A2;i7;#2;Lt4;R#2;A2;i7;#2;Lt5;R#2;A2;i7;#2;Lt6;R#2;A2;i7;#6;Lm';R#6;A2;i8;A3;i9;i6;r16;A7;k10;A31;k11;r40;r39;r38;r37;r15;r14;r13;r36;r35;A1;k12;r17;r12;r11;r10;r9;r8;r7;r6;r34;r33;r32;r31;r30;r29;r28;r27;r26;r25;r5;r4;r3;r2;r24;A1;k13;r40;r23;A1;o14;#2;r1;A1;k15;k16;A2;i8;A3;k17;A3;o18;#7;A4;o20;i3;i3;A2;k21;#8;A1;o23;#0;#8;A3;o18;#7;A4;o20;i3;i3;#9;A2;k24;#9;A1;o23;#10;A3;o18;#7;A4;o20;i3;i3;r22;A2;k24;r22;A1;k26;r21;A1;o27;#7;r18;r1;A2;i8;m5;RNLa;Ri5;pr17;2;Le;Ri3;#11;Lchanged;Ri29;m29;RNLchanged;Ri29;pr1;2;i30;#11;A2;i8;A2;k31;k16;r1;A2;i8;A4;k32;k16;r1;r19;#8;A2;i8;A4;k33;k16;r1;#9;A3;o18;i34;A1;o35;A2;k36;r17;r20;A1;o27;i34;m5;RNLa;Ri5;pr17;2;Le;Ri3;A2;i8;A2;k37;A1;o23;o38;r1;A2;k37;r1;A1;o23;Y11;7ff;Lchanged;Ri29;i30;").

Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 64)%Z -> (0xf6000 <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR VML MI -> -> A0 AL L0 LO CEILJ SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.
  call_sp rvmwait_spec; [exact ST | exact VML | exact MI | lia | lia | ].
  match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ RVMLOCK _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
  do 3 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 0 "S124;A1;o23;Y12;000;A3;i9;i3;A2;k270;r2;#0;o40;A2;k37;o40;r4;Y1;0;A1;o23;#3;Y6;00;A1;o23;#5;A2;k43;#4;#6;A1;o1;#5;A2;k39;#8;r7;A2;k22;#8;#9;A1;o23;Y63;7ffffffffffff000;A1;i0;#8;A2;k39;#8;r1;A2;k39;#8;r8;A3;i9;#12;#13;#14;A2;k24;r8;r7;Y11;7ff;A1;o23;#17;A2;k24;#16;#18;A2;k22;#8;A2;k39;#8;A2;k271;A2;k22;#8;A2;k39;#8;#19;#11;A2;k22;#8;#13;A2;k39;#8;A2;k271;r1;#11;A2;k22;#8;#22;A2;k24;A2;k24;r7;r6;#18;A2;k39;#8;A2;k271;r8;#11;A2;k21;r7;A2;k270;r7;#0;A2;k270;r8;#0;A2;k39;#8;A2;k21;r8;#27;A3;k272;r7;#0;r3;A2;k37;o40;#0;P~R#30;A2;k37;o40;#27;A2;k70;#4;#6;P~RA2;k42;o40;#4;P~RA2;k37;o40;#6;A2;k42;o40;#7;A2;k37;o40;#4;LHa;R#34;L~Ri30;A3;k71;#4;#6;r2;PHa;R#34;P~Ri30;A2;k37;o40;#7;A3;k272;r9;#0;r5;P~R#30;A2;k37;o40;A2;k270;r10;#0;A1;o27;i72;A1;i73;i72;A2;o75;i3;r3;A1;o76;i3;A4;o74;i3;#41;r2;#42;A1;i77;i3;A1;i79;i3;A2;o88;i3;o40;A2;o88;i3;#0;A1;o14;i81;A2;o85;i3;#3;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#49;o89;A2;o85;i3;o38;A2;k90;#45;o82;A4;k91;r1;r3;cvA2;o64;i29;o92;A3;i9;i29;A2;k93;r1;r3;o92;A3;k94;i3;o40;r2;A2;k37;o40;r3;A3;i9;i3;#0;o40;A1;k211;#55;A2;k24;r9;r8;A2;k24;#57;#18;A2;k270;#58;#0;A2;k42;o40;#0;A2;k24;r10;r9;A2;k24;#61;#18;A2;k270;#62;#0;A2;k42;#0;o40;A2;k24;A2;k24;r11;r10;#18;A2;k270;#65;#0;A2;k24;A2;k24;r12;r11;#18;A2;k24;A2;k24;r13;r12;#18;A2;k270;r17;#0;A2;k270;r18;#0;A2;k270;r23;#0;A2;k270;r24;#0;A2;o208;i3;A1;o25;o38;N7;A2;o183;i3;#74;N6;A2;o183;i3;#76;N3;A2;o183;i3;#78;N2;A2;o183;i3;#80;N1;A2;o183;i3;#82;A2;o183;i3;o184;N4;A3;o182;i3;#83;#84;A6;o212;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#47;o101;#46;o89;Y3;0;A2;o85;i3;Y2;1;Y2;3;Y2;0;A2;o85;i3;#91;Y1;1;A2;o85;i3;#93;A3;o100;i3;#51;#49;A3;o100;i3;#95;A2;o88;i3;#18;P~R#55;i188;P~R#97;A3;i9;i3;r3;A2;k24;A2;k274;#0;r9;r6;A2;k24;r7;r8;A2;k39;#8;r10;A2;k39;#8;r9;A3;i9;#12;#100;#100;A2;k22;#8;#100;A2;k21;#57;r9;A1;k39;#8;A2;k272;#62;#0;P~RA2;k37;o40;#62;P~R#30;A2;k37;o40;A2;k270;#67;#0;A3;k272;r12;#0;r8;P~R#30;A2;k37;o40;A2;k270;r13;#0;A2;k24;r1;r2;A3;o177;i3;A2;o88;i3;#4;#8;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#51;o89;L__x2;Ri3;L__x1;Ri3;E__wit;RA3;o18;i72;A2;o181;A3;o182;i3;#79;A3;o182;i3;#81;#84;o185;#39;#40;E__varmap;RA4;o74;i3;A4;o74;i3;#41;r3;#42;r2;#42;#44;E__ff;RA8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o100;i3;A3;o100;i3;#51;#92;#47;o86;#111;o89;#48;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#92;o89;#48;A8;o78;#45;k80;i81;i81;o82;#112;#48;A7;o175;#45;k80;i81;i81;o82;#112;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#51;o200;#111;o89;#52;#53;A2;k37;A2;k24;#110;#0;#7;P__x2;Ri3;P__x1;Ri3;P~R#114;P~R#54;P~R#54;A2;i8;#2;A2;k42;r4;#7;A5;r1;r14;r15;r9;r10;r11;A3;o18;i72;A2;o181;A3;o182;i3;#81;#86;o185;#39;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o100;i3;#95;#47;o86;#111;o89;A2;k24;r4;r5;A2;k24;#119;#18;A5;r1;r11;r12;r6;r7;r8;E__sat4;R#29;#31;E__sat3;R#32;#33;E__sat2;R#35;#36;E__sat1;R#37;#38;E__arith;RL__x2;Ri3;L__x1;Ri3;E__wit;R#117;#40;E__varmap;R#43;#44;E__ff;RA8;o78;#45;k80;i81;i81;o82;#118;#48;A8;o78;#45;k80;i81;i81;o82;#50;#48;A8;o78;#45;k80;i81;i81;o82;#112;#48;A7;o175;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#96;o89;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#96;o200;#111;o89;#52;#53;P__x2;Ri3;P__x1;Ri3;P~R#114;P~R#54;P~R#54;A2;i8;A2;k37;o40;#120;A2;k42;#120;#7;#121;E__sat4;R#29;#31;E__sat3;R#32;#33;E__sat2;R#35;#36;E__sat1;R#37;#38;E__arith;R#113;#115;#121;LA;Ri3;LL;Ri3;LHA;R#1;LHL;R#1;LA0;R#2;LL0;R#2;LB;RA2;k37;A2;k24;A2;k24;r6;r5;#0;#7;A6;k41;i3;A2;k271;#10;#11;Lz;Ri3;A2;i8;#15;A3;i9;#12;A2;k39;#8;A2;k21;#20;#21;#9;A6;k41;i3;r7;Lz;Ri3;A2;i8;A3;i9;#12;#22;#14;A3;i9;#12;A2;k39;#8;A2;k21;#20;#23;#9;A6;k41;i3;#24;Lz;Ri3;A2;i8;A3;i9;#12;#25;#14;A3;i9;#12;A2;k39;#8;A2;k21;#23;A2;k22;#8;#25;#9;A6;k41;i3;#26;Lz;Ri3;A2;i8;#15;A3;i9;#12;A2;k39;#8;A2;k21;A2;k22;#8;A2;k39;#8;A2;k271;#19;#11;#21;#9;A6;k41;i3;A2;k21;#24;A2;k270;#24;#0;Lz;Ri3;A2;i8;A3;i9;#12;#28;#14;A3;i9;#12;A2;k39;#8;A2;k21;#21;A2;k22;#8;#28;#9;EE1;RE__sat4;R#29;#31;E__sat3;R#32;#33;E__sat2;R#35;#36;E__sat1;R#37;#38;E__arith;RL__x2;Ri3;L__x1;Ri3;E__wit;R#39;#40;E__varmap;R#43;#44;E__ff;RA8;o78;#45;k80;i81;i81;o82;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#47;o89;#48;#50;#48;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#49;o101;#46;o89;#48;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o87;i3;#51;#49;o101;#51;o89;#52;#53;P__x2;Ri3;P__x1;Ri3;P~RP~R#30;#54;P~RA3;i9;i3;r3;o40;A3;i9;i3;A2;k21;r3;r4;r3;A4;r1;A2;k270;r12;#0;r12;r5;r10;A3;i9;i3;#26;r7;EE2;REH;RA2;k273;#19;#0;P~R#56;A3;i9;i3;#58;A2;k24;A2;k274;#0;A2;k275;#58;#0;#59;EH0;RA2;k276;#58;#0;P~R#60;A2;i8;A2;k37;o40;#63;A2;k42;#63;#0;EH1;RA2;k277;#62;#0;P~R#64;A2;i8;A2;k42;#0;#66;A2;k37;#66;o40;EH2;RA2;k278;#65;#0;P~R#55;A3;i9;i3;A2;k275;#67;#0;o40;EH3;RA2;k279;#67;#0;P~R#55;A3;i9;i3;A2;k270;#68;#0;#68;Eq;RA2;k275;#68;#0;i3;Er;RA2;k270;A2;k24;A2;k24;r14;r13;#18;#0;i3;EH4;RA2;k273;r15;#0;P~R#56;A3;i9;i3;r16;A2;k24;A2;k274;#0;A2;k275;r16;#0;A2;k270;r16;#0;EH5;RA2;k276;r16;#0;P~R#60;A2;i8;A2;k37;o40;#69;A2;k42;#69;#0;EH6;RA2;k277;r17;#0;P~R#64;A2;i8;A2;k42;#0;#70;A2;k37;#70;o40;EH7;RA2;k278;r18;#0;P~R#55;A3;i9;i3;A2;k275;r19;#0;o40;EH8;RA2;k279;r19;#0;P~R#55;A3;i9;i3;A2;k270;r20;#0;r20;Eq0;RA2;k275;r20;#0;i3;Er0;RA2;k270;r21;#0;i3;EH9;RA2;k273;r21;#0;P~R#56;A3;i9;i3;r22;A2;k24;A2;k274;#0;A2;k275;r22;#0;A2;k270;r22;#0;EH10;RA2;k276;r22;#0;P~R#60;A2;i8;A2;k37;o40;#71;A2;k42;#71;#0;EH11;RA2;k277;r23;#0;P~R#64;A2;i8;A2;k42;#0;#72;A2;k37;#72;o40;EH12;RA2;k278;r24;#0;P~R#55;A3;i9;i3;A2;k275;r25;#0;o40;EH13;RA2;k279;r25;#0;P~R#55;A3;i9;i3;A2;k270;r26;#0;r26;Eq1;RA2;k275;r26;#0;i3;Er1;RA2;k270;r27;#0;i3;E__sat15;R#32;#33;E__sat14;R#35;#36;E__arith;RL__x8;Ri3;L__x7;Ri3;L__x6;Ri3;L__x5;Ri3;L__x4;Ri3;L__x3;Ri3;L__x2;Ri3;L__x1;Ri3;E__wit;RA3;o18;i72;A2;o280;A3;o182;i3;A3;o207;i3;#73;#75;A3;o182;i3;A3;o207;i3;#73;#77;A3;o182;i3;#79;A3;o182;i3;#81;A3;o182;i3;A3;o207;i3;#73;#83;#84;A2;o280;A3;o182;i3;A2;o183;i3;N8;A3;o182;i3;#75;A3;o182;i3;#77;A3;o182;i3;A3;o207;i3;#73;A2;o183;i3;#85;A3;o182;i3;A3;o207;i3;#73;#79;#81;A2;o181;#86;o185;#39;#40;E__varmap;RA4;o74;i3;A4;o74;i3;A4;o74;i3;A2;o75;i3;r9;r5;#42;r3;A2;o75;i3;r7;r2;A4;o74;i3;A2;o75;i3;r6;r4;A2;o75;i3;r8;#44;E__ff;RA8;o78;#45;k80;i81;i81;o82;A8;o78;#45;k80;i81;i81;o82;#87;#48;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#49;o101;A3;o100;i3;A3;o281;i3;#47;A2;o85;i3;#88;#89;o89;#48;A8;o78;#45;k80;i81;i81;o82;A8;o78;#45;k80;i81;i81;o82;#87;#48;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#51;o101;A3;o100;i3;A3;o281;i3;#47;A2;o85;i3;#90;#92;o89;#48;A8;o78;#45;k80;i81;i81;o82;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o200;#47;o89;#48;A7;o175;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#94;o89;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#94;o200;#47;o89;#48;A8;o78;#45;k80;i81;i81;o82;A8;o78;#45;k80;i81;i81;o82;#87;#48;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#96;o101;A3;o100;i3;A3;o281;i3;#47;A2;o85;i3;Y2;2;#94;o89;#48;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o87;i3;#51;#92;o101;#51;o89;#48;A8;o78;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#89;o101;#46;o89;#48;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o87;i3;#96;#94;o101;#95;o89;#52;#53;P__x8;Ri3;P__x7;Ri3;P__x6;Ri3;P__x5;Ri3;P__x4;Ri3;P__x3;Ri3;P__x2;Ri3;P__x1;Ri3;P~R#98;P~R#98;P~RP~R#60;A2;i8;A2;k37;o40;r6;A2;k42;r6;#0;P~RP~R#97;A3;i9;i3;A2;k24;A2;k24;r5;r6;#18;A2;k24;A2;k274;#0;r10;r7;P~RA3;i9;i3;A2;k21;r5;r8;r5;P~RA3;i9;i3;r10;o40;A3;i9;i3;A2;k21;A2;k24;#99;#18;r9;#99;A14;r1;r5;r12;r19;r4;r11;r18;r31;r32;r10;r17;r23;r24;r25;r29;A3;i9;i3;A2;k21;#19;A2;k270;#19;#0;#16;A6;k41;i3;r9;Lz;Ri3;A2;i8;A3;i9;#12;#13;#100;A3;i9;#12;A2;k39;#8;A2;k21;A2;k22;#8;A2;k39;#8;A2;k21;#62;#63;#21;#101;A6;k41;i3;#57;Lz;Ri3;A2;i8;#102;A3;i9;#12;A2;k39;#8;A2;k21;#21;#103;#101;A6;k41;i3;#57;Lz;Ri3;A2;i8;#102;A3;i9;#12;A2;k39;#8;A2;k21;r1;#103;#101;A6;k41;i3;r9;Lz;Ri3;A2;i8;#102;A3;i9;#12;A2;k39;#8;A2;k21;#61;r1;#101;A4;o105;A3;i9;#12;#101;#101;A3;i9;#12;A2;k39;#8;#104;#14;A2;o64;#12;#101;A8;k153;i3;#12;#105;#105;#104;r8;A2;o64;P~Ri3;#12;#105;E__sat7;R#37;#38;E__sat6;R#106;#107;E__sat5;R#32;#33;E__sat4;R#35;#36;E__sat3;R#108;#109;E__arith;RL__x2;Ri3;L__x1;Ri3;E__wit;R#39;#40;E__varmap;R#43;#44;E__ff;RA7;o83;#45;k80;i81;i81;o82;A4;o84;i3;A3;o87;i3;#95;#51;o101;#49;o89;#52;#53;P__x2;Ri3;P__x1;Ri3;A3;i9;i3;A2;k21;#110;r1;r2;A2;r1;r14;r15;A2;k22;#8;#101;A2;k197;r9;E__sat7;R#37;#38;E__sat6;R#106;#107;E__sat5;R#32;#33;E__sat4;R#35;#36;E__sat3;R#108;#109;E__arith;R#113;#115;#116;A2;k22;#8;A2;k39;#8;#57;A2;k197;#57;E__sat7;R#37;#38;E__sat6;R#106;#107;E__sat5;R#32;#33;E__sat4;R#35;#36;E__sat3;R#108;#109;E__arith;RL__x2;Ri3;L__x1;Ri3;E__wit;R#117;#40;E__varmap;R#43;#44;E__ff;RA8;o78;#45;k80;i81;i81;o82;#118;#48;A8;o78;#45;k80;i81;i81;o82;#50;#48;A8;o78;#45;k80;i81;i81;o82;#112;#48;A7;o175;#45;k80;i81;i81;o82;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#46;o86;#95;o89;A7;o83;#45;k80;i81;i81;o82;A4;o84;i3;#95;o200;#111;o89;#52;#53;P__x2;Ri3;P__x1;Ri3;P~R#114;P~R#54;P~R#54;A2;i8;A2;k37;o40;#119;A2;k42;#119;#7;#116;A2;k21;#58;#59;r1;A2;k21;r9;A2;k270;r9;#0;r2;A2;k271;#24;#11;A2;k282;#24;#122;A2;k271;r7;#11;A2;k282;r7;#123;A2;k22;#8;A2;k39;#8;#24;A2;k197;#24;#122;#10;A2;k197;r7;#123;A2;k271;#11;#10;A2;k283;#11;#10;").
Qed.

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop := ltac2:(Rpl.RP.run_k (rplG ()) 24 "S15;Y6;00;A1;o1;#0;A1;i0;#1;Y2;1;Y5;00;Y3;0;A1;o1;#5;A1;i0;#6;P~R#2;A1;i4;#7;A2;i19;i3;i3;A2;k22;#1;r39;A2;k24;A2;k22;#1;r37;A1;o25;Y7;24;Y2;0;A1;o27;i34;A1;k285;r22;Lra;R#2;Lsp;R#2;Lgp;R#2;Ltp;R#2;Ls0;R#2;Ls1;R#2;Ls2;R#2;Ls3;R#2;Ls4;R#2;Ls5;R#2;Ls6;R#2;Ls7;R#2;Ls8;R#2;Ls9;R#2;Ls10;R#2;Ls11;R#2;LF;RA2;k2;A1;o1;#3;#2;Lfc;RA1;i0;A1;o1;#4;LA;Ri3;LL;Ri3;Lerrv;R#2;Llo;Ri3;Lm;R#8;La;Ri5;Lms';Ri6;A2;i7;#2;Lt0;R#2;A2;i7;#2;Lt1;R#2;A2;i7;#2;Lt2;R#2;A2;i7;#2;La1;R#2;A2;i7;#2;La2;R#2;A2;i7;#2;La3;R#2;A2;i7;#2;La4;R#2;A2;i7;#2;La5;R#2;A2;i7;#2;La6;R#2;A2;i7;#2;La7;R#2;A2;i7;#2;Lt3;R#2;A2;i7;#2;Lt4;R#2;A2;i7;#2;Lt5;R#2;A2;i7;#2;Lt6;R#2;A2;i7;#8;Lm';R#8;A2;i8;A3;i9;i6;r16;A7;k10;A31;k11;r40;r39;r38;r37;r15;r14;r13;r36;r35;A1;k12;r17;r12;r11;r10;r9;r8;r7;r6;r34;r33;r32;r31;r30;r29;r28;r27;r26;r25;r5;r4;r3;r2;r24;A1;k13;r40;r23;A1;o14;#2;r1;A1;k15;k16;A2;i8;A3;k17;A3;o18;#9;A4;o20;i3;i3;A2;k21;#10;A1;o23;#4;#10;A3;o18;#9;A4;o20;i3;i3;#11;A2;k24;#11;A1;o23;#12;A3;o18;#9;A4;o20;i3;i3;r22;A2;k24;r22;r21;A1;o27;#9;r18;r1;A2;i8;A3;k28;k16;r18;r1;A2;i8;A2;k31;k16;r1;A2;i8;A4;k32;k16;r1;r19;#10;A2;i8;A4;k33;k16;r1;#11;A3;o18;i34;A1;o35;A2;k36;r17;r20;#13;A2;i8;A4;k33;k16;r1;k284;A3;o18;i34;A1;o165;A2;k39;#1;A1;o23;Y12;000;#13;m5;RNLa;Ri5;pr17;2;Le;Ri3;A2;i8;A2;k37;A1;o23;o38;r1;A2;k37;r1;A1;o23;Y11;7ff;Lchanged;Ri29;m29;RNLchanged;Ri29;pr1;2;A4;k33;k16;r2;r23;A3;o18;i34;A2;o95;#14;A3;k286;#7;A2;k39;#6;o40;#14;#13;i30;").

Lemma rmprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (A + L <= 0x10000 \/ 0xf6000 <= A)%Z ->
  (0xf6000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMprotect A L P) (dec_mprotect A L))
       (epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr rsegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. ltac2:(Rpl.RP.run_k (rplG ()) 1 "S21;Y1;0;A1;o23;#0;Y6;00;A1;o23;#2;A2;k43;#1;#3;A2;i8;A2;k37;o40;r1;A2;k42;r1;#4;A2;k70;#1;#3;A2;k37;o40;#3;P~RA2;k42;o40;#1;P~R#7;A2;k42;o40;#4;A2;k37;o40;#1;LHa;R#9;L~Ri30;A3;k71;#1;#3;r2;PHa;R#9;P~Ri30;A2;k37;o40;#4;A1;o27;i72;A1;i73;i72;A1;i77;i3;A1;i79;i3;A2;o88;i3;o40;A2;o85;i3;o38;A7;o175;#15;k80;i81;i81;o82;A7;o83;#15;k80;i81;i81;o82;A4;o84;i3;#16;o86;#17;o89;A7;o83;#15;k80;i81;i81;o82;A4;o84;i3;#17;o200;A3;o177;i3;A2;o88;i3;#1;A1;o1;#2;o89;A2;k90;#15;o82;A4;k91;r1;r3;cvA2;o64;i29;o92;A3;i9;i29;A2;k93;r1;r3;o92;A3;k94;i3;o40;r2;Ly;Ri3;L~R#5;A6;k41;i3;A2;k270;r2;#4;Lz;Ri3;A3;i9;i3;r1;r3;A3;k327;r2;#4;E__sat1;R#6;#8;E__sat0;R#10;#11;E__arith;RL__x1;Ri3;E__wit;R#12;#13;E__varmap;RA2;o75;i3;r2;#14;E__ff;RA8;o78;#15;k80;i81;i81;o82;#18;A1;o14;i81;#18;#19;#20;P__x1;Ri3;P~R#5;A2;i8;A2;k37;o40;r2;A2;k42;r2;#4;A2;r1;r5;r4;A2;k271;r2;A1;k328;#3;A3;k329;r2;#3;E__sat1;R#6;#8;E__sat0;R#10;#11;E__arith;RE__wit;R#12;#13;E__varmap;RA1;o76;i3;#14;E__ff;RA7;o83;#15;k80;i81;i81;o82;A4;o84;i3;#16;o86;A2;o88;i3;#3;o89;#19;#20;#7;r1;").
Qed.

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop := ltac2:(Rpl.RP.run_k (rplG ()) 25 "S19;A1;o1;Y6;00;A1;i0;#0;Y2;1;Y5;00;A2;i19;i3;i3;Y3;0;P~R#1;A1;i4;A1;i0;A1;o1;#5;A1;k13;r41;A1;o14;#1;A1;k15;k16;A2;k22;#0;r40;A4;o20;i3;i3;A2;k21;#10;A1;o23;Y6;10;#10;A2;k24;A2;k22;#0;r38;A1;o25;Y7;24;Y2;0;A1;o27;#4;A3;k28;k16;r19;r1;A2;k31;k16;r1;A1;o27;i34;A4;k332;r42;r16;r23;r1;Lisnone;Ri29;Lra;R#1;Lsp;R#1;Lgp;R#1;Ltp;R#1;Ls0;R#1;Ls1;R#1;Ls2;R#1;Ls3;R#1;Ls4;R#1;Ls5;R#1;Ls6;R#1;Ls7;R#1;Ls8;R#1;Ls9;R#1;Ls10;R#1;Ls11;R#1;LF;RA2;k2;A1;o1;#2;#1;Lfc;RA1;i0;A1;o1;#3;Llen;Ri3;Lavoid;RA1;i73;#4;Lerrv;R#1;Llo;Ri3;Lm;R#6;La;Ri330;Lms';Ri6;m330;RNLa;Ri330;pr2;2;Le;Ri3;A2;i7;#1;Lt0;R#1;A2;i7;#1;Lt1;R#1;A2;i7;#1;Lt2;R#1;A2;i7;#1;La1;R#1;A2;i7;#1;La2;R#1;A2;i7;#1;La3;R#1;A2;i7;#1;La4;R#1;A2;i7;#1;La5;R#1;A2;i7;#1;La6;R#1;A2;i7;#1;La7;R#1;A2;i7;#1;Lt3;R#1;A2;i7;#1;Lt4;R#1;A2;i7;#1;Lt5;R#1;A2;i7;#1;Lt6;R#1;A2;i7;#6;Lm';R#6;A2;i8;A3;i9;i6;r17;A7;k10;A31;k11;r41;r40;r39;r38;r15;r14;r13;r37;r36;A2;k39;#0;A1;o25;o38;r12;r11;r10;r9;r8;r7;r6;r35;r34;r33;r32;r31;r30;r29;r28;r27;r26;r5;r4;r3;r2;r25;#7;r24;#8;r1;#9;A2;i8;A3;k17;A3;o18;#4;#11;A3;o18;#4;A4;o20;i3;i3;#12;A2;k24;#12;A1;o23;#13;#14;r19;r1;A2;i8;#15;A2;i8;#16;A2;i8;A4;k32;k16;r1;r20;#10;A2;i8;A4;k33;k16;r1;#12;A3;o18;i34;A1;o35;A2;k39;#0;A1;k331;r16;#17;A2;i8;A2;k37;A1;o23;o38;r16;A2;k37;r16;A1;o23;Y11;7ff;Lx;Ri3;A2;i7;#1;Lt0;R#1;A2;i7;#1;Lt1;R#1;A2;i7;#1;Lt2;R#1;A2;i7;#1;La1;R#1;A2;i7;#1;La2;R#1;A2;i7;#1;La3;R#1;A2;i7;#1;La4;R#1;A2;i7;#1;La5;R#1;A2;i7;#1;La6;R#1;A2;i7;#1;La7;R#1;A2;i7;#1;Lt3;R#1;A2;i7;#1;Lt4;R#1;A2;i7;#1;Lt5;R#1;A2;i7;#1;Lt6;R#1;A2;i7;#6;Lm2;R#6;A2;i8;A3;i9;i6;r17;A7;k10;A31;k11;r41;r40;r39;r38;r15;r14;r13;r37;r36;A2;k39;#0;r16;r12;r11;r10;r9;r8;r7;r6;r35;r34;r33;r32;r31;r30;r29;r28;r27;r26;r5;r4;r3;r2;r25;#7;r24;#8;#18;#9;A2;i8;A3;k17;A3;o18;#4;#11;#14;r19;r1;A2;i8;#15;A2;i8;#16;A2;i8;A4;k32;k16;#18;r20;#10;A2;i8;A4;k33;k16;r1;#12;A3;o18;i34;A1;o35;r21;#17;A3;i9;i29;A4;k333;vRUNp;r23;r22;r16;o92;").

Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose_ceil.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; exact D. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    pose_ceil. pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop := ltac2:(Rpl.RP.run_k (rplG ()) 26 "U10;A1;o1;Y6;00;A1;i0;#0;Y2;1;Y5;00;Y3;0;P~R#1;A1;i4;A1;i0;A1;o1;#4;A2;i19;i3;i3;A2;k22;#0;r41;A2;k24;A2;k22;#0;r39;A1;o25;Y7;24;Y2;0;LX;RtLR;RP~Rr1;P~R#1;P~Ri29;pLra;R#1;Lsp;R#1;Lgp;R#1;Ltp;R#1;Ls0;R#1;Ls1;R#1;Ls2;R#1;Ls3;R#1;Ls4;R#1;Ls5;R#1;Ls6;R#1;Ls7;R#1;Ls8;R#1;Ls9;R#1;Ls10;R#1;Ls11;R#1;LF;RA2;k2;A1;o1;#2;#1;Lfc;RA1;i0;A1;o1;#3;LA;Ri3;LL;Ri3;Lerrv;R#1;Llo;Ri3;Lm;R#5;La;Rr25;Lms';Ri6;A2;i7;#1;Lr;R#1;A2;i7;i29;Lu;Ri29;A2;i7;#1;Lt0;R#1;A2;i7;#1;Lt1;R#1;A2;i7;#1;Lt2;R#1;A2;i7;#1;La1;R#1;A2;i7;#1;La2;R#1;A2;i7;#1;La3;R#1;A2;i7;#1;La4;R#1;A2;i7;#1;La5;R#1;A2;i7;#1;La6;R#1;A2;i7;#1;La7;R#1;A2;i7;#1;Lt3;R#1;A2;i7;#1;Lt4;R#1;A2;i7;#1;Lt5;R#1;A2;i7;#1;Lt6;R#1;A2;i7;#5;Lm';R#5;A2;i8;A3;r43;r19;r17;r16;A2;i8;A3;i9;i6;r18;A7;k10;A31;k11;r42;r41;r40;r39;r15;r14;r13;r38;r37;A1;k234;r17;r12;r11;r10;r9;r8;r7;r6;r36;r35;r34;r33;r32;r31;r30;r29;r28;r27;r5;r4;r3;r2;r26;A1;k13;r42;r25;A1;o14;#1;r1;A1;k15;k16;A2;i8;A3;k17;A3;o18;#6;A4;o20;i3;i3;A2;k21;#7;A1;o23;Y6;20;#7;A3;o18;#6;A4;o20;i3;i3;#8;A2;k24;#8;A1;o23;#9;A3;o18;#6;A4;o20;i3;i3;r24;A2;k24;r24;A1;k26;r23;A1;o27;#6;r20;r1;A2;i8;P~RA3;i9;i29;r16;o130;A3;k28;k16;r21;r2;A2;i8;A2;k31;k16;r1;A2;i8;A4;k32;k16;r1;r21;#7;A4;k33;k16;r1;#8;A3;o18;i34;A1;o35;A2;k235;r17;r22;A1;o27;i34;").

Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 96)%Z -> (0xf6000 <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DEC ST ERR VML MI -> -> -> -> -> -> A0 LEN AL PR LO CEILJ SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  (* [comment removed for export] *)
  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step.
  (* [comment removed for export] *)
  step.
  call_sp rvmwait_spec; [exact ST | exact VML | exact MI | lia | lia | ].
  match goal with H : stk rsegs _ _ _ |- _ => rename H into ST end. match goal with H : rw_cells rsegs _ RVMLOCK _ |- _ => rename H into VML end. match goal with H : mem_inv rsegs _ |- _ => first [ rename H into MI | idtac ] end.
  do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; match goal with H : stk rsegs _ _ _ |- _ => first [ rename H into ST | idtac ] end; match goal with H : rw_cells rsegs _ (errno_addr _) _ |- _ => first [ rename H into ERR | idtac ] end.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv rsegs ?mm |- mem_inv rsegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk rsegs ?mm ?a ?b |- stk rsegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells rsegs ?mm ?a ?c |- rw_cells rsegs ?mm _ _ => exact H end.
Qed.
End CEIL_WRAP_1.

