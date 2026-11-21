(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed rmmap_anon_spec, rmmap_fixed_spec, rmprotect_spec and 1 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ITree Nodes SysStep Decode.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_mm_syscalls.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import F_syscalls RF_vm_wait RMallocRep.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @mmap_len]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @impl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @node]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @at_node]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @Exc; @exc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @range_ans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @enode]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @NMunmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_munmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @epost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @rmunmap_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmunmap_entry]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_mm_syscalls; @mmap_len_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @impl_enode]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @resp]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ITree; @nret]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @stk_lo_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Corelib; @Numbers; @BinNums; @N]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_vm_wait; @rvmwait_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_vm_wait; @rvmwait_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @micromega; @Tauto; @NOT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @evt_ecall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MSsvc]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @areg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_munmap_Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @efferr]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @mkEffectU]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @MemCopy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @eff0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @RgErr]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @errno_ret]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @apply_writes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @apply_zeros]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @apply_unmaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @sysret_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @sysret_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @sysret_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @sysret_errno]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @errno_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @errno_of_errno_ret]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @apply_mem_none]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @nret_MSsvc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @RgDone]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @rw_cells_unmaps_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @stk_unmaps_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @munch_unmaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @mem_inv_unmaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @errno_of_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @apply_mem_unmaps]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_mm_syscalls; @land_m4096]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RPAGE_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @NMprotect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mprotect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @rmprotect_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmprotect_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @rmprotect_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mprotect_Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_mm_syscalls; @mmap_len_aligned]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @ref_ro_addr_false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @ro_addr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @rw_cells_zeros_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @stk_zeros]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @munch_zeros]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @wmono_zeros]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @mem_inv_zeros]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @rw_cells_zeros_new]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Lists; @ListDef; @repeat]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @apply_mem_zeros]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @mmap_ans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Nodes; @NMmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mmap_none]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @rmmap_anon_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmmap_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @mmap_addr_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mmap_none_Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @MmErr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @MmOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @dec_mmap_Some]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @unsigned_errno_ret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @mmap_addr_ok_true]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Decode; @avoids]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @unsigned_lit_land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @land_ones64]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_mm_syscalls; @CEIL_WRAP_1; @rmmap_fixed_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_mm_syscalls; @fixed_shape]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lxor]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @wview]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_eq_0_iff]].

Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.

Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m RVMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 64)%Z -> (0xfb000 <= lo)%Z ->
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_R0!1,?|<000;!3+C+4!2'c0#20,A!2'F,A#4|10;!1,?3|600;!1,?5!2'H46!1,15!2'@8#7!2'789!1,?|^B7ffffffffffff000;!1+08!2'@8#1!2'@8#8!3+C<=>!2'9#8#7|;7ff;!1,?A!2'9@B!2'78!2'@8!2'c1!2'78!2'@8C;!2'78=!2'@8!2'c1#1;!2'78F!2'9!2'9#7#6B!2'@8!2'c1#8;!2'J#7!2'c0#70!2'c0#80!2'@8!2'J#8K!3'c2#70#3!2'F,A0%~RN!2'F,AK!2'^A46%~R!2'E,A4%~R!2'F,A6!2'E,A7!2'F,A4$Ha;RR$~R+^B!3'^C46#2%Ha;RR%~R+^B!2'F,A7!3'c2#90#5%~RN!2'F,A!2'c0#:0!1,>+^D!1+^E+^D!2,^G+4#3!1,^H+4!4,^F+4Y#2Z!1+^I+4!1+^K+4!2,^U+4,A!2,^U+40!1,Y+^M!2,^Q+43!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S^4,^V!2,^Q+4,^R!2'^W^0,^N!4'^X#1#3vv!2,^;+^Y,^Z!3+C+^Y!2'^[#1#3,^Z!3'^\+4,A#2!2'F,A#3!3+C+40,A!1'aO^:!2'9#9#8!2'9^<B!2'c0^=0!2'E,A0!2'9#:#9!2'9^@B!2'c0^A0!2'E0,A!2'9!2'9#;#:B!2'c0^D0!2'9!2'9#<#;B!2'9!2'9#=#<B!2'c0#A0!2'c0#B0!2'c0#G0!2'c0#H0!2,aL+4!1,:,^R}7!2,a2+4^M}6!2,a2+4^O}3!2,a2+4^Q}2!2,a2+4^S}1!2,a2+4^U!2,a2+4,a3}4!3,a1+4^V^W!6,aP^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^2,_:^1,^V|30;!2,^Q+4|21;|23;|20;!2,^Q+4_1|11;!2,^Q+4_3!3,_9+4^6^4!3,_9+4_5!2,^U+4B%~R^:+a7%~R_7!3+C+4#3!2'9!2'c40#9#6!2'9#7#8!2'@8#:!2'@8#9!3+C<_:_:!2'78_:!2'J^<#9!1'@8!2'c2^A0%~R!2'F,A^A%~RN!2'F,A!2'c0^F0!3'c2#<0#8%~RN!2'F,A!2'c0#=0!2'9#1#2!3,`Y+4!2,^U+448!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S^6,^V$__x2;R+4$__x1;R+4&__wit;R!3,;+^D!2,a0!3,a1+4^R!3,a1+4^T^W,a4WX&__varmap;R!4,^F+4!4,^F+4Y#3Z#2Z\&__ff;R!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4!3,_9+4!3,_9+4^6_2^2,^S_E,^V^3!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S_2,^V^3!8,^J^0'^L+^M+^M,^N_F^3!7,`W^0'^L+^M+^M,^N_F!7,^O^0'^L+^M+^M,^N!4,^P+4^6,aC_E,^V^7^8!2'F!2'9_D07%__x2;R+4%__x1;R+4%~R_H%~R^9%~R^9!2+I2!2'E#47!5#1#>#?#9#:#;!3,;+^D!2,a0!3,a1+4^T^Y,a4W!7,^O^0'^L+^M+^M,^N!4,^P+4!3,_9+4_5^2,^S_E,^V!2'9#4#5!2'9_MB!5#1#;#<#6#7#8&__sat4;RMO&__sat3;RPQ&__sat2;RST&__sat1;RUV&__arith;R$__x2;R+4$__x1;R+4&__wit;R_KX&__varmap;R[\&__ff;R!8,^J^0'^L+^M+^M,^N_L^3!8,^J^0'^L+^M+^M,^N^5^3!8,^J^0'^L+^M+^M,^N_F^3!7,`W^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S_6,^V!7,^O^0'^L+^M+^M,^N!4,^P+4_6,aC_E,^V^7^8%__x2;R+4%__x1;R+4%~R_H%~R^9%~R^9!2+I!2'F,A_N!2'E_N7_O&__sat4;RMO&__sat3;RPQ&__sat2;RST&__sat1;RUV&__arith;R_G_I_O$A;R+4$L;R+4$HA;R1$HL;R1$A0;R2$L0;R2$B;R!2'F!2'9!2'9#6#507!6'D+4!2'c1:;$z;R+4!2+I?!3+C<!2'@8!2'JDE9!6'D+4#7$z;R+4!2+I!3+C<F>!3+C<!2'@8!2'JDG9!6'D+4H$z;R+4!2+I!3+C<I>!3+C<!2'@8!2'JG!2'78I9!6'D+4J$z;R+4!2+I?!3+C<!2'@8!2'J!2'78!2'@8!2'c1C;E9!6'D+4!2'JH!2'c0H0$z;R+4!2+I!3+C<L>!3+C<!2'@8!2'JE!2'78L9&E1;R&__sat4;RMO&__sat3;RPQ&__sat2;RST&__sat1;RUV&__arith;R$__x2;R+4$__x1;R+4&__wit;RWX&__varmap;R[\&__ff;R!8,^J^0'^L+^M+^M,^N!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S^2,^V^3^5^3!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^4,_:^1,^V^3!7,^O^0'^L+^M+^M,^N!4,^P+4!3,^T+4^6^4,_:^6,^V^7^8%__x2;R+4%__x1;R+4%~R%~RN^9%~R!3+C+4#3,A!3+C+4!2'J#3#4#3!4#1!2'c0#<0#<#5#:!3+C+4J#7&E2;R&H;R!2'c3C0%~R^;!3+C+4^=!2'9!2'c40!2'c5^=0^>&H0;R!2'c6^=0%~R^?!2+I!2'F,A^B!2'E^B0&H1;R!2'c7^A0%~R^C!2+I!2'E0^E!2'F^E,A&H2;R!2'c8^D0%~R^:!3+C+4!2'c5^F0,A&H3;R!2'c9^F0%~R^:!3+C+4!2'c0^G0^G&q;R!2'c5^G0+4&r;R!2'c0!2'9!2'9#>#=B0+4&H4;R!2'c3#?0%~R^;!3+C+4#@!2'9!2'c40!2'c5#@0!2'c0#@0&H5;R!2'c6#@0%~R^?!2+I!2'F,A^H!2'E^H0&H6;R!2'c7#A0%~R^C!2+I!2'E0^I!2'F^I,A&H7;R!2'c8#B0%~R^:!3+C+4!2'c5#C0,A&H8;R!2'c9#C0%~R^:!3+C+4!2'c0#D0#D&q0;R!2'c5#D0+4&r0;R!2'c0#E0+4&H9;R!2'c3#E0%~R^;!3+C+4#F!2'9!2'c40!2'c5#F0!2'c0#F0&H10;R!2'c6#F0%~R^?!2+I!2'F,A^J!2'E^J0&H11;R!2'c7#G0%~R^C!2+I!2'E0^K!2'F^K,A&H12;R!2'c8#H0%~R^:!3+C+4!2'c5#I0,A&H13;R!2'c9#I0%~R^:!3+C+4!2'c0#J0#J&q1;R!2'c5#J0+4&r1;R!2'c0#K0+4&__sat15;RPQ&__sat14;RST&__arith;R$__x8;R+4$__x7;R+4$__x6;R+4$__x5;R+4$__x4;R+4$__x3;R+4$__x2;R+4$__x1;R+4&__wit;R!3,;+^D!2,c:!3,a1+4!3,aK+4^L^N!3,a1+4!3,aK+4^L^P!3,a1+4^R!3,a1+4^T!3,a1+4!3,aK+4^L^V^W!2,c:!3,a1+4!2,a2+4}8!3,a1+4^N!3,a1+4^P!3,a1+4!3,aK+4^L!2,a2+4^X!3,a1+4!3,aK+4^L^R^T!2,a0^Y,a4WX&__varmap;R!4,^F+4!4,^F+4!4,^F+4!2,^G+4#9#5Z#3!2,^G+4#7#2!4,^F+4!2,^G+4#6#4!2,^G+4#8\&__ff;R!8,^J^0'^L+^M+^M,^N!8,^J^0'^L+^M+^M,^N^Z^3!7,^O^0'^L+^M+^M,^N!4,^P+4^4,_:!3,_9+4!3,c;+4^2!2,^Q+4^[^\,^V^3!8,^J^0'^L+^M+^M,^N!8,^J^0'^L+^M+^M,^N^Z^3!7,^O^0'^L+^M+^M,^N!4,^P+4^6,_:!3,_9+4!3,c;+4^2!2,^Q+4_0_2,^V^3!8,^J^0'^L+^M+^M,^N!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,aC^2,^V^3!7,`W^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S_4,^V!7,^O^0'^L+^M+^M,^N!4,^P+4_4,aC^2,^V^3!8,^J^0'^L+^M+^M,^N!8,^J^0'^L+^M+^M,^N^Z^3!7,^O^0'^L+^M+^M,^N!4,^P+4_6,_:!3,_9+4!3,c;+4^2!2,^Q+4|22;_4,^V^3!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4!3,^T+4^6_2,_:^6,^V^3!8,^J^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^\,_:^1,^V^3!7,^O^0'^L+^M+^M,^N!4,^P+4!3,^T+4_6_4,_:_5,^V^7^8%__x8;R+4%__x7;R+4%__x6;R+4%__x5;R+4%__x4;R+4%__x3;R+4%__x2;R+4%__x1;R+4%~R_8%~R_8%~R%~R^?!2+I!2'F,A#6!2'E#60%~R%~R_7!3+C+4!2'9!2'9#5#6B!2'9!2'c40#:#7%~R!3+C+4!2'J#5#8#5%~R!3+C+4#:,A!3+C+4!2'J!2'9_9B#9_9!>#1#5#<#C#4#;#B#O#P#:#A#G#H#I#M!3+C+4!2'JC!2'c0C0@!6'D+4#9$z;R+4!2+I!3+C<=_:!3+C<!2'@8!2'J!2'78!2'@8!2'J^A^BE_;!6'D+4^<$z;R+4!2+I_<!3+C<!2'@8!2'JE_=_;!6'D+4^<$z;R+4!2+I_<!3+C<!2'@8!2'J#1_=_;!6'D+4#9$z;R+4!2+I_<!3+C<!2'@8!2'J^@#1_;!4,_>!3+C<_;_;!3+C<!2'@8_>>!2,^;<_;!8'`A+4<_?_?_>#8!2,^;%~R+4<_?&__sat7;RUV&__sat6;R_@_A&__sat5;RPQ&__sat4;RST&__sat3;R_B_C&__arith;R$__x2;R+4$__x1;R+4&__wit;RWX&__varmap;R[\&__ff;R!7,^O^0'^L+^M+^M,^N!4,^P+4!3,^T+4_5^6,_:^4,^V^7^8%__x2;R+4%__x1;R+4!3+C+4!2'J_D#1#2!2#1#>#?!2'78_;!2'a@#9&__sat7;RUV&__sat6;R_@_A&__sat5;RPQ&__sat4;RST&__sat3;R_B_C&__arith;R_G_I_J!2'78!2'@8^<!2'a@^<&__sat7;RUV&__sat6;R_@_A&__sat5;RPQ&__sat4;RST&__sat3;R_B_C&__arith;R$__x2;R+4$__x1;R+4&__wit;R_KX&__varmap;R[\&__ff;R!8,^J^0'^L+^M+^M,^N_L^3!8,^J^0'^L+^M+^M,^N^5^3!8,^J^0'^L+^M+^M,^N_F^3!7,`W^0'^L+^M+^M,^N!7,^O^0'^L+^M+^M,^N!4,^P+4^1,^S_5,^V!7,^O^0'^L+^M+^M,^N!4,^P+4_5,aC_E,^V^7^8%__x2;R+4%__x1;R+4%~R_H%~R^9%~R^9!2+I!2'F,A_M!2'E_M7_J!2'J^=^>#1!2'J#9!2'c0#90#2!2'c1H;!2'c<H_P!2'c1#7;!2'c<#7_Q!2'78!2'@8H!2'a@H_P:!2'a@#7_Q!2'c1;:!2'c=;:").
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells rsegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z
       | RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

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
  (A + L <= 0x10000 \/ 0xfb000 <= A)%Z ->
  (0xfb000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 1 "SE0|10;!1,?0|600;!1,?2!2'H13!2+I!2'F,A#1!2'E#14!2'^A13!2'F,A3%~R!2'E,A1%~R7!2'E,A4!2'F,A1$Ha;R9$~R+^B!3'^C13#2%Ha;R9%~R+^B!2'F,A4!1,>+^D!1+^E+^D!1+^I+4!1+^K+4!2,^U+4,A!2,^Q+4,^R!7,`W?'^L+^M+^M,^N!7,^O?'^L+^M+^M,^N!4,^P+4@,^SA,^V!7,^O?'^L+^M+^M,^N!4,^P+4A,aC!3,`Y+4!2,^U+41!1,12,^V!2'^W?,^N!4'^X#1#3vv!2,^;+^Y,^Z!3+C+^Y!2'^[#1#3,^Z!3'^\+4,A#2$y;R+4$~R5!6'D+4!2'c0#24$z;R+4!3+C+4#1#3!3'd<#24&__sat1;R68&__sat0;R:;&__arith;R$__x1;R+4&__wit;R<=&__varmap;R!2,^G+4#2>&__ff;R!8,^J?'^L+^M+^M,^NB!1,Y+^MBCD%__x1;R+4%~R5!2+I!2'F,A#2!2'E#24!2#1#5#4!2'c1#2!1'd=3!3'd>#23&__sat1;R68&__sat0;R:;&__arith;R&__wit;R<=&__varmap;R!1,^H+4>&__ff;R!7,^O?'^L+^M+^M,^N!4,^P+4@,^S!2,^U+43,^VCD7#1").
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2
        /\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono rsegs m m')
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

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
  (lo <= bv_unsigned sp - 96)%Z -> (0xfb000 <= lo)%Z ->
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

