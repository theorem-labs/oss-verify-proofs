(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @cons]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @eq]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @swrap32_small]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_remuw]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @SP0]; [@Corelib; @Init; @Datatypes; @option]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @rsegs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @DG_W]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Corelib; @Init; @Logic; @or]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_post]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@Corelib; @Init; @Logic; @eq_sym]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_mem]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_ret]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_ret']; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @or_introl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_xori]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @b2z_lor01]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_read]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @le1_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_weed2]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @Lists; @List; @nth_error_None]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_weed1]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_rw2_loop]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @sx32_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srl]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_l]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_gt_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @gt]; [@Stdlib; @micromega; @RingMicromega; @OpGt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_l2exit]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Corelib; @Init; @Logic; @False_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_mod64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_rw1_loop]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_divuw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul32]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_DIVU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_divuw]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_REMU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_remuw]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_rw1_entry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_loop2]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_0_l]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_1_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @v_remuw_small]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg_r]; [@Stdlib; @micromega; @Tauto; @TT]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MULHU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mulhu]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mulhu]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_l1_k1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_mod_any]; [@Stdlib; @micromega; @RingMicromega; @PsatzLet]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_l1_k2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @bv_eqb_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_var]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_lower_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgBaseU; @DG; @dg_l1_k3]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_1_l]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_shl_shr]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := Ubsan.Ubsan_loaded_segments.

Lemma le1_lit : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|30;!1,40!1+31!1+22|600;!1,44!2'65#1!2'756!2'617!2'61#1!1,82%~R33!1,52!1+3#1!1+3#2%~R!3+<!1+3#3#2#1!3+<+0!2'7#4#3!2'7#4#2%~R!3+<+0!2'7#3#2!2'7#3#1!3+<!1+3#4#3#2!2'75!2'65#2!2'61A!2'61#2!2'71!2'61#3!2'?5#2!2'?1#2|10;!1,BG!2'AH!1,B4!2'AH!1,B0!2'AH!1,B|518;!3,529:$v;R+0vdvd!8'133!2,528!2,529::!8'12;<<89!2,9%~R2;<&H;R$n;R+:$b1;R=$b2;R>!5';?@%~R!3+<+0!2'7#3#2!2'7#3#1!3+<!1+3#4#3#2$~R?$~R%~R!3+<+0!2'7#4#3!2'7#4#2!3+<!1+3#5#4#3#1!3'=#3#2#1%n;R+:%b1;R=%b2;R>@!4#11BC!6'>+0!2'?1A$z;R+0!3+<+0#1D!6'>+0E$z;R+0!3+<+0!2'?1#1D!6'>+0F$z;R+0!3+<+0!2'?1!2'?5#3#1vd!4'@#2IJ!4,C+0$z;R+0!3+<+0I!2'D#1JK!2,9+0!2'DKJ!3+<+0!2'?1EF!2'71C!2'E1#2A!2'E5#2!2'71B!2'E1A!2,93:!3+<3!2'F}17L!3+<3!1'G6L").
Qed.

Lemma sx32_small : forall k, (- 2 ^ 31 <= k < 2 ^ 31)%Z -> sx32 (Z_to_bv 64 k) = Z_to_bv 64 k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^@0|10;!1,B0|4f;!1,B2!2'A13!2+H!2'I!1'J4#1!2'K#14|600;!1,46!1+37!1'67|500;!1,4:!2'67#2!2'77<!2'?7#2!2'A1!1,B6!2'M#2?!1,B:!2'A1A!2'M@B!2'M4B!2'N#34!2'MEB!2'M#2B!2'M!2'NGDB!2'M#3?!2'N#24!2'MJB!2'P1A!2'K,Q1%~R!2'I,QA!2'K,QB%~RMN!2'I,Q1$Ha;RP$~R+R!3'S1A#2%Ha;RP%~R+R!2'I,QB!2'P13%~R!2'I,Q3!2'K,Q4%~RMT$Ha;RP$~R+R!3'S13#2%Ha;RP%~R+R!2'I,Q4vd!2,9+T!2'U,Q1M!1#2X!1#5X!1,8+V!1+2+V!1+X+0!1+Z+0!2,^4+01!3,^3+0^2;!2,^4+0,Q!2'^7^1,^0!4'^8#1#3vv!2,9+^9,^:!3+<+^9!2'^;#1#3,^:!3'^<+0,Q#2&__sat3;RLO&__sat2;RQR&__sat1;RSU&__sat0;RVW&__sat1;RYT&__sat3;RZN&__arith;R&__wit;R[\&__varmap;R!1,W+0^0&__ff;R!6,Y^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0^3,^5^4,^6^5^6%~R!3+<+0B,Q+^=#1!2'M!2'N@4B$z;R+0!3+<+0!2'^?#14#4!2,^@+0#2!2,^C+0,^D!3,^3+0^2!1,42!3,^B+0^;^<!2'A1!1'^L;!2'^M^>1$k;R+0$Hk;R5vd!8'1+0899!2'L;=#2!2,9%~R+089!6'>+0>$z;R+0!3+<+0!2'L;#1#3vdvd&H;R!6'>+0!2'M!2'NCDB$z;R+0!3+<+0F#1!6'>+0H$z;R+0!3+<+0#1!2'M!2'N!2'MIBDB!6'>+0G$z;R+0!3+<+0!2'M!2'N!2'M#3BDB!2'M!2'N#1DB!2,9+0HC!4'@#2?B!4,C+0$z;R+0!3+<+0?!2'D#1BB!2,9+0!2'DBBK!4'O#24B^7^8!4'O@4B^7!3+<+0K^8!6'^>+0F^9!6'>+0E^9&__sat1;RSU&__sat0;RVW&__sat1;RYT&__arith;R$__x1;R+0&__wit;R[\&__varmap;R^:^0&__ff;R!7,^1^1'[+\+\,^0!4,^2+0!3,^A+0^=^<,^5^;,^6^5^6%__x1;R+0!3+<+0!2'^?!2'N#144#1!1#1#7F!3'^EEB&__sat3;RLO&__sat2;RQR&__sat1;RSU&__sat0;RVW&__sat1;RYT&__sat3;RZN&__arith;R$__x1;R+0&__wit;R[\&__varmap;R^:^0&__ff;R!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0!2,^H+0^<,^I^;,^6!7,^1^1'[+\+\,^0!4,^2+0^;,^J^<,^6!1,^K+\!7,^G^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0^4,^I^=,^6!7,^1^1'[+\+\,^0!4,^2+0^=,^J^3,^6^5^6%__x1;R+0%~R5!2+H!2'I,QJ!2'KJB!2#1#:#9!2'M!2'NI4B#1!3+<+0!2'^?!2'M!2'N!2'M#2!2'A1!1'^L7^?^>^?#2!3+<+0!2'L;>#2=!2'E7#2!3+<8!1'^N<<").
Qed.

Lemma swrap32_small : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SR0|10;!1,B0|4f;!1,B2!2'A13!2+H!2'I!1'J4#1!2'K#14!2'N#24!2'P13!2'K,Q1%~R!2'I,Q3!2'K,Q4%~R89!2'I,Q1$Ha;R;$~R+R!3'S13#2%Ha;R;%~R+R!2'I,Q4vd!2,9+T!2'U,Q18!1#2>!1,8+V!1+2+V!2,^@+0#2!1+X+0!1+Z+0!2,^C+0,^D!2,^4+01!3,^3+0F!1,42!3,^B+0EG!2'^7D,^0!4'^8#1#3vv!2,9+^9,^:!3+<+^9!2'^;#1#3,^:!3'^<+0,Q#2|500;!1,BK!2'A1L%~R!2'I,QL!2'K,QM!1,4K!2'A1!1'^LO!2'^MP1$x;R+0$Hx;R5vdvd!6'>+06$z;R+0!3+<+0!2'^?#14#3&__sat1;R7:&__sat0;R<=&__sat1;R?9&__arith;R$__x1;R+0&__wit;R@A&__varmap;RBC&__ff;R!7,^1D'[+\+\,^0!4,^2+0!3,^A+0HG,^5E,^6IJ%__x1;R+0!3+<+0!2'^?!2'N#144#1!1#1#6!2'M6M!3'^E6M&__sat3;R!2'P1L%~R8N&__sat2;R$Ha;R;$~R+R!3'S1L#2%Ha;R;%~R+R!2'I,QM&__sat1;R7:&__sat0;R<=&__sat1;R?9&__sat3;R!1#5>N&__arith;R$__x1;R+0&__wit;R@A&__varmap;RBC&__ff;R!8,^FD'[+\+\,^0!7,^GD'[+\+\,^0!7,^1D'[+\+\,^0!4,^2+0!2,^H+0G,^IE,^6!7,^1D'[+\+\,^0!4,^2+0E,^JG,^6!1,^K+\!7,^GD'[+\+\,^0!7,^1D'[+\+\,^0!4,^2+0!2,^4+0,Q,^IH,^6!7,^1D'[+\+\,^0!4,^2+0H,^J!3,^3+0FO,^6IJ%__x1;R+0%~R5!2+H!2'I,Q6!2'K6M!2#1#9#8!3+<+0!2'^?!2'M!2'N#2QPQ#2!3+<+0!2'LO#2#2").
Qed.

Lemma v_remuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z -> v_remuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`C0!2'I,Q#2|10;!1,B1|4f;!1,B3!2'A24!2'K#25!1,B,^D!2'I7#2|600;!1,49!1+3:|500;!1,4<!2'?=#1!2'7:!2'6:#5!2'6:!2'M#5#4!2'?:#4!2'?=A!1,B9!2'A2C!2'M#4D$z;R+0!3+<+0#1#5!2,9+0#4!2'P2C!2'K,Q2!2'K,QD%~R!2'I,QCJ%~RIK!2'I,Q2$Ha;RM$~R+R!3'S2C#2!2'I,QD%Ha;RM%~R+RO!2'P24%~R!2'I,Q4!2'K,Q5%~RIR$Ha;RM$~R+R!3'S24#2!2'I,Q5%Ha;RM%~R+RUvd!2,9+T!2'U,Q2I!1#2W!1#5W!1,8+V!1+2+V!2,^@+0#2!1+X+0!1+Z+0!2,^4+0,Q!2,^C+0,^D!7,^1^1'[+\+\,^0!4,^2+0^2,^I^3,^6!2,^4+02!3,^3+0^5!1,43!7,^1^1'[+\+\,^0!4,^2+0^3,^J^6,^6!1,^K+\!3,^3+0^5:!7,^1^1'[+\+\,^0!4,^2+0^3,^J^9,^6!7,^G^1'[+\+\,^0^4^:!2'^7^1,^0!4'^8#1#3vv!2,9+^9,^:!3+<+^9!2'^;#1#3,^:!3'^<+0,Q#2!2'I,Q#1!2'K#15!2+H0!2'K#2D!2#1#;#9!1,B<!2'A2^B!2'ME^C!2'P2^B%~R!2'I,Q^B!2'K,Q^C%~RI^F$Ha;RM$~R+R!3'S2^B#2!2'I,Q^C%Ha;RM%~R+R^I!2'^P#:D!2'I,Q#:!2'M#<D%~R^L%~RO!2'I,Q^M!2'^Q#;D!3+<+0D,Q%~R!1'^R^P!3+<+0#<!2'N!2'DD!2'^M#<D^M!2'^S#<D!2'M#=D%~RJ!2+H!2'I,Q^S!2'K^SD!2'^T#=D!2'M#>D%~R!2'KD,Q!2+H!2'KD^V!2'I^V,Q!2'^U#>D%~R^P!3+<+0!2'^M#?D,Q!2'^V#?D%~R^P!3+<+0!2'M#@D#@!2'^X#@Dvd,^W^\!1#5vd!2,9+T!2'U,QDJ!2'M#AD!2'I,Q_2!2+H_3!2'K_2D$a;RM!2#;#1#2%a;RMU!1#<W$a;RM!2#@#1#2%a;RMO!1#AW$a;RM!2#E#1#2%a;RM^I!1#FW!2,^[+0}5}4!2,^[+0_?}2!2,^[+0_A!2,^[+0,_2}1!3,5+V!2,^Y!3,^Z+0_>!3,^Z+0_@_B!2,^\!3,^Z+0!3,_0+0!2,_1+0!1,B|^C0000000000000000;_C!3,^Z+0!3,_3+0!2,_4+0!1,_5,^D_>!3,^Z+0_B!2,^[+0_D,_6Z!2,^@+0#4!1,W+0!4,_7+0_F#3_G!6,_8^1'[+\+\,^0#6!7,^G^1'[+\+\,^0_I^:!6,Y^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0^9,^5^2,^6!2,^C+01|20;!7,^1^1'[+\+\,^0!4,^2+0^2,^I_L,^6!8,^F^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0^2,^I^9,^6^8^4!7,^G^1'[+\+\,^0^4!7,^1^1'[+\+\,^0!4,^2+0^3,^J!3,^3+0^5=,^6!2+H#4!2'K#1D%~R%~R^P+^=!3+<+0#4!2'N!2'DD#5#3!2'I,Q#4!2'I,Q#5%~R_S%~RO_T!2'K#55!2+H_T!2'K#5^C!2'M#LD!8#1!2'I,Q_X!2'^M#LD#L_X#;#A#B#J!2+H_3!2'K_2^C!3+<+0!2'M!2'M#4!2'A2!1'^L:!2'A2!1'^L=#4!3+<+0B#4!2,^4+07!7,^1^1'[+\+\,^0!4,^2+0`0,^I^3,^6!2'I7#1|11;!2,^C+0`3!7,^G^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0`0,^I`4,^6!7,^1^1'[+\+\,^0!4,^2+0`4,^J^6,^6!2'?=!2'?:#6!2'6:!2'L=!2'?:#7!2'6:!2'M#7#6!2'M#:#9!2'L=`9!3+<+0#7,Q!3+<+0#8,Q!6,_8^1'[+\+\,^0#4!1'6:!2'I,Q#;!2'K#45!2'6:#4!2'6:#3$x;R+0$y;R+0$Hx;R!2+H06$Hy;R!2+H86vd!6'>+0!2'?:#3$z;R+0!3+<;-^9RN$~R+^9;!2'^O>,Q2!2'6:!2'L=?!2'6:!2'L=!2'M!2'?=?>@!6'>+0A$z;R+0!3+<;-^9RN$~R+^9;!2'^OB,Q2!2'6:!2'L=#1!2'6:!2'L=!2'M>B@&Wx;Rvdvd!6'>+0EF!6'>+0#4FGE!3'^E#4D&__sat3;RHL&__sat2;RNP&__sat1;RQS&__sat0;RTV&__sat1;RXR&__sat3;RYK&__arith;R$__x1;R+0&__wit;RZ[&__varmap;R\^0&__ff;R!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0^4^7^8^;^<^=%__x1;R+0%~R!2+H^>^?^@^A^D!3'^EE^C&__sat6;R^E^G&__sat5;R^H^J&__sat4;RHL&__sat3;RNP&__sat2;RQS&__sat1;RTV&__sat0;R^K^N&H;R^O^Q&H0;R^R^T&H1;R^U^W&H2;R^X^Y&H3;R^Z^[&H4;R_0^\vd&H0;R_1_4&zh;R#2+R&__sat1;R_5_6&__sat2;R_7R&zh;R#5+R&__sat3;R_8_9&__sat4;R_:K&zh;R#8+R&__sat5;R_;_<&__sat6;R_=^F&__arith;R$__p1;Rw$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R_E[&__varmap;R!4,_7+0_H#2_G^0&__ff;R!8,^F^1'[+\+\,^0_J^8!8,^F^1'[+\+\,^0!8,^F^1'[+\+\,^0_K^8!7,^1^1'[+\+\,^0!4,^2+0_L,^5!3,^B+0!3,_9+0^9!2,^C+0_M^3,^6^8!8,^F^1'[+\+\,^0!8,^F^1'[+\+\,^0_N^8_O^8!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0_N!7,^1^1'[+\+\,^0!4,^2+0_L,^J^6,^6^8_P^<^=%__p1;Rw%__x3;R+0%__x2;R+0%__x1;R+0%~R_Q%~R_R%~R_U%~R!2+H_T_V_W_Y_Z_[_\_\&Wy;Rvdvd!6'>+0EF!6'>+0#4FGE!3'^E#4D&__sat3;RHL&__sat2;RNP&__sat1;RQS&__sat0;RTV&__sat1;RXR&__sat3;RYK&__arith;R$__x1;R+0&__wit;RZ[&__varmap;R\^0&__ff;R!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0`1^7^8^;^<^=%__x1;R+0%~R!2+H`2^?^@^A^D!3'^EE^C&__sat6;R^E^G&__sat5;R^H^J&__sat4;RHL&__sat3;RNP&__sat2;RQS&__sat1;RTV&__sat0;R^K^N&H;R^O^Q&H0;R^R^T&H1;R^U^W&H2;R^X^Y&H3;R^Z^[&H4;R_0^\vd&H0;R_1_4&zh;R#2+R&__sat1;R_5_6&__sat2;R_7R&zh;R#5+R&__sat3;R_8_9&__sat4;R_:K&zh;R#8+R&__sat5;R_;_<&__sat6;R_=^F&__arith;R$__p1;Rw$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R_E[&__varmap;R!4,_7+0_G#2_H^0&__ff;R!8,^F^1'[+\+\,^0_J^8!8,^F^1'[+\+\,^0!8,^F^1'[+\+\,^0_K^8!7,^1^1'[+\+\,^0!4,^2+0`4,^5!3,^B+0!3,_9+0^9!2,^C+0|21;^3,^6^8!8,^F^1'[+\+\,^0!8,^F^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0^2,^I`4,^6^8_O^8!8,^F^1'[+\+\,^0`5^8_P^<^=%__p1;Rw%__x3;R+0%__x2;R+0%__x1;R+0%~R_Q%~R_R%~R_U%~R!2+H!2'I7#5_V_W_Y_Z_[_\_\!6'>+0#6$z;R+0!3+<;-^9RN$~R+^9;!2'^O`6,Q2`7!2'6:!2'L=!2'M#1`6`8!6'>+0#5$z;R+0!3+<;-^9RN$~R+^9;!2'^O#1,Q2`7!2'6:!2'L=!2'M#7#1`8&r;R!2'_:#5,Q!2+_;!3+<+0#5,Q!2'^O#5,Q&b;R!2'^O#6,Q+^9-_;RN$b;R+^9$r;R!2+_;!3+<+0#8,Q#1!3+<;-^9RN$~R+^9;#22!2'6:!2'L=!2'?:#:!2'6:`:!2'6:`9#22$e;R`;!1$E;R`<&__sat2;R!2'^P#:#9%~R^L%~R^L!2'I,Q!2'M#<#;&__sat1;RQS&__sat0;RTV&__sat1;RXR&__arith;R$__p2;Rw$__p1;Rw$__x1;R+0&__wit;RZ[&__varmap;R!4,_7+0\#2_G^0&__ff;R!8,^F^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0_L,^5^2,^6^8!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0`0,^I_L,^6`=^8!6,_8^1'[+\+\,^0#5^<^=%__p2;Rw%__p1;Rw%__x1;R+0%~R!3+<+0#1,Q%~R!2+H8#3#5!5#1!3+<;!2'6:!2'L=!2'?:#?!2'6:!2'M#?#>!2'K#>5#>#6#<#1$n;R!1'^R`;!1$E;R!1'^R`<!8'1+0;`>`>`:`9!2,9%~R+0;`>!2'_<`9&H;R!3'^S#:#9&__sat1;RQS&__sat0;RTV&__sat1;RXR&__arith;R$__p1;Rw$__x1;R+0&__wit;RZ[&__varmap;R\^0&__ff;R!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0`1`=^8!7,^1^1'[+\+\,^0!4,^2+0^2,^J^3,^6^<^=%__p1;Rw%__x1;R+0%~R!2+H`2#2!2'K,Q#2!3#1!2'K#=5#=#;!2+H!2'I,Q`9!2'K`9#9&__sat2;R!2'^P#;#:%~R`?%~R`?!2'I,Q!2'M#=#<&__sat1;RQS&__sat0;RTV&__sat1;RXR&__arith;R$__p1;Rw$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R!3,5+V!2,^\!3,^Z+0_@!3,^Z+0_B_C,_6Z[&__varmap;R!4,_7+0!2,^@+0#3#2_F^0&__ff;R!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0^4!7,^1^1'[+\+\,^0!4,^2+0^3,^J`4,^6^8!8,^F^1'[+\+\,^0`5^8!8,^F^1'[+\+\,^0!7,^G^1'[+\+\,^0_N_I^8!7,^G^1'[+\+\,^0!7,^1^1'[+\+\,^0!4,^2+0!2,^H+0^6,^I^3,^6^7^<^=%__p1;Rw%__x3;R+0%__x2;R+0%__x1;R+0%~R!2+H^>!2'K#1#3%~R!2+H!2'I7#4`@%~R!2+H_S#6!2+H!2'I!1'J5#4`@!7#1!2'K#@5#?#@!2'M#@#?#6#=#>#1!2'?=!2'?:#5#1`6#2!2'7:`A!2'E:#4!2'7:`B!2'E:#3!3+<;!2'_=`A`B!2'6:!2'M#4#3").
Qed.


Lemma sgn_small64 : forall x, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.
Lemma lxor63 : forall x, (0 <= x < 2 ^ 63)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof.
  intros x Hx. change 9223372036854775808%Z with (2 ^ 63)%Z.
  rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n) as [<-|Hne]; [|apply andb_false_r].
  rewrite andb_true_r. destruct (Z.eq_dec x 0) as [->|Hx0]; [reflexivity|].
  apply Z.bits_above_log2; [lia|]. apply (proj1 (Z.log2_lt_pow2 x 63 ltac:(lia))). lia.
Qed.
Lemma swrap32_modl : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616 + y) = (x + y)%Z.
Proof.
  intros x y H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
  rewrite (Z.mod_eq x 18446744073709551616) by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616) + y + 2147483648)%Z
    with ((x + y + 2147483648) + (- (4294967296 * (x / 18446744073709551616))) * 4294967296)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Definition dg_idx (A k : Z) : Prop := True.
Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 (z mod 18446744073709551616) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. apply Z.mod_mod. lia.
Qed.
Lemma land3_mod4 : forall k, Z.land k 3 = (k mod 4)%Z.
Proof. intros k. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land7_mod8 : forall k, Z.land k 7 = (k mod 8)%Z.
Proof. intros k. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma v_divuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z. rewrite !(Z.mod_small _ 4294967296) by lia.
  destruct (Z.eqb_spec y 0) as [->|Hy0]; [lia|].
  rewrite swrap32_small; [reflexivity|]. pose proof (Z.div_pos x y ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound x y x ltac:(lia) ltac:(nia)). lia.
Qed.
Ltac dg_u8fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m _ _) _) =>
    rewrite ?le1_lit;
    lazymatch goal with
    | H : u8arr rsegs m ?A ?xs |- context [write_to_mem m (Z_to_bv 64 (?A + ?k)) [?b]] =>
        let BU' := fresh "BU" in
        pose proof (u8arr_write rsegs m A xs k b H ltac:(rewrite ?upd_length; lia)) as BU'; clear H; store_done
    | H : u8arr rsegs m ?A ?xs |- context [write_to_mem m (wa (?A + ?k)) [?b]] =>
        let BU' := fresh "BU" in
        pose proof (u8arr_write rsegs m A xs k b H ltac:(rewrite ?upd_length; lia)) as BU'; clear H; store_done
    end
  | _ => idtac
  end.
Ltac dg_divfacts :=
  repeat match goal with |- context [Z.div ?x ?c] =>
    lazymatch goal with
    | _ : (c * (x / c) <= x)%Z |- _ => fail
    | _ => pose proof (Z.mul_div_le x c ltac:(lia)); pose proof (Z.mul_succ_div_gt x c ltac:(lia))
    end
  end.
Ltac dg_divfacts_in K :=
  repeat match type of K with context [Z.div ?x ?c] =>
    lazymatch goal with
    | _ : (c * (x / c) <= x)%Z |- _ => fail
    | _ => pose proof (Z.mul_div_le x c ltac:(lia)); pose proof (Z.mul_succ_div_gt x c ltac:(lia))
    end
  end.
Definition dg_cheap_mode : Prop := True.
Ltac dg_nonlin x := match x with
  | context [Z.mul ?a ?b] =>
      lazymatch a with Zpos _ => fail | Zneg _ => fail | Z0 => fail | _ =>
      lazymatch b with Zpos _ => fail | Zneg _ => fail | Z0 => fail | _ => idtac end end
  | context [bv_unsigned ?w] => is_var w
  end.
Ltac dg_cheap_ok x := lazymatch goal with
  | _ : dg_cheap_mode |- _ => tryif dg_nonlin x then fail else idtac
  | _ => idtac
  end.
Ltac dg_lia := lia.
Ltac dg_norm :=
  rewrite ?Z.add_0_r;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  dg_divfacts;
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by dg_lia end;
  repeat match goal with |- context [v_divuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_divuw_small x y) by dg_lia end;
  repeat match goal with |- context [v_remuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_remuw_small x y) by dg_lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl x y) by dg_lia end;
  repeat match goal with |- context [bv_swrap 32 ?x] => dg_cheap_ok x; rewrite (swrap32_small x) by dg_lia end;
  repeat match goal with |- context [Z.modulo ?x 18446744073709551616] => dg_cheap_ok x; rewrite (Z.mod_small x 18446744073709551616) by dg_lia end;
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) by dg_lia end;
  repeat match goal with |- context [Z.ltb ?a ?b] => dg_cheap_ok a; dg_cheap_ok b;
    first [ rewrite (proj2 (Z.ltb_lt a b)) by dg_lia | rewrite (proj2 (Z.ltb_ge a b)) by dg_lia ] end;
  cbn [Z.b2z]; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r.
Ltac dg_hs := lazymatch goal with
  | IDX : dg_idx ?A ?k |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with H : u8arr rsegs m A ?xs |- _ =>
      assert (store_ok rsegs m (wa (A + k)) 1 = true)
        by (apply (u8arr_store_ok rsegs m A xs k); [exact H | rewrite ?upd_length; lia | reflexivity])
    end
  end.
Ltac dg_rd := lazymatch goal with
  | IDX : dg_idx ?A ?k |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with H : u8arr rsegs m A ?xs |- _ =>
      let b := fresh "b" in let NB := fresh "NB" in
      destruct (nth_error xs (Z.to_nat k)) as [b|] eqn:NB;
      [ pose proof (u8arr_read rsegs m A xs k b _ H NB ltac:(lia) eq_refl)
      | exfalso; apply nth_error_None in NB; rewrite ?upd_length in NB; lia ]
    end
  end.
Ltac dg_norm_cheap :=
  rewrite ?Z.add_0_r;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by dg_lia end;
  repeat match goal with |- context [v_divuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_divuw_small x y) by dg_lia end;
  repeat match goal with |- context [v_remuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_remuw_small x y) by dg_lia end.
Ltac dg_xstep := first [ zstep; dg_u8fix; dg_norm | if_true | if_false | dg_hs; zstep; dg_u8fix; dg_norm
                       | dg_rd; zstep; dg_u8fix; dg_norm ].
Ltac dg_inl x l := lazymatch l with cons ?y ?r => first [constr_eq x y | dg_inl x r] | nil => fail end.
Ltac dg_at l := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?x) _ _ _ _) => dg_inl x l end.
Ltac dg_run l := repeat (tryif dg_at l then fail else dg_xstep).
Ltac dg_swrap_in K :=
  unfold bv_swrap, bv_wrap in K;
  try change (bv_half_modulus 32%N) with 2147483648%Z in K; try change (bv_modulus 32%N) with 4294967296%Z in K;
  try change (bv_half_modulus 64%N) with 9223372036854775808%Z in K; try change (bv_modulus 64%N) with 18446744073709551616%Z in K.
Ltac dg_prune K := exfalso; rewrite ?land3_mod4, ?land7_mod8 in K; dg_divfacts_in K;
  repeat match type of K with context [bv_signed (Z_to_bv 64 ?x)] =>
    rewrite (sgn_small64 x) in K by dg_lia end;
  first [ lia | lazymatch type of K with context [bv_swrap] => (dg_swrap_in K; Z.div_mod_to_equations; lia) end ].
Ltac dg_solve d l :=
  lazymatch d with
  | O => fail 100 "dg_solve: out of fuel"
  | S ?d' =>
    dg_run l; dg_norm;
    tryif dg_at l then idtac
    else lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "K" in if_cases K; zify_cond K;
        [ first [ dg_prune K | dg_solve d' l ] | first [ dg_prune K | dg_solve d' l ] ]
    end
  end.

Ltac dg_conjs := repeat (lazymatch goal with |- _ /\ _ => split end).
Ltac dg_exs := repeat (lazymatch goal with |- ex _ => eexists end).
Ltac dg_b01 := repeat (match goal with |- context [Z.b2z ?b] => lazymatch b with true => fail | false => fail | _ => destruct b end end);
  first [ left; vm_compute; reflexivity | right; vm_compute; reflexivity | lia ].
Ltac dg_reg n := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
  let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
  let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
  lazymatch v with Some ?w => w end end.
Ltac dg_fold_R := lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      lazymatch R with
      | TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) => change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
      end
  end.
Lemma land_m1 : forall a s c, (0 <= s)%Z -> c = (2 ^ s - 1)%Z -> Z.land a c = (a mod 2 ^ s)%Z.
Proof. intros a s c Hs ->. rewrite <- Z.land_ones by exact Hs. f_equal. rewrite Z.ones_equiv. lia. Qed.
Ltac l2_landfacts :=
  match goal with |- context [Z.land (?x * 10) ?c] =>
    first [ rewrite !(land_m1 (x * 10) 56 c ltac:(lia) ltac:(reflexivity)) in *
          | rewrite !(land_m1 (x * 10) 57 c ltac:(lia) ltac:(reflexivity)) in *
          | rewrite !(land_m1 (x * 10) 58 c ltac:(lia) ltac:(reflexivity)) in *
          | rewrite !(land_m1 (x * 10) 59 c ltac:(lia) ltac:(reflexivity)) in * ]
  end;
  match goal with |- context [(?y mod (2 ^ ?S))%Z] => pose proof (Z.mod_pos_bound y (2 ^ S) ltac:(lia)) as LMB end.
Section DG.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Definition SP0 : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'7!1,4|600;/sp;").
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis LENR : (4096 <= lenp /\ lenp + 4 <= 2^47)%Z.
Hypothesis KPR : (4096 <= kp /\ kp + 4 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 64 \/ SP0 + 8 <= buf)%Z.
Hypothesis SEP_L : (lenp + 4 <= SP0 - 64 \/ SP0 + 8 <= lenp)%Z.
Hypothesis SEP_K : (kp + 4 <= SP0 - 64 \/ SP0 + 8 <= kp)%Z.
Hypothesis SEP_BL : (buf + 21 <= lenp \/ lenp + 4 <= buf)%Z.
Hypothesis SEP_BK : (buf + 21 <= kp \/ kp + 4 <= buf)%Z.
Hypothesis SEP_LK : (lenp + 4 <= kp \/ kp + 4 <= lenp)%Z.
Hypothesis LA : (lenp mod 4 = 0)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Definition DG_W : list (Z * Z) := [(SP0 - 64, SP0); (buf, buf + 21); (lenp, lenp + 4); (kp, kp + 4)]%Z.

Definition dg_post (Ks : Z) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (res len kappa : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch DG_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (SP0 - 64) SP0
    /\ u8arr rsegs m' buf bs /\ length bs = 21%nat
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (Ks + kappa))] /\ (-18 <= kappa <= 2)%Z
    /\ (res = 0 \/ res = 1)%Z.

Definition dg_mem (m : word -> option byte) (len Kv : Z) (bs : list byte) : Prop :=
  stk rsegs m (SP0 - 64) (SP0 - 64) /\
  rw_cells rsegs m (SP0 - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  munch DG_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  u8arr rsegs m buf bs /\ length bs = 21%nat /\
  rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] /\ rw_cells rsegs m kp [C4 (Z_to_bv 64 Kv)].
Ltac dg_mem_tac := unfold dg_mem, DG_W; dg_conjs; try eassumption; try (rewrite ?upd_length; assumption).

Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DG_W in MU.

Lemma dg_ret' : forall (res len kappa Ks : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' (m : word -> option byte) (bs : list byte),
  dg_mem m len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z -> (res = 0 \/ res = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 64)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                                  s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0x450ec) fc None m (seg_rom rsegs)).
Proof using BUFR LENR KPR SPR0 SEP_B SEP_L SEP_K SEP_BL SEP_BK SEP_LK LA KA.
  intros res len kappa Ks t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' t3' t4' t5' t6' m bs DM Hlen Hk Hres.
  destruct DM as (ST & FR & MU & WM & MI & BU & BL & LE & KC). unfold DG_W in MU. unfold SP0 in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  repeat dg_xstep.
  release_frame FR ST (bv_unsigned sp).
  assert (ESP : (bv_unsigned sp - 64 + 64 = bv_unsigned sp)%Z) by lia. rewrite ESP, Z_to_bv_bv_unsigned.
  apply evt_done. unfold dg_post, SP0. dg_exs. split; [reflexivity|].
  dg_conjs; try eassumption; lia.
Qed.

End DG.
