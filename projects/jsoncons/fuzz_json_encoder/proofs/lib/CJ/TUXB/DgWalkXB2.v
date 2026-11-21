(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed dg_loop2, dg_rw1_entry. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXB Require Import DgWalkXB.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_mem]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @SP0]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DG_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sh_read]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@Corelib; @Init; @Datatypes; @prod]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@Corelib; @Init; @Datatypes; @pair]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @swrap32_small]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sgn_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_byte]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slti]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slti]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lxor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @lxor63]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @le1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @swrap32_modl]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_l]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_gt_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @gt]; [@Stdlib; @micromega; @RingMicromega; @OpGt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_l2exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slti_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sx32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srl]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_shiftr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @land3_0]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @Tauto; @NOT]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addw]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_mod64]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_weed1]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_rw1_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slt_b2z]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB2.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Local Notation SP0 := (DgWalkXB.SP0 sp).
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 96 \/ lenp + 4 <= buf)%Z.
Local Notation app_buf := (DgWalkXB.app_buf buf).
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 96)%Z.
Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Local Notation DG_W := (DgWalkXB.DG_W sp buf lenp kp).
Local Notation dg_post := (DgWalkXB.dg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp).
Local Notation dg_mem := (DgWalkXB.dg_mem ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m0 buf lenp kp).
Local Notation L x := (x ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 buf lenp kp BUFR SPR0 KL KS KA SEP_B APP_B APP_S SHL SHK SHBUF).
Local Notation sh_read := (L DgWalkXB.sh_read).
Local Notation dg_weed1 := (L DgWalkXB.dg_weed1).
Local Notation dg_rw1_loop := (L DgWalkXB.dg_rw1_loop).
Local Notation dg_l2exit := (L DgWalkXB.dg_l2exit).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkXB.DG_W in MU.

(* [comment removed for export] *)
Lemma dg_loop2 : forall (n : nat) (i p2 D s len Ks : Z) t2' t4' s0' a2' s3' s4' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m j8 len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (D <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= D)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' s0' (Z_to_bv 64 10)
                                  (Z_to_bv 64 kp) (Z_to_bv 64 (10 ^ i)) a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 (- i)) s3' s4' s5' s6' s7' s8' s9' s10 s11 (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xcc330) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i p2 D s len Ks t2' t4' s0' a2' s3' s4' s5' s6' s7' s8' s9' m j8 bs Hn HM LR IR KsR Hs HP HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  assert (H10 : (1 <= 10 ^ i < 2 ^ 58)%Z) by (pose proof (Z.pow_pos_nonneg 10 i ltac:(lia) ltac:(lia)); lia).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  set (dd := ((p2 * 10) ≫ (s mod 64))%Z).
  assert (Hdd : (0 <= dd < 10)%Z).
  { unfold dd. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }

  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 D) (Z_to_bv 64 10)
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 (- i)) (Z_to_bv 64 dd) (Z_to_bv 64 dd) s5' s6' s7' s8' s9' s10 s11
              (Z_to_bv 64 s) (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 (p2 * 10)) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xcc358) fc None m (seg_rom rsegs))).
  { intros a1x.
    zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (dd + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
    rewrite (swrap32_small (dd + 48)) by lia.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    zstep. zstep. if_cases Kl; [zify_cond Kl; rewrite (swrap32_small (len + 1)) in Kl by lia; rewrite !sgn_small in Kl by lia; lia | ].
    rewrite (swrap32_small (len + 1)) by lia.
    zstep; zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHl.
    zstep. zstep. zstep.
    zstep. if_cases Kn; [zify_cond Kn; ub_norm_in Kn; lia | ].
    do 4 zstep. zstep. if_cases Kp; [zify_cond Kp; ub_norm_in Kp; cbv in Kp; discriminate | ].
    zstep. if_cases Kb; [zify_cond Kb; lia | ].
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DgWalkXB.DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 3 zstep. zstep. if_cases K0d; [cbv in K0d; discriminate | ].
    clear SHb.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (dch := (dd + 48)%Z).
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 dch))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 dch])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 dch) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 dch)))
      by (unfold DgWalkXB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
          split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
    zstep. zstep. if_cases Kk; [zify_cond Kk; rewrite (swrap32_modl (- i) (-1)) in Kk by lia; rewrite !sgn_small in Kk by lia; lia | ].
    rewrite (swrap32_modl (- i) (-1)) by lia.
    do 5 zstep.
    assert (HLm : (Z.land (p2 * 10) (2 ^ s - 1) < 2 ^ s)%Z)
      by (replace (2 ^ s - 1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
    assert (HL0 : (0 <= Z.land (p2 * 10) (2 ^ s - 1))%Z) by (apply Z.land_nonneg; lia).
    if_cases K3; zify_cond K3.
    -
      assert (Hi1 : (i + 1 <= 17)%Z).
      { destruct (Z_le_gt_dec (i + 1) 17) as [?|Hg]; [lia|]. assert (H18 : (10 ^ 18 <= 10 ^ (i + 1))%Z) by (apply Z.pow_le_mono_r; lia).
        rewrite Z.pow_add_r in * by lia. lia. }
      replace (Z_to_bv 64 (10 ^ i * 10)) with (Z_to_bv 64 (10 ^ (i + 1))) by (f_equal; rewrite Z.pow_add_r by lia; lia).
      replace (Z_to_bv 64 (- i + -1)) with (Z_to_bv 64 (- (i + 1))) by (f_equal; lia).
      eapply (IH (Z.to_nat (17 - (i + 1)))); [lia | reflexivity | exact HM2 | lia | lia | lia | lia | lia | rewrite Z.pow_add_r by lia; lia].
    -
      zstep.
      replace (Z_to_bv 64 (D * 10)) with (Z_to_bv 64 (10 * D)) by (f_equal; lia).
      eapply dg_l2exit; [exact HM2 | lia | lia | lia | lia | lia | lia]. }
  do 6 zstep.
  replace (bv_swrap 32 ((p2 * 10) ≫ (s mod 64) + 0)) with dd by (unfold dd in *; rewrite Z.add_0_r; symmetry; apply swrap32_small; lia).
  fold dd.
  if_cases K1.
  - apply BODY.
  - zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2; [lia | ].
    apply BODY.
Qed.

(* [comment removed for export] *)
Lemma dg_rw1_entry : forall (D r dv cnt s len Ks : Z) t2' t4' t5' t6' a1' a2' a4' s2' s3' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 3)%Z -> (2 <= cnt <= 4)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (56 <= s <= 59)%Z -> (0 <= r < D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 dv) (Z_to_bv 64 cnt)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) a4' (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11 (Z_to_bv 64 s) t4' t5' t6')
                              F (Z_to_bv 64 0xcc240) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hdv Hs Hr HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  zstep. if_cases Kz; [zify_cond Kz; lia | ].
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 kp KA) in Ka; lia | ].
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  zstep. rewrite sx32_small by lia.
  zstep. rewrite (swrap32_small (cnt + -2)) by lia.
  zstep. zstep. zstep. if_cases Kov; [zify_cond Kov; rewrite (swrap32_modl Ks (cnt + -2)) in Kov by lia; exfalso; exact (Kov eq_refl) | ].
  zstep. zstep. if_cases K0b; [cbv in K0b; discriminate | ].
  clear SHk.
  zstep.
  assert (KC' : rw_cells rsegs m1 kp [C4 (Z_to_bv 64 (Ks + (cnt - 2)))]) by (replace (Ks + (cnt - 2))%Z with (Ks + (cnt + -2))%Z by lia; exact KC).
  assert (HM1 : dg_mem m1 j8 len (Ks + (cnt - 2)) bs).
  { unfold DgWalkXB.dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC']. }
  zstep.
  set (tk := ((dv ≪ (s mod 64)) mod 2 ^ 64)%Z).
  assert (Htk : (1 <= tk < 2 ^ 64)%Z).
  { assert (Hc : (s = 56 \/ s = 57 \/ s = 58 \/ s = 59)%Z) by lia. unfold tk.
    destruct Hdv as [-> | [-> | ->]]; destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence. }
  replace (Z_to_bv 64 (dv ≪ (s mod 64))) with (Z_to_bv 64 tk) by (unfold tk; apply Z_to_bv_mod64).
  do 3 zstep. if_cases K1.
  - zstep. eapply dg_weed1; [exact HM1 | lia | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed1; [exact HM1 | lia | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DgWalkXB.DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 14 zstep.
      rewrite (swrap32_small (len + -1)) by lia.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      eapply (dg_rw1_loop (Z.to_nat (D - r)) D r tk len); [reflexivity | exact HM1 | lia | lia | lia | lia | | lia].
      revert K2; unfold tk; rewrite ?Z.mod_small by lia; intros K2; lia.
Qed.

End DGB2.
