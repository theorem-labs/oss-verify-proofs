(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed mc_6e4, mc_714, mc_71c and 21 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import TSTRW_tac.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @INV]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @memcpy_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @copied]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@Corelib; @Init; @Logic; @eq_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_ite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec0]; [@Corelib; @Init; @Datatypes; @reflect]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @ZArith; @BinInt; @Z; @nlt_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @window_ex]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @Arith; @PeanoNat; @Nat; @succ_inj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @mc_read1]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @ld_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@stdpp; @tactics; @f_equal_help]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @st_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @mc_store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @le1_zxb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @mc_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @upd_bytes]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_mod_any]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @copied_all]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @rw_cells_of_u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @land_1]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @land_bit_2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_a8c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_a60]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @land_bit_4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_a58]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_734]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_a0c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @land_bit_8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_a04]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @TSTRW_tac; @mc_read4]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @le4_lw]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_848]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_828]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_7f8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @window_sub]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srliw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_srliw]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @merge_r16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_72c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_978]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @lwb0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @lwb1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_770]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @merge_r8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_878]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @merge_r24]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @STRW_merge; @lwb2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_90c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_864]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_8e8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_754]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_740]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_7ec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_71c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_714]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @land_3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_of_rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @copied_0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @StrFun; @rw_cells_CB_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @Proofs; @mc_6e4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6TMemcpy_u5; @memcpy_body]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_bound]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Definition rsegs := Ubsan.Ubsan_loaded_segments.

Definition memcpy_entry := 0xbe048%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at rsegs m' (bv_unsigned a1) src.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
    munch W m m1 /\ wmono rsegs m m1.

  Ltac open_inv H := destruct H as (SRC & DST & CP & MU & WM).
  Ltac inv_tac :=
    lazymatch goal with
    | |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
        lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
          first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
    end.

  (* [comment removed for export] *)
  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe408 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_2 by lia.
    zstep. if_cases K2; zify_cond K2.
    -
      destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
      window P 2%nat HW.
      ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
      st1 HW 0%nat. st1 HW 1%nat.
      zstep. zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + zstep. fin.
      + window (P + 2)%Z 1%nat HW1.
        ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
      zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
      + zstep. fin.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe3dc m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 4%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe3d4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - use (mc_a60 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe388 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 8%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
    use (mc_a58 _ _ (P + 8)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe0b0 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a60 m1 bs P).
    - zstep. use (mc_a8c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe380 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_734 m1 bs P).
    - use (mc_a0c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe0a8 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a0c m1 bs P).
    - use (mc_734 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe2f4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 16%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
    ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
    ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
    zstep.
    st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
    zstep.
    st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
    zstep.
    use (mc_a04 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe1c4 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
      use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe1a4 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
    zstep. zstep. if_cases K8; zify_cond K8.
    - use (mc_848 m1 bs P (Z_to_bv 64 r)).
    - window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
      use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe174 m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
    window P 16%nat HW.
    ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
    zstep. zstep.
    st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
    - use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe168 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K16; zify_cond K16.
    - use (mc_828 m1 bs P (n - P)%Z).
    - zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

  (* [comment removed for export] *)
  Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
    xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe0ec m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 2)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
    st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe0d0 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
    xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe1f4 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 1)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
    st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe1e0 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    st HW 0%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep. zstep.
    use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
    xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe288 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 3)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
    st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe264 m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe0bc m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
    window P 4%nat HW. ld4 HW 0%nat q0.
    zstep. zstep. if_cases K3; zify_cond K3.
    - use (mc_864 m1 bs P q0). by_win HW 0%nat.
    - zstep. zstep. if_cases K2; zify_cond K2.
      + use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
      + use (mc_754 m1 bs P q0). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe098 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K32; zify_cond K32.
    - use (mc_740 m1 bs P).
    - zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_978 m1 bs P).
      + use (mc_72c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0xbe090 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_7ec m1 bs P).
    - use (mc_71c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    xa4 = Z_to_bv 64 (S + P + 1) ->
    evt rsegs POST (ST 0xbe060 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
  Proof using AB LEN SEP.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
    st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_714 _ _ (P + 1)%Z).
    - zstep. zstep. if_cases K1; zify_cond K1.
      + use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
      + zstep. use (mc_714 _ _ (P + 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_body : forall junk,
    rw_cells rsegs m D [CB (Z.to_nat n) junk] -> bytes_at rsegs m S src ->
    evt rsegs POST (ST 0xbe048 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
  Proof using AB LEN SEP.
    intros junk DST0 SRC.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
    change 0%nat with (Z.to_nat 0) in CP. clear DST0.
    zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
    -
      zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
      + use (mc_71c m junk 0%Z).
      + use (mc_7ec m junk 0%Z).
    - zstep. if_cases K0; zify_cond K0.
      + zstep. use (mc_714 m junk 0%Z).
      + zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
  Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at rsegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  evt rsegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbe048) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP.
  eapply memcpy_body; try eassumption.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.
