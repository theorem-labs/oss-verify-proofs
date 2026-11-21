(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed firstn4_le8, pop_arg_spec, va_area_bound and 2 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import F_memset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import F_extenddftf2.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @bool]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @T_DBL]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @hi64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @f128_of_d]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Datatypes; @option]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_memset; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @pop_arg_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @pop_arg_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @va_area]; [@Corelib; @Init; @Logic; @not]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@Corelib; @Init; @Logic; @eq_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64s]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64s_split]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Nat; @mul]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @mul]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_mul]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Lists; @List; @app_nil_r]; [@Stdlib; @Lists; @List; @firstn_0]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub_diag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @Lists; @List; @firstn_all2]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @Lists; @List; @firstn_app]; [@Stdlib; @Lists; @List; @app_nil_l]; [@Stdlib; @Lists; @List; @skipn_0]; [@Stdlib; @Lists; @List; @skipn_all2]; [@Stdlib; @Lists; @List; @skipn_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_ov_read]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @firstn4_le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64s_length]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @T_PTR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @T_INT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @T_UINT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @pop_arg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @va_area_bound]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @Lists; @List; @nth_error_Some]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_cells_image]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_bytes_b]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @bv_lit_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @va_read8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_pop_arg; @va_read4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@LinuxProcessSemantics; @Riscv; @Instr; @FLoad]; [@LinuxProcessSemantics; @Riscv; @Instr; @FMT_D]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_extenddftf2; @extenddftf2_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_extenddftf2; @extenddftf2_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @lo64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_extenddftf2; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @ivl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @freg_get_other]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @micromega; @Tauto; @NOT]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @freg_get_same]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Plain; @Plain_loaded_segments]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation rsegs := F_memset.rsegs.

Definition pop_arg_entry := 0xb0d30%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at rsegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_PTR)%Z then slot
  else if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Definition pop_arg_hi (ty : Z) (slot y : word) : word := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!1,2|600;!1+10$ty;R+0$slot;R1$y;R1-3RN$~R+31!2'4#3'52!2'60!1'7!1'8!2'90#2#1").

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 27 "S?0!1,2|600;!1+10|21;!1,22!2':31|500;|30;%~R1!1+<!1+1!1,26!2+I+0+0!2'90#\|40;!1,L:!2'K9;!1,L6!1,N+S$ra;R1$sp;R1$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R4$fc;R!1+1!1,25$ARG;R+0$AP;R+0$VA;R+0$slots;R!1+;1$i;R+0$ty;R+0$slot;R1$y;R1$m;R7$ms';R+=!2+>1$t0;R1!2+>1$t1;R1!2+>1$t2;R1!2+>1$a0;R1!2+>1$a1;R1!2+>1$a2;R1!2+>1$a3;R1!2+>1$a4;R1!2+>1$a5;R1!2+>1$a6;R1!2+>1$a7;R1!2+>1$t3;R1!2+>1$t4;R1!2+>1$t5;R1!2+>1$t6;R1!2+>4$Ft;R4!2+>7$m';R7!2+?!3+@+=#B!7'A!O'B#^0#\#[#Z#A#@#?#Y#X#>#=#<#;#:#9#8#7#W#V#U#T#S#R#Q#P#O#N#6#5#4#3#2!1'C#^0#L!1,D1#1!1'E'F!2+?!3'G!3,H8!4,J+0+0<9!3,H8!4,J+0+0#J!2'M#J=!3,H8!4,J+0+0#K!2'M#K;!1,N8#C#1!2+?!3'O'F#C#1!2+?!2'P'F#1!2+?!4'Q'F#1<9!2+?!4'R'F#1#J!3,H+S!1,T!2'60!2'M#I!2'U=!2'M#G!1,L,V>!2+?!4'R'F#1#K!3,H+S!1,T!2'W#F#E!3,H+S!1,T!3'X#F#E#D>!2+?!3'Y#1#I#H%k;R!1+13%~R!1'Z!3+@+0!2'93#1!1,L|32;!3+@1!2'[#4#2!2'[#O#2").

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma va_read8 : forall m VA slots (i : Z) w a,
  bytes_at rsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma va_read4 : forall m VA slots (i : Z) w a,
  bytes_at rsegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes rsegs m a 4 = Some (le4 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma pop_arg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells rsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells rsegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk rsegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb0d30) fc None m (seg_rom rsegs)).
Proof.
  intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
  -
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  -
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  -
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  -
    zstep. zstep. zstep. if_lit. do 7 zstep.
    carve_frame 16%nat ST.
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep.
    zstep. call extenddftf2_spec. 1:{ exact MI. }
    cbv delta [F_extenddftf2.rsegs] in *. fold rsegs in *.
    rewrite freg_get_same by reflexivity.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
    { intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed.
