(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed dg_l1_k3, dg_spec, negmod64 and 3 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/CJ/TUB/DgSpecB.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 57-106, 111-119, 124-125, 139-199. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXB Require Import DgWalkXB DgWalkXB2 DgL1XB.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_mem]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @SP0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DG_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @dg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sh_read]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@Corelib; @Init; @Datatypes; @prod]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@Corelib; @Init; @Datatypes; @pair]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_divuw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul32]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_DIVU]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_divuw]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @swrap32_small]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sgn_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_byte]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slti]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slti]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lxor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @lxor63]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @le1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB2; @dg_rw1_entry]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MULHU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mulhu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mulhu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgL1XB; @dg_l1_k2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @shl_s]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @subw_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzLet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slti_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sx32_small]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_0_l]; [@Stdlib; @ZArith; @BinInt; @Z; @div_small]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @v_divuw_small]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @ro_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @bv_eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @land3_0]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_l]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_var]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells_frame]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_lower_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgSpecXB; @DGB4; @dg_l1_k3]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_1_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgSpecXB; @DGB4; @zbv_sub64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgSpecXB; @DGB4; @swrap32_sub64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgSpecXB; @DGB4; @negmod64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgSpecXB; @DGB4; @swrap32_neg]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DGB4.
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
Local Notation dg_loop2 := (L DgWalkXB2.dg_loop2).
Local Notation dg_rw1_entry := (L DgWalkXB2.dg_rw1_entry).
Local Notation dg_l1_k2 := (L DgL1XB.dg_l1_k2).
Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DgWalkXB.DG_W in MU.

(* [comment removed for export] *)
Lemma dg_l1_k3 : forall (p1 len p2 D s Wp1 Ks : Z) t2' t4' a1' a2' s4' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (0 <= len <= 0)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (0 <= p1 < 256)%Z -> (0 <= p2 < 2 ^ s)%Z -> (2 <= D < 2 ^ 64)%Z ->
  (len = 0 -> p1 * 2 ^ s + p2 = Wp1 /\ D <= Wp1 /\ 8 <= p1)%Z -> (p1 * 2 ^ s + p2 < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 100) (Z_to_bv 64 4)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 1) (Z_to_bv 64 p1) s4' (Z_to_bv 64 (0xcccccccd * 2 ^ 32)) s6' s7' s8' s9' s10 s11
                                  (Z_to_bv 64 s) t4' (Z_to_bv 64 p2) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xcc170) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KsR Hs Hp1 Hp2 HD Hinv HX.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound p1 100 ltac:(lia)) as Hpm.
  assert (Hprod : (0 <= p1 mod 100 * 2 ^ s <= p1 * 2 ^ s)%Z)
    by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; [lia | apply Z.mod_le; lia]]).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.
  zstep. rewrite Z.add_0_r, swrap32_small by lia.
  zstep. rewrite v_divuw_small by lia.
  zstep. if_cases K1; zify_cond K1;
    [ | zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2; [ | lia] ].
  2:
     destruct (Hinv ltac:(lia)) as (Hw & HDw & H8);
     do 4 zstep; rewrite (Z.div_small p1 100), Z.mul_0_l, Z.sub_0_r, swrap32_small, shl_s by lia;
     zstep; if_cases K3; zify_cond K3; [lia | ];
     do 5 zstep; if_cases K4; zify_cond K4; [ | lia];
     eapply (dg_l1_k2 p1 len p2 D s Wp1 Ks); [exact HM0 | lia | lia | lia | lia | lia | lia | intros _; lia].

  zstep. zstep. if_cases Kd; [zify_cond Kd; rewrite (swrap32_small (p1 / 100 + 48)) in Kd by lia; rewrite !sgn_small in Kd by lia; lia | ].
  rewrite (swrap32_small (p1 / 100 + 48)) by lia.
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
  replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 (p1 / 100 + 48)))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 (p1 / 100 + 48)])
    by (f_equal; symmetry; apply le1_lit).
  pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 (p1 / 100 + 48)) BU ltac:(lia)) as BU'.
  clear BU; store_done.
  assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 (p1 / 100 + 48))))
    by (unfold DgWalkXB.dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
        split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
  do 4 zstep.
  rewrite subw_mod, shl_s by lia.
  zstep; if_cases K3; zify_cond K3.
  - eapply (dg_rw1_entry D (p1 mod 100 * 2 ^ s + p2) 100 4 s (len + 1) Ks); [exact HM2 | lia | lia | lia | right; right; reflexivity | lia | lia | lia].
  - do 5 zstep.
    if_cases K4; zify_cond K4; [ | lia].
    eapply (dg_l1_k2 (p1 mod 100) (len + 1) p2 D s Wp1 Ks); [exact HM2 | lia | lia | lia | lia | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma swrap32_neg : forall s, (0 < s <= 2 ^ 31)%Z -> bv_swrap 32 (4294967296 - s + 0) = (- s)%Z.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (4294967296 - s + 0 + 2 ^ 31)%Z with ((2 ^ 31 - s) + 1 * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma negmod64 : forall s, (0 < s < 2 ^ 64)%Z -> ((- s) mod 18446744073709551616 = 18446744073709551616 - s)%Z.
Proof. intros s H. rewrite <- (Z.mod_add (- s) 1) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma swrap32_sub64 : forall s, (- 2 ^ 31 <= s < 2 ^ 31)%Z -> bv_swrap 32 (s - 18446744073709551616) = s.
Proof.
  intros s H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace (s - 18446744073709551616 + 2 ^ 31)%Z with ((s + 2 ^ 31) + (- 4294967296) * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zbv_sub64 : forall x, Z_to_bv 64 (x - 18446744073709551616) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  replace (x - 18446744073709551616)%Z with (x + (-1) * 18446744073709551616)%Z by lia. apply Z.mod_add. lia.
Qed.

(* [comment removed for export] *)
Lemma dg_spec : forall t0 t1 t2 t3 t4 t5 t6 (m : word -> option byte) (Wm dW dP s Ks : Z) (bs : list byte) lj,
  (56 <= s <= 59)%Z -> (1 <= Wm)%Z -> (0 <= dW)%Z -> (0 <= dP)%Z -> (Wm + dW + dP <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wm + dW + dP + 1)%Z ->
  (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  stk rsegs m (SP0 - 96) SP0 -> rw_cells rsegs m SP0 [C8 (Z_to_bv 64 kp)] ->
  u8arr rsegs m buf bs -> length bs = 21%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 Ks)] ->
  ro_cells rsegs m 0x164518 [C8 (Z_to_bv 64 0x16d7b8)] -> ro_cells rsegs m 0x16d7b8 [C8 (Z_to_bv 64 2147450880)] ->
  mem_inv rsegs m -> m = m0 ->
  evt rsegs (dg_post Ks) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (Wm + dW)) (Z_to_bv 64 (2 ^ 32 - s))
                                  (Z_to_bv 64 (Wm + dW + dP)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0xcc090) fc None m (seg_rom rsegs)).
Proof using All.
  intros until lj. intros Hs HWm HdW HdP Hsum HWp HKs ST KPc BU BL LE KC GOT SHV MI ->.
  pose proof (munch_refl DG_W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (munch_refl [((SP0 - 96)%Z, SP0)] m0) as MUf. pose proof (wmono_refl rsegs m0) as WMf.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).

  assert (BOX : rw_cells rsegs m0 SP0 [C8 (Z_to_bv 64 kp)] /\ u8arr rsegs m0 buf bs /\ rw_cells rsegs m0 lenp [C4 lj] /\ rw_cells rsegs m0 kp [C4 (Z_to_bv 64 Ks)] /\
                ro_cells rsegs m0 0x164518 [C8 (Z_to_bv 64 0x16d7b8)] /\ ro_cells rsegs m0 0x16d7b8 [C8 (Z_to_bv 64 2147450880)])
    by exact (conj KPc (conj BU (conj LE (conj KC (conj GOT SHV))))).
  clear KPc BU LE KC GOT SHV.
  unfold DgWalkXB.DG_W in MU. unfold DgWalkXB.SP0 in *.
  carve_frame 96%nat ST.
  do 12 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct BOX as (KPc0 & BU0 & LE0 & KC0 & GOT0 & SHV0);
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ KPc0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as KPc;
    pose proof (u8arr_transport rsegs _ m0 mm _ _ BU0 MUf WMf ltac:(cbn [disjoint_from]; rewrite BL; cbn; lia)) as BU;
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ LE0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as LE;
    pose proof (rw_cells_transport rsegs _ m0 mm _ _ KC0 MUf WMf ltac:(cbn [disjoint_from]; cbn; lia)) as KC;
    pose proof (ro_cells_transport rsegs _ m0 mm _ _ GOT0 MUf ltac:(cbn [disjoint_from]; cbn; lia)) as GOT;
    pose proof (ro_cells_transport rsegs _ m0 mm _ _ SHV0 MUf ltac:(cbn [disjoint_from]; cbn; lia)) as SHV;
    clear KPc0 BU0 LE0 KC0 GOT0 SHV0
  end.
  clear MUf WMf.
  do 3 zstep. if_cases K0; [rewrite bv_eqb_refl in K0; discriminate | ].
  do 2 zstep. if_cases K1; zify_cond K1; [lia | ].
  do 2 zstep. if_cases K0b; [rewrite bv_eqb_refl in K0b; discriminate | ].
  zstep. if_cases K2; zify_cond K2; [lia | ].
  rewrite (swrap32_neg s) by lia.
  zstep. zstep. rewrite ?(negmod64 s) by lia.
  replace (0 - (18446744073709551616 - s))%Z with (s - 18446744073709551616)%Z by lia.
  rewrite ?(swrap32_sub64 s) by lia.
  zstep. if_cases Kng; [zify_cond Kng; rewrite <- (Z.mod_add (s - 18446744073709551616) 1) in Kng by lia; rewrite Z.mod_small in Kng by lia; lia | ].
  rewrite zbv_sub64.
  zstep. rewrite (swrap32_small (s + 0)) by lia. rewrite Z.add_0_r.
  zstep. zstep. if_cases Ksh; [zify_cond Ksh; lia | ].
  zstep. if_cases Klz; [zify_cond Klz; lia | ].
  zstep. zstep. if_cases Kla; [zify_cond Kla; rewrite (land3_0 lenp ltac:(rewrite KL; rewrite <- Zplus_mod_idemp_l, KA; reflexivity)) in Kla; lia | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh_read mm lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DgWalkXB.DG_W, DgWalkXB.SP0; exact MU) ltac:(lia) eq_refl SHL) as SHl end.
  do 8 zstep. if_cases K3; [cbv in K3; discriminate | ].
  clear SHl.
  do 19 zstep.
  replace (0 <? buf)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  rewrite (Z.mod_small s 64) by lia.
  rewrite Z.shiftl_1_l. rewrite (Z.mod_small (2 ^ s + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.land (2 ^ s + -1) (Wm + dW + dP + 1)) with ((Wm + dW + dP + 1) mod 2 ^ s)%Z
    by (rewrite Z.land_comm; replace (2 ^ s + -1)%Z with (Z.ones s) by (rewrite Z.ones_equiv; lia); rewrite Z.land_ones by lia; reflexivity).
  replace (Z_to_bv 64 (bv_unsigned sp + -96)) with (Z_to_bv 64 (SP0 - 96)) by (unfold DgWalkXB.SP0; f_equal; lia).
  replace (2 ^ s + -1)%Z with (2 ^ s - 1)%Z by lia.
  set (Wp1 := (Wm + dW + dP + 1)%Z).
  eassert (HM : dg_mem m1 _ 0 Ks bs).
  { unfold DgWalkXB.dg_mem, DgWalkXB.DG_W, DgWalkXB.SP0. replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  pose proof (Z.div_mod Wp1 (2 ^ s) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound Wp1 (2 ^ s) ltac:(lia)) as MB.
  assert (P1lo : (8 <= Wp1 / 2 ^ s)%Z).
  { apply Z.div_le_lower_bound; [lia|]. assert (8 * 2 ^ s <= 8 * 2 ^ 59)%Z by lia. lia. }
  assert (P1hi : (Wp1 / 2 ^ s < 256)%Z) by (apply Z.div_lt_upper_bound; lia).
  eapply (dg_l1_k3 (Wp1 / 2 ^ s) 0 (Wp1 mod 2 ^ s) (Wm + dW + dP - Wm + 2) s Wp1 Ks); [exact HM | lia | lia | lia | lia | lia | lia | | lia].
  intros _. split; [lia | split; lia].
Qed.

End DGB4.
