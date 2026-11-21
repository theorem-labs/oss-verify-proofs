(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed Lepi, Lfin, Lhalf and 17 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul_core1.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import F_multf3_core.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @landM32_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @land_W64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @land_ones_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @micromega; @VarMap; @Empty]; [@stdpp; @bitvector; @definitions; @bv_swrap_small]; [@stdpp; @bitvector; @definitions; @bv_half_modulus]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv_signed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_eqm]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @sra63_neg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_small]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@Corelib; @Init; @Datatypes; @negb]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @mul_finish]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @mul_round]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @mf_normal]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @mk128]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Corelib; @Init; @Datatypes; @pair]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @shr_land_W64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_shiftr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @sticky_b2z]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_nonneg]; [@Corelib; @Init; @Logic; @proj2]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_land_mask]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @micromega; @ZMicromega; @SplitProof]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @pe_shift]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @pe_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @sub64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @wrap64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @is_neg64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @zext32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @add64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @shl64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @not64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @nez64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @MASK48]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lor]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_core; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @saved9]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @lo64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @hi64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @multf3_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Lepi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @lo64_mk128]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @hi64_mk128]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec0]; [@Corelib; @Init; @Datatypes; @reflect]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @unsigned_lit_land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xor]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lxor]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @not_iff_morphism]; [@Corelib; @Program; @Basics; @flip]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @flip2]; [@Corelib; @Classes; @Morphisms; @iff_flip_impl_subrelation]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_eq_0_iff]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_eq0]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @land_1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @SIGN64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @eqz64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @ltu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @b2z_Zb2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slti]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slti]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_b2z_zero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_sign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Lup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_b2z_nonzero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Ltie]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @lxor_b2z_1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slti_b2z]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @mfr_normal]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @andb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_l]; [@Stdlib; @micromega; @Tauto; @EQ]; [@Stdlib; @micromega; @Tauto; @isBool]; [@Stdlib; @micromega; @Tauto; @FF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Lhalf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Lrnd2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @mf_tiny]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_total]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @mfr_caseA]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srai]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srai]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul; @land_sub_neg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @mod64_land63]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @sra63_pos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @land_M32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_shl_shr_land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @land_ones_l]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @mfr_caseB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @mfr_caseC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @F_f128_mul_core1; @MC_tail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @INF_HI]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @signed_of_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Lfin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Walk; @Linf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_land64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @mul_core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_core; @multf3_mid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_core; @multf3_core1]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_multf3_tail; @Ltail]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

(* [comment removed for export] *)
Definition multf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 80) (bv_unsigned sp).

Definition saved9 (s8 s7 s6 s5 s4 s3 s2 s1 s0 : word) (j : list byte) : list cell := ltac2:(Rpl.RP.run_i (rplG ()) 10 "S20!1+0!1,1|600;|30;$s8;R0$s7;R0$s6;R0$s5;R0$s4;R0$s3;R0$s2;R0$s1;R0$s0;R0$j;R!1+2!1+0!1,11!3,3+4!2,5}8#1!3,3+4!1,6#:!3,3+4!1,6#9!3,3+4!1,6#8!3,3+4!1,6#7!3,3+4!1,6#6!3,3+4!1,6#5!3,3+4!1,6#4!3,3+4!1,6#3!3,3+4!1,6#2!1,7+4").

(* [comment removed for export] *)
Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros. rewrite landM32_mod. apply Z.mod_small. lia. Qed.
Lemma land_ones_r : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros. rewrite land_W64. apply Z.mod_small. lia. Qed.
Lemma land_ones_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros. rewrite Z.land_comm. apply land_ones_r. assumption. Qed.
(* [comment removed for export] *)
Lemma sra63_neg : forall x, -2^63 <= x < 0 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma sra63_negw : forall x, 2^63 <= x < 2^64 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
  intros x Hx. replace (Z_to_bv 64 x) with (Z_to_bv 64 (x - 2^64)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  apply sra63_neg. lia.
Qed.
Lemma sra63_pos : forall x, 0 <= x < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
  intros x Hx. rewrite Z_to_bv_signed, bv_swrap_small.
  2:{ unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 `div` 2) with (2^63). lia. }
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia.
Qed.
Lemma lxor_b2z_1 : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zzr := zsimp; rewrite ?Z.add_0_r;
  try rewrite !land_sub_neg by alia;
  try rewrite !land_M32_small by alia;
  try rewrite !sra63_neg by alia; try rewrite !sra63_pos by alia;
  try rewrite !land_ones_l by (first [zrange | alia]);
  rewrite ?Z.land_0_l.
Ltac zrstep := step; zzr.

(* [comment removed for export] *)
Lemma mfr_normal : forall s pe hh hl lh ll,
  0 < pe <= 131072 -> 0 <= hl < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.lor (Z.land (pe ≪ 48) 18446744073709551615) (Z.land hh 281474976710655)) (Z.land hl 18446744073709551615) lh ll.
Proof.
  intros * Hpe Hhl. rewrite (land_ones_r hl) by lia. apply mf_normal. lia.
Qed.

Lemma mfr_caseA : forall s pe hh hl lh ll,
  -126 <= pe < -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.lor (Z.land (hh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                  (Z.land ((hl ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615)) 0)
    (Z.lor (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)
                               (Z.lor (Z.land (lh ≪ Z.land (pe + 127) 63) 18446744073709551615)
                                      (Z.land ((ll ≫ 1) ≫ Z.land (Z.lxor (pe + 127) 18446744073709551615) 63) 18446744073709551615))))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseB : forall s pe hh hl lh ll,
  pe = -63 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s 0 (hh ≫ Z.land (1 - pe) 63)
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) 0)
    (Z.lor (Z.lor 0 (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Lemma mfr_caseC : forall s pe hh hl lh ll,
  -63 < pe <= 0 -> 0 <= hh < 2^64 -> 0 <= hl < 2^64 -> 0 <= lh < 2^64 -> 0 <= ll < 2^64 ->
  mul_finish s pe hh hl lh ll =
  mul_round s (Z.land (hh ≫ Z.land (1 - pe) 63) 18446744073709551615)
    (Z.lor (Z.land (hl ≫ Z.land (1 - pe) 63) 18446744073709551615)
           (Z.land (Z.land (hh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615))
    (Z.lor (Z.land (hl ≪ Z.land (pe + 127) 63) 18446744073709551615) (Z.land (lh ≫ Z.land (1 - pe) 63) 18446744073709551615))
    (Z.lor (Z.lor 0 (Z.lor (Z.land (ll ≫ Z.land (1 - pe) 63) 18446744073709551615)
                           (Z.land (Z.land (lh ≪ 1) 18446744073709551615 ≪ Z.land (Z.lxor (1 - pe) 18446744073709551615) 63) 18446744073709551615)))
           (Z.b2z (0 <? Z.lor 0 (Z.land (ll ≪ Z.land (pe + 127) 63) 18446744073709551615)))).
Proof. intros * Hpe Hhh Hhl Hlh Hll. mf_pure. Qed.

Section Walk.
  Variables (sp : word).
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).

  Ltac hyp :=
    match goal with
    | H : mem_inv _ ?m |- mem_inv _ ?m => exact H
    | H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
    | H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
    | H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
    | H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
    | H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
    | H : bv_unsigned ?w = _ |- bv_unsigned ?w = _ => exact H
    | H : ?x = ?y |- ?x = ?y => exact H
    | H : ?x <> ?y |- ?x <> ?y => exact H
    | |- (0 <= _ < _)%Z => zrange2
    end.
  Ltac join L := eapply L; try hyp.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac model_in H := sf_model_in H.

  Ltac eblia := rewrite ?Z.shiftl_mul_pow2 in * by lia; blia.
  Ltac decide_in_cond H c :=
    match c with
    | context [Z.eqb ?x ?y] =>
        first [ rewrite (proj2 (Z.eqb_eq x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.eqb_neq x y)) in H by (clear H; eblia) ]
    | context [Z.ltb ?x ?y] =>
        first [ rewrite (proj2 (Z.ltb_lt x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.ltb_ge x y)) in H by (clear H; eblia) ]
    | context [Z.leb ?x ?y] =>
        first [ rewrite (proj2 (Z.leb_le x y)) in H by (clear H; eblia) | rewrite (proj2 (Z.leb_gt x y)) in H by (clear H; eblia) ]
    end.
  Ltac decide_head H :=
    cbn_bool_in H;   (* [comment removed for export] *)
    lazymatch type of H with
    | _ = ?t => match t with context [if ?c then _ else _] => decide_in_cond H c end
    end;
    cbn_bool_in H.

  (* [comment removed for export] *)
  Lemma Lepi : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    Z_to_bv 64 (lo64 R) = w0 -> Z_to_bv 64 (hi64 R) = w1 ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 w0 w1 y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb3034) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO H0 H1. unfold saved9 in FR.
    pose_word_ranges.
    do 11 zstep.
    release_frame FR ST (bv_unsigned sp).
    rewrite <- H0, <- H1. finish.
  Qed.

  (* [comment removed for export] *)
  Ltac res_words :=
    rewrite ?lo64_mk128, ?hi64_mk128 by zrange; weq.

  (* [comment removed for export] *)
  Lemma Linf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (sgn : Z)
      y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mk128 (Z.lor sgn 9223090561878065152) 0 ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 sgn) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb2d54) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rs HR. subst R.
    do 5 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lup : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 : Z)
      y5 y6 y7 y8 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z ->
    R = mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + 1) 18446744073709551615 =? 0)) 18446744073709551615) (Z.land (rl + 1) 18446744073709551615) ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) y12 y13 y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb3028) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 HR. subst R.
    do 3 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Ltie : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh1 lh2 ll2 : Z)
      y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh1 < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z ->
    R = (if Z.lor ll2 (Z.lxor lh2 9223372036854775808) =? 0
         then mk128 (Z.land (rh1 + Z.b2z (Z.land (rl + Z.land rl 1) 18446744073709551615 <? rl)) 18446744073709551615)
                    (Z.land (rl + Z.land rl 1) 18446744073709551615)
         else mk128 rh1 rl) ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 rh1) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) y14 y15 y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb2d98) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 HR.
    do 4 zstep. zstep. if_cases K; zify_cond K.
    -   decide_head HR. subst R. join Lepi; res_words.
    - decide_head HR. subst R. do 7 zstep. join Lepi; res_words.
  Qed.

  (* [comment removed for export] *)
  Lemma Lrnd2 : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 <> 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb2d88) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep. rewrite lxor_b2z_1. zstep.
    zstep. if_cases K; zify_cond K; rewrite zb_lxor_sign in K by lia.
    -   decide_head HR. join Lup.
    - decide_head HR. join Ltie.
  Qed.

  (* [comment removed for export] *)
  Lemma Lhalf : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rl rh lh2 ll2 sgn : Z)
      y5 y6 y7 y8 y9 y16 y17 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= rl < 2^64)%Z -> (0 <= rh < 2^64)%Z -> (0 <= lh2 < 2^64)%Z -> (0 <= ll2 < 2^64)%Z -> (0 <= sgn < 2^64)%Z ->
    lh2 = 9223372036854775808 ->
    R = mul_round sgn rh rl lh2 ll2 ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 rl) (Z_to_bv 64 sgn) (Z_to_bv 64 ll2) (Z_to_bv 64 lh2) (Z_to_bv 64 rh)
               (Z_to_bv 64 9223372036854775808) y16 y17
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb301c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO R0 R1 R2 R3 R4 Kh HR.
    unfold mul_round in HR. model_in HR. decide_head HR.
    do 2 zstep.
    zstep. if_cases K; zify_cond K.
    -   decide_head HR. join Ltie.
    - decide_head HR. join Lup.
  Qed.

  (* [comment removed for export] *)
  Lemma Lfin : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (pe hh hl lh ll sgn : Z)
      y6 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (-131072 <= pe < 32767)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (0 <= sgn < 2^64)%Z ->
    R = mul_finish sgn pe hh hl lh ll ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 pe) y6 (Z_to_bv 64 (-16383)) y8 y9
               y10 (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb2d68) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Rpe Rhh Rhl Rlh Rll Rsg HR.
    pose_word_ranges.
    destruct (Z.lt_ge_cases 0 pe) as [C1|C1].
    -
      rewrite mfr_normal in HR by lia.
      zrstep; if_decide. do 4 zrstep. do 2 zrstep. zrstep; if_cases K; zify_cond K.
      + join Lhalf.
      + join Lrnd2.
    - destruct (Z.lt_ge_cases pe (-126)) as [C2|C2].
      +
        rewrite mf_tiny in HR by lia. subst R.
        zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 2 zrstep. join Lepi; res_words.
      + zrstep; if_decide. do 3 zrstep. zrstep; if_decide. do 5 zrstep.
        destruct (Z.lt_total pe (-63)) as [C3|[C3|C3]].
        *
          rewrite mfr_caseA in HR by lia.
          zrstep; if_decide. do 7 zrstep. zrstep; if_decide. do 5 zrstep.
          do 7 zrstep. zrstep; if_decide. do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        *
          rewrite mfr_caseB in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 6 zrstep. zrstep; if_decide. do 7 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
        *
          rewrite mfr_caseC in HR by lia.
          zrstep; if_decide. do 4 zrstep. zrstep; if_decide. do 8 zrstep. zrstep; if_decide.
          do 9 zrstep. zrstep; if_decide. do 5 zrstep. do 6 zrstep.
          zrstep; if_cases K; zify_cond K.
          -- join Lrnd2.
          -- join Lhalf.
  Qed.

  (* [comment removed for export] *)
  Lemma Ltail : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (es hh hl lh ll scale sgn : Z)
      y6 y8 y9 y18 y19 y20 y21 y22 y23 y24 y28 y29 y30 y31
      (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
    rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
    (4096 <= bv_unsigned sp)%Z ->
    (0 <= es < 65536)%Z -> (0 <= hh < 2^64)%Z -> (0 <= hl < 2^64)%Z -> (0 <= lh < 2^64)%Z -> (0 <= ll < 2^64)%Z ->
    (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
    R = MC_tail sgn es hh hl lh ll scale ->
    evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
      (MS (mkR ra spw gp tp (Z_to_bv 64 es) y6 (Z_to_bv 64 (-16383)) y8 y9
               (Z_to_bv 64 scale) (Z_to_bv 64 sgn) (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh)
               (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 hl)
               y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0xb2ca4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until R. intros MI MU WM ST FR SPLO Res Rhh Rhl Rlh Rll Rsc Rsg HR.
    pose_word_ranges.
    unfold MC_tail in HR. model_in HR.
    do 3 zstep. replace (scale + -16383) with (scale - 16383) by lia.
    zstep. if_cases K1; zify_cond K1; decide_head HR.
    -
      do 3 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Lfin. all: first [lia | exact HR].
      + join Linf.
    - do 12 zstep. zstep. if_cases K2; zify_cond K2; signed_lits_in K2; decide_head HR.
      + join Linf.
      + zstep. rewrite <- (Z_to_bv_land64 (Z.shiftl ll 1)). join Lfin. all: first [lia | exact HR].
  Qed.
End Walk.

(* [comment removed for export] *)
Lemma multf3_core : forall ra sp gp tp w1 w2 s0 s1 (scale sgn ea eb : Z) w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6
    y8 y9 y18 y19 y20 y21 y22 y23 y24 y28
    (F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
  y28 = Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32) ->
  mem_inv rsegs m1 ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
  stk rsegs m1 (bv_unsigned sp - 80) (bv_unsigned sp + -80) ->
  rw_cells rsegs m1 (bv_unsigned sp + -80) (saved9 s8 s7 s6 s5 s4 s3 s2 s1 s0 j) ->
  (4096 <= bv_unsigned sp)%Z ->
  (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z -> (0 <= sgn < 2^64)%Z ->
  R = mul_core sgn ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) scale ->
  evt rsegs (multf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 eb) w1 w2 y8 y9 (Z_to_bv 64 scale) (Z_to_bv 64 sgn) w4 a3 a4
             (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
             y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 y28 w3 t5 t6)
        F (Z_to_bv 64 0xb2b18) fc None m1 (seg_rom rsegs)).
Proof.
  intros until R. intros Hy28 MI MU WM ST FR SPLO Ra Rb Rsc Rsg HR. subst y28 R.
  eapply evt_cut. { eapply multf3_core1; eauto. }
  intros ms' P.
  destruct P as (es & hh & hl & lh & ll & y5' & t1 & t2' & x8 & x9 & a5' & a6' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & t3 & t4 & t5' & t6'
                  & EQ & Res & Rhh & Rhl & Rlh & Rll & E5 & Ea5 & Ea6 & Et2 & E).
  subst ms' y5' a5' a6' t2'. rewrite EQ.
  eapply Ltail; eauto.
Qed.
