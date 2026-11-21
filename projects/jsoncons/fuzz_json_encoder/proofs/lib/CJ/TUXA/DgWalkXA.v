(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed b2z_lor01, dg_l2exit, dg_loop2 and 18 more. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @cons]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @eq]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @swrap32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_remuw]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_upper_bound]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_divuw]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEmul]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Datatypes; @false]; [@Corelib; @Init; @Logic; @or_introl]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_le_trans]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mrd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_ov_read]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @SP0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @DG_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @shadow_big]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @mrd_ov1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_ret]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @b2z_lor01]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @sh_read]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_byte]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @le1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_weed2]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Stdlib; @Lists; @List; @nth_error_None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_weed1]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_rw2_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @sx32_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_l]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_gt_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @gt]; [@Stdlib; @micromega; @RingMicromega; @OpGt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_l2exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srl]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_shiftr]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_mod64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @DGA; @dg_rw1_loop]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := Asan.Asan_loaded_segments.

Lemma le1_lit : forall v, le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof.
  intros v. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8)%Z. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.

Lemma sx32_small : forall k, (- 2 ^ 31 <= k < 2 ^ 31)%Z -> sx32 (Z_to_bv 64 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  replace ((k mod 2 ^ 64 + 2 ^ 31) mod 2 ^ 32)%Z with ((k + 2 ^ 31) mod 2 ^ 32)%Z.
  - rewrite Z.mod_small by lia. lia.
  - rewrite (Z.add_mod (k mod 2 ^ 64)) by lia. rewrite (Z.add_mod k (2 ^ 31)) by lia. rewrite Z.mod_mod_divide by (exists (2 ^ 32)%Z; reflexivity). reflexivity.
Qed.

Lemma swrap32_small : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma v_remuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z -> v_remuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold v_remuw. rewrite !Z_to_bv_unsigned.
  assert (Wx : bv_wrap 32 (bv_wrap 64 x) = x) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  assert (Wy : bv_wrap 32 (bv_wrap 64 y) = y) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  rewrite Wx, Wy. destruct (Z.eqb_spec y 0) as [E|E]; [lia|]. f_equal. apply swrap32_small.
  pose proof (Z.mod_pos_bound x y ltac:(lia)). lia.
Qed.

Lemma v_divuw_small : forall x y, (0 <= x < 2 ^ 31)%Z -> (1 <= y < 2 ^ 31)%Z -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !Z_to_bv_unsigned.
  assert (Wx : bv_wrap 32 (bv_wrap 64 x) = x) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  assert (Wy : bv_wrap 32 (bv_wrap 64 y) = y) by (unfold bv_wrap, bv_modulus; cbn -[Z.pow]; rewrite !Z.mod_small by lia; reflexivity).
  rewrite Wx, Wy. destruct (Z.eqb_spec y 0) as [E|E]; [lia|]. f_equal. apply swrap32_small.
  split; [pose proof (Z.div_pos x y); lia | ]. pose proof (Z.div_le_upper_bound x y x ltac:(lia) ltac:(nia)). lia.
Qed.

Lemma subw_mod : forall p dv, (0 <= p < 2 ^ 31)%Z -> (1 <= dv < 2 ^ 31)%Z -> bv_swrap 32 (p - p / dv * dv) = (p mod dv)%Z.
Proof.
  intros p dv Hp Hd. rewrite (Z.mod_eq p dv) by lia. replace (p - p / dv * dv)%Z with (p - dv * (p / dv))%Z by ring. apply swrap32_small.
  pose proof (Z.mod_pos_bound p dv ltac:(lia)). rewrite Z.mod_eq in H by lia. lia.
Qed.
Lemma shl_s : forall x s, (0 <= x < 2 ^ 64)%Z -> (0 <= s < 64)%Z -> ((x mod 18446744073709551616) ≪ (s mod 64))%Z = (x * 2 ^ s)%Z.
Proof. intros x s Hx Hs. rewrite !Z.mod_small by lia. apply Z.shiftl_mul_pow2. lia. Qed.

Lemma b2z_lor01 : forall b1 b2, (Z.lor (Z.b2z b1) (Z.b2z b2) = 0 \/ Z.lor (Z.b2z b1) (Z.b2z b2) = 1)%Z.
Proof. intros [|] [|]; cbv; auto. Qed.

Definition SHB : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,B|N3fff8000;").
Lemma shadow_big : forall y, (0 <= y < 2 ^ 47)%Z -> (0x7fff7000 <= Z.shiftr y 3 + 2147450880 < 0x10007fff8000)%Z.
Proof. intros y Hy. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. split; [pose proof (Z.div_pos y 8); lia | ]. apply Z.lt_le_trans with (2 ^ 44 + 2147450880)%Z; [|lia]. pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44)); lia. Qed.

Lemma mrd_ov1 : forall (m : word -> option byte) (x : Z) (b : byte), (0 <= x < 2 ^ 64)%Z -> mrd rsegs m (wa x) = Some b -> ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [b].
Proof.
  intros m x b Hx H. replace (Z_to_bv 64 x) with (wa (x + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m x [b] 0 1); [reflexivity| |cbn; lia].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth_error]. replace (x + Z.of_nat 0)%Z with x by lia. exact H.
Qed.

Section DGA.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Definition SP0 : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'7!1,4|600;/sp;").

Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.

Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis SEP_B : (buf + 21 <= SP0 - 80 \/ lenp + 4 <= buf)%Z.

Definition app_buf : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2+_T!2'I!2'N/buf;!1,B|45;!1,B|N3fff7000;!2'I!1,B|\0007fff8000;/buf;").
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 80)%Z.

Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Definition DG_W : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+_D+0+0!1,B|20;!3,50!4,`N+0+0!2'^?'`O!1,B|610;'`O!3,50!4,`N+0+0/buf;!2'N/buf;!1,B|45;!3,50!4,`N+0+0/lenp;!2'N/lenp;1!3,50!4,`N+0+0/kp;!2'N/kp;1!1,80").

Lemma sh_read : forall (m : word -> option byte) (y x : Z), munch DG_W m0 m -> (0 <= y < 2 ^ 47)%Z -> x = (Z.shiftr y 3 + 2147450880)%Z ->
  mrd rsegs m0 (wa x) = Some (Z_to_bv 8 0) -> ov_read_bytes rsegs m (Z_to_bv 64 (Z.shiftr y 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof using All.
  intros m y x MU Hy -> H. pose proof (shadow_big y Hy) as SBg.
  apply mrd_ov1; [lia|]. unfold mrd. rewrite (MU (wa (Z.shiftr y 3 + 2147450880))). { exact H. }
  unfold DG_W. cbn [outside]. rewrite wa_unsigned by lia. unfold SP0, app_buf in *. repeat split; lia.
Qed.

Definition dg_post (Ks : Z) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S90!1,4|600;!1+30|30;!1+3!1,42%~R1!1+`13!1+23!1,8+a5!1,B,^D|10;$Ks;R+0$ms';R+`X!2+`Y1$t0';R1!2+`Y1$t1';R1!2+`Y1$t2';R1!2+`Y1$a1';R1!2+`Y1$a2';R1!2+`Y1$a3';R1!2+`Y1$a4';R1!2+`Y1$a5';R1!2+`Y1$a6';R1!2+`Y1$a7';R1!2+`Y1$t3';R1!2+`Y1$t4';R1!2+`Y1$t5';R1!2+`Y1$t6';R1!2+`Y4$m';R4!2+`Y+0$res;R+0!2+`Y+0$len;R+0!2+`Y+0$kappa;R+0!2+`Y5$bs;R5!2+H!3+<+`X#D!7'`Z!O'`[/ra;/sp;/gp;/tp;#C#B#A/s0;/s1;!2'60#4#@#?#>#=#<#;#:/s2;/s3;/s4;/s5;/s6;/s7;/s8;/s9;/s10;/s11;#9#8#7#6/F;!1'`\/ra;/fc;!1,^K1#5!1'`T'`3!2+H!3'`P'`Q/m0;#5!2+H!3'a0'`3/m0;#5!2+H!2'a1'`3#5!2+H!4'a2'`3#5!2'^?'`O!1,B|610;'`O!2+H!4'a3'`3#5/buf;#1!2+H!3+<+`>!2'`C3#1}E!2+H!4'a4'`3#5/lenp;!3,5+a5!1,a6!2'60#36!2+H!2+H!2'I7#3!2'I#3!1,B|45;!2+H!4'a4'`3#5/kp;!3,5+a5!1,a6!2'60!2'N#E#26!2+H!2+H!2'I!1,_5|42;#2!2'I#2!1,B8!2+_T!3+<+0#4,Q!3+<+0#47").

Definition dg_mem (m : word -> option byte) (j8 : list byte) (len Kv : Z) (bs : list byte) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S70!1,4|600;|30;!1+3!1,41!1+22!2'^?'`O!1,B|610;}8!1,8+a5$m;R%~R!1+30!1+`12$j8;R3$len;R+0$Kv;R+0$bs;R3!2+H!4'a2'`3#544!2+H!4'a4'`3#54!3,5+a5!2,a75#4!3,5+a5!1,a8/s7;!3,5+a5!1,a8/s6;!3,5+a5!1,a8/s5;!3,5+a5!1,a8/s4;!3,5+a5!1,a8/s3;!3,5+a5!1,a8/s2;!3,5+a5!1,a8/s1;!3,5+a5!1,a8/s0;!3,5+a5!1,a8/ra;6!2+H!3'`P'`Q/m0;#5!2+H!3'a0'`3/m0;#5!2+H!2'a1'`3#5!2+H!4'a3'`3#5/buf;#1!2+H!3+<+`>!2'`C2#1}E!2+H!4'a4'`3#5/lenp;!3,5+a5!1,a6!2'60#36!4'a4'`3#5/kp;!3,5+a5!1,a6!2'60#26").

Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DG_W in MU.

Lemma dg_ret : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (res len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  a0' = Z_to_bv 64 res -> (res = 0 \/ res = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8b8c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Ha0 Hres. dg_mem_intro HM. subst a0'.
  do 11 zstep.
  replace (Z_to_bv 64 (SP0 - 80 + 80)) with sp by (unfold SP0; rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST SP0.
  finish. all: first [eassumption | lia].
Qed.

Lemma dg_xori : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (x len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (x = 0 \/ x = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 x) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8b88) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Hx. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_ret; [exact HM0 | exact LR | exact KR | reflexivity | ]. destruct Hx as [-> | ->]; cbv; auto.
Qed.

Lemma dg_or : forall t0' t1' t2' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (b1 b2 : bool) (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 (Z.b2z b2)) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8b84) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_xori; [exact HM0 | exact LR | exact KR | apply b2z_lor01].
Qed.

Lemma dg_weed1 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8b04) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 2 step. if_cases K1.
  - do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
  - step. if_cases K2.
    + do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 step. if_cases K3.
      * do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 step. if_cases K4.
        -- do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
        -- do 4 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
Qed.

Lemma dg_weed2 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8b3c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR.
  do 3 step. if_cases K1.
  - do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
  - step. if_cases K2.
    + do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
    + do 2 step. if_cases K3.
      * do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
      * do 3 step. if_cases K4.
        -- do 7 step. zsimp_slt. eapply dg_or; [exact HM | exact LR | exact KR].
        -- do 2 step. eapply dg_ret; [exact HM | exact LR | exact KR | reflexivity | lia].
Qed.

Lemma dg_rw2_loop : forall (n : nat) (D r one len : Z) t1' t2' s1' a1' a2' a3' a5' a6' a7' s2' s3' s4' s5' s6' s7' t4' t5' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= one)%Z -> (r + one <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) t1' t2' (Z_to_bv 64 (D - r - one)) s1'
                                  (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) a5' a6' a7' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11
                                  (Z_to_bv 64 r) t4' t5' t6')
                              F (Z_to_bv 64 0xc8ab0) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r one len t1' t2' s1' a1' a2' a3' a5' a6' a7' s2' s3' s4' s5' s6' s7' t4' t5' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall a7x t5x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) t1' t2' (Z_to_bv 64 (D - r - one)) s1'
              (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) (Z_to_bv 64 (r + one)) a6' a7x s2' s3' s4' s5' s6' s7' s8 s9 s10 s11
              (Z_to_bv 64 r) t4' t5x (Z_to_bv 64 (D - r - one)))
         F (Z_to_bv 64 0xc8ac4) fc None m (seg_rom rsegs))).
  { intros a7x t5x.
    pose proof (sh_read m (buf + len + -1) (Z.shiftr (buf + (len - 1)) 3 + 2147450880) MU ltac:(lia) ltac:(f_equal; f_equal; lia) (SHBUF (len - 1) ltac:(lia))) as SH.
    zstep. zstep. if_cases K0; [cbv in K0; discriminate | ].
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU SH RD. store_done.
    assert (HM1 : dg_mem m1 j8 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zstep. zstep. if_cases K2.
    + eapply dg_weed2; [exact HM1 | exact LR | exact KR].
    + do 3 zstep. zstep. if_cases K3; zify_cond K3.
      *
        replace (Z_to_bv 64 (D - r - one - one)) with (Z_to_bv 64 (D - (r + one) - one)) by (f_equal; lia).
        eapply (IH (Z.to_nat (D - (r + one)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zstep. eapply dg_weed2; [exact HM1 | exact LR | exact KR].
  }
  do 3 zstep. if_cases K1.
  - apply BODY.
  - do 2 zstep. if_cases K4.
    + do 2 zstep. eapply dg_weed2; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_rw1_loop : forall (n : nat) (D r tk len : Z) t1' t2' s0' s1' a2' a4' a5' a6' a7' s2' s3' s4' s6' s7' t3' t4' t5' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= tk)%Z -> (r + tk <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) t1' t2' s0' s1'
                                  (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) a4' a5' a6' a7' s2' s3' s4' (Z_to_bv 64 r) s6' s7' s8 s9 s10 s11
                                  t3' t4' t5' t6')
                              F (Z_to_bv 64 0xc8958) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r tk len t1' t2' s0' s1' a2' a4' a5' a6' a7' s2' s3' s4' s6' s7' t3' t4' t5' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall a6x a7x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) t1' t2' s0' s1'
              (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) (Z_to_bv 64 (r + tk)) a5' a6x a7x s2' s3' s4' (Z_to_bv 64 r) s6' s7' s8 s9 s10 s11
              t3' t4' t5' t6')
         F (Z_to_bv 64 0xc896c) fc None m (seg_rom rsegs))).
  { intros a6x a7x.
    pose proof (sh_read m (buf + len + -1) (Z.shiftr (buf + (len - 1)) 3 + 2147450880) MU ltac:(lia) ltac:(f_equal; f_equal; lia) (SHBUF (len - 1) ltac:(lia))) as SH.
    zstep. zstep. if_cases K0; [cbv in K0; discriminate | ].
    assert (Hi : (Z.to_nat (len - 1) < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat (len - 1))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (u8arr_read rsegs m buf bs (len - 1) b (Z_to_bv 64 (buf + len + -1)) BU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep.
    pose proof (u8arr_store_ok rsegs m buf bs (len - 1) (Z_to_bv 64 (buf + len + -1)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (b' := Z_to_bv 8 (bv_unsigned b + -1)).
    replace (write_to_mem m (Z_to_bv 64 (buf + len + -1)) (le1 (Z_to_bv 64 (bv_unsigned b + -1)))) with (write_to_mem m (wa (buf + (len - 1))) [b'])
      by (f_equal; [unfold wa; f_equal; lia | symmetry; apply le1_lit]).
    pose proof (u8arr_write rsegs m buf bs (len - 1) b' BU ltac:(lia)) as BU'.
    clear BU SH RD. store_done.
    assert (HM1 : dg_mem m1 j8 len (Ks + kappa) (upd bs (Z.to_nat (len - 1)) b')).
    { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU'|].
      split; [rewrite upd_length; exact BL|]. split; [exact LE | exact KC]. }
    zstep. zstep. if_cases K2.
    + eapply dg_weed1; [exact HM1 | exact LR | exact KR].
    + zstep. zstep. if_cases K3; zify_cond K3.
      *
        eapply (IH (Z.to_nat (D - (r + tk)))); [lia | reflexivity | exact HM1 | exact LR | exact KR | lia | lia | lia | lia].
      * zstep. eapply dg_weed1; [exact HM1 | exact LR | exact KR].
  }
  zstep. zstep. if_cases K1.
  - apply BODY.
  - do 3 zstep. if_cases K4.
    + do 2 zstep. eapply dg_weed1; [exact HM0 | exact LR | exact KR].
    + apply BODY.
Qed.

Lemma dg_l2exit : forall (Dold r one len kappa Ks : Z) t2' a1' a2' a5' s2' s3' s4' s5' s6' s7' t4' t5' t6' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= -1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (0 <= r < 10 * Dold)%Z -> (1 <= one <= 2 ^ 59)%Z -> (10 * Dold < 2 ^ 63)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 Dold) (Z_to_bv 64 kappa)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 (10 * Dold)) (Z_to_bv 64 one) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 (Z_to_bv 64 r) t4' t5' t6')
                              F (Z_to_bv 64 0xc8a3c) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hr Ho HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  clear SHk.
  zstep. rewrite sx32_small by lia.
  do 3 zstep.
  assert (HM1 : dg_mem m1 j8 len (Ks + kappa) bs).
  { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  do 3 zstep. if_cases K1.
  - zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 14 zstep.
      replace (Z_to_bv 64 (Dold * 10 - (one + r))) with (Z_to_bv 64 (10 * Dold - r - one)) by (f_equal; lia).
      eapply (dg_rw2_loop (Z.to_nat (10 * Dold - r)) (10 * Dold) r one len); [reflexivity | exact HM1 | exact LR | lia | lia | lia | lia | lia].
Qed.

Lemma dg_loop2 : forall (n : nat) (i p2 D s len Ks : Z) t2' s0' a2' a5' s3' s4' s5' s6' s7' (m : word -> option byte) j8 (bs : list byte),
  Z.to_nat (17 - i) = n ->
  dg_mem m j8 len Ks bs -> (1 <= len <= 3 + i)%Z -> (0 <= i <= 17)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (56 <= s <= 59)%Z -> (D <= p2 < 2 ^ s)%Z -> (2 * 10 ^ i <= D)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' s0' (Z_to_bv 64 (- i))
                                  (Z_to_bv 64 kp) (Z_to_bv 64 (10 ^ i)) a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  (Z_to_bv 64 10) s3' s4' s5' s6' s7' s8 s9 s10 s11 (Z_to_bv 64 p2) (Z_to_bv 64 s) (Z_to_bv 64 (2 ^ 32 - 1)) (Z_to_bv 64 (2 ^ s - 1)))
                              F (Z_to_bv 64 0xc89ac) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros i p2 D s len Ks t2' s0' a2' a5' s3' s4' s5' s6' s7' m j8 bs Hn HM LR IR KsR Hs HP HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (H2s : (2 ^ 56 <= 2 ^ s <= 2 ^ 59)%Z) by (split; apply Z.pow_le_mono_r; lia).
  assert (H10 : (1 <= 10 ^ i < 2 ^ 58)%Z) by (pose proof (Z.pow_pos_nonneg 10 i ltac:(lia) ltac:(lia)); lia).
  pose proof (sh_read m lenp (Z.shiftr lenp 3 + 2147450880) MU ltac:(lia) eq_refl SHL) as SHl.

  assert (BODY : forall a1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) (Z_to_bv 64 (10 ^ i)) (Z_to_bv 64 D) (Z_to_bv 64 (- i))
              (Z_to_bv 64 kp) a1x a2' (Z_to_bv 64 D) (Z_to_bv 64 (2 ^ s)) a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
              (Z_to_bv 64 10) (Z_to_bv 64 ((p2 * 10) ≫ (s mod 64))) (Z_to_bv 64 (Z.land ((p2 * 10) ≫ (s mod 64)) 4294967295)) s5' s6' s7' s8 s9 s10 s11
              (Z_to_bv 64 (p2 * 10)) (Z_to_bv 64 s) (Z_to_bv 64 4294967295) (Z_to_bv 64 (2 ^ s - 1)))
         F (Z_to_bv 64 0xc89d4) fc None m (seg_rom rsegs))).
  { intros a1x.
    zstep; zstep; if_cases K0b; [cbv in K0b; discriminate | ].
    zstep; rewrite sx32_small by lia.
    do 3 zstep.
    clear SHl.
    pose proof (sh_read m1 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold DG_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
    do 4 zstep; if_cases K0c; [cbv in K0c; discriminate | ].
    clear SHb.
    zstep.
    pose proof (u8arr_store_ok rsegs m1 buf bs len (Z_to_bv 64 (buf + len)) BU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    set (dch := ((p2 * 10) ≫ (s mod 64) + 48)%Z).
    replace (write_to_mem m1 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 dch))) with (write_to_mem m1 (wa (buf + len)) [Z_to_bv 8 dch])
      by (f_equal; symmetry; apply le1_lit).
    pose proof (u8arr_write rsegs m1 buf bs len (Z_to_bv 8 dch) BU ltac:(lia)) as BU'.
    clear BU; store_done.
    assert (HM2 : dg_mem m2 j8 (len + 1) Ks (upd bs (Z.to_nat len) (Z_to_bv 8 dch)))
      by (unfold dg_mem; split; [exact ST|]; split; [exact FR|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact BU'|];
          split; [rewrite upd_length; exact BL|]; split; [exact LE | exact KC]).
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
  do 6 zstep. if_cases K1.
  - apply BODY.
  - zstep; zstep; if_cases K0a; [cbv in K0a; discriminate | ]; zstep; rewrite sx32_small by lia; zstep; if_cases K2; zify_cond K2; [lia | ].
    apply BODY.
Qed.

Lemma dg_rw1_entry : forall (D r dv cnt s len Ks : Z) t2' a1' a2' a4' a5' s2' s3' s4' s6' s7' t3' t5' t6' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 3)%Z -> (2 <= cnt <= 4)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (dv = 1 \/ dv = 10 \/ dv = 100)%Z -> (56 <= s <= 59)%Z -> (0 <= r < D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 80)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 cnt) (Z_to_bv 64 dv)
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 D) a4' a5' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' s3' s4' (Z_to_bv 64 r) s6' s7' s8 s9 s10 s11 t3' (Z_to_bv 64 s) t5' t6')
                              F (Z_to_bv 64 0xc8904) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hdv Hs Hr HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  clear SHk.
  zstep. rewrite sx32_small by lia.
  do 5 zstep.
  assert (KC' : rw_cells rsegs m1 kp [C4 (Z_to_bv 64 (Ks + (cnt - 2)))]) by (replace (Ks + (cnt - 2))%Z with (Ks + cnt + -2)%Z by lia; exact KC).
  assert (HM1 : dg_mem m1 j8 len (Ks + (cnt - 2)) bs).
  { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC']. }
  set (tk := ((dv ≪ (s mod 64)) mod 2 ^ 64)%Z).
  assert (Htk : (1 <= tk < 2 ^ 64)%Z).
  { assert (Hc : (s = 56 \/ s = 57 \/ s = 58 \/ s = 59)%Z) by lia. unfold tk.
    destruct Hdv as [-> | [-> | ->]]; destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence. }
  replace (Z_to_bv 64 (dv ≪ (s mod 64))) with (Z_to_bv 64 tk) by (unfold tk; apply Z_to_bv_mod64).
  do 2 zstep. if_cases K1.
  - zstep. eapply dg_weed1; [exact HM1 | lia | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed1; [exact HM1 | lia | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 5 zstep.
      eapply (dg_rw1_loop (Z.to_nat (D - r)) D r tk len); [reflexivity | exact HM1 | lia | lia | lia | lia | | lia].
      revert K2; unfold tk; rewrite ?Z.mod_small by lia; intros K2; lia.
Qed.

End DGA.
