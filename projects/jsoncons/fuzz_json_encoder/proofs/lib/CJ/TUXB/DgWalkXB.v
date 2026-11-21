(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed b2z_lor01, dg_l2exit, dg_or and 21 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @cons]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @eq]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @swrap32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_remuw]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_upper_bound]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_divuw]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEmul]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Datatypes; @false]; [@Corelib; @Init; @Logic; @or_introl]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_le_trans]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mrd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_ov_read]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Corelib; @Init; @Nat; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_pow2_small]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec0]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_signed]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEpow]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @ZArith; @BinInt; @Z; @to_N]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @SP0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @DG_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @shadow_big]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @mrd_ov1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_ret]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @b2z_lor01]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_b2z]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Init; @Logic; @False_ind]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @sh_read]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_byte]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @le1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_weed2]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Stdlib; @Lists; @List; @nth_error_None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_weed1]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @land3_0]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @swrap32_mod64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slt]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slti]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slti]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @DGB; @dg_rw2_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @lxor63]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lxor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slti_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_slt_b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXB; @DgWalkXB; @sx32_small]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rsegs := AsanUbsan.AsanUbsan_loaded_segments.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition SHB : Z := 2147450880.
Lemma shadow_big : forall y, (0 <= y < 2 ^ 47)%Z -> (0x7fff7000 <= Z.shiftr y 3 + 2147450880 < 0x10007fff8000)%Z.
Proof. intros y Hy. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. split; [pose proof (Z.div_pos y 8); lia | ]. apply Z.lt_le_trans with (2 ^ 44 + 2147450880)%Z; [|lia]. pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44)); lia. Qed.

(* [comment removed for export] *)
Lemma mrd_ov1 : forall (m : word -> option byte) (x : Z) (b : byte), (0 <= x < 2 ^ 64)%Z -> mrd rsegs m (wa x) = Some b -> ov_read_bytes rsegs m (Z_to_bv 64 x) 1 = Some [b].
Proof.
  intros m x b Hx H. replace (Z_to_bv 64 x) with (wa (x + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m x [b] 0 1); [reflexivity| |cbn; lia].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth_error]. replace (x + Z.of_nat 0)%Z with x by lia. exact H.
Qed.


(* [comment removed for export] *)
Ltac pgoal := match goal with |- ?G => idtac "GOAL:" G end.
Lemma lxor63 : forall x, (0 <= x < 2 ^ 63)%Z -> Z.lxor x 9223372036854775808 = (x + 9223372036854775808)%Z.
Proof. intros x H. pose proof (zb_lxor_pow2_small x 63 H ltac:(lia)) as E. change (2 ^ 63)%Z with 9223372036854775808%Z in E. exact E. Qed.
(* [comment removed for export] *)
Ltac ub_norm :=
  repeat match goal with |- context [(?x mod 18446744073709551616)%Z] =>
    first [ rewrite (Z.mod_small x 18446744073709551616) by lia | fail ] end;
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) by lia end;
  repeat match goal with |- context [(?x <? ?y)%Z] =>
    first [ replace (x <? y)%Z with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y)%Z with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; zsimp.
Lemma sgn_small : forall x, (- 2 ^ 63 <= x < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x H. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - replace (x mod 2 ^ 64)%Z with (x + 2 ^ 64)%Z by (rewrite <- (Z.mod_add x 1) by lia; rewrite Z.mod_small by lia; lia).
    destruct (Z.ltb_spec0 (x + 2 ^ 64) (2 ^ 63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 x (2 ^ 63)); lia.
Qed.
Lemma swrap32_modl : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616 + y) = (x + y)%Z.
Proof.
  intros x y H. change 18446744073709551616%Z with (2 ^ 64)%Z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite (Z.mod_eq x (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) + y + 2 ^ 31)%Z with (x + y + 2 ^ 31 + (- (2 ^ 32) * (x / 2 ^ 64)) * 2 ^ 32)%Z by (change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac ub_norm_in K :=
  repeat match type of K with context [(?x mod 18446744073709551616)%Z] => rewrite (Z.mod_small x 18446744073709551616) in K by lia end;
  repeat match type of K with context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) in K by lia end;
  repeat match type of K with context [(?x <? ?y)%Z] =>
    first [ replace (x <? y)%Z with true in K by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y)%Z with false in K by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z] in K.
Lemma land3_0 : forall k, (k mod 4 = 0)%Z -> Z.land k 3 = 0%Z.
Proof. intros k H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
(* [comment removed for export] *)
Lemma swrap32_mod64 : forall x y, (- 2 ^ 31 <= x + y < 2 ^ 31)%Z -> bv_swrap 32 (x mod 2 ^ 64 + y mod 2 ^ 64) = (x + y)%Z.
Proof.
  intros x y H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite (Z.mod_eq x (2 ^ 64)), (Z.mod_eq y (2 ^ 64)) by lia.
  replace (x - 2 ^ 64 * (x / 2 ^ 64) + (y - 2 ^ 64 * (y / 2 ^ 64)) + 2 ^ 31)%Z
    with (x + y + 2 ^ 31 + (- (2 ^ 32) * (x / 2 ^ 64 + y / 2 ^ 64)) * 2 ^ 32)%Z by (change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Section DGB.
(* [comment removed for export] *)
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable fc : bv 32.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.

Definition SP0 : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'7!1,4|600;/sp;").
(* [comment removed for export] *)
Hypothesis BUFR : (4096 <= buf /\ buf + 21 <= 2^47)%Z.
Hypothesis SPR0 : (2^40 <= SP0 /\ SP0 + 8 <= 2^47)%Z.
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis KS : (SP0 + 8 <= kp /\ kp + 8 <= 2^47)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.                      (* [comment removed for export] *)
Hypothesis SEP_B : (buf + 21 <= SP0 - 96 \/ lenp + 4 <= buf)%Z.
(* [comment removed for export] *)
Definition app_buf : Prop := (buf + 21 <= 0x7fff7000 \/ 0x10007fff8000 <= buf)%Z.
Hypothesis APP_B : app_buf.
Hypothesis APP_S : (0x10007fff8000 <= SP0 - 96)%Z.
(* [comment removed for export] *)
Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 21)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Definition DG_W : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+_D+0+0!1,B|20;!3,50!4,a2+0+0!2'^?'a3!1,B|620;'a3!3,50!4,a2+0+0/buf;!2'N/buf;!1,B|45;!3,50!4,a2+0+0/lenp;!2'N/lenp;1!3,50!4,a2+0+0/kp;!2'N/kp;1!1,80").

(* [comment removed for export] *)
Lemma sh_read : forall (m : word -> option byte) (y x : Z), munch DG_W m0 m -> (0 <= y < 2 ^ 47)%Z -> x = (Z.shiftr y 3 + 2147450880)%Z ->
  mrd rsegs m0 (wa x) = Some (Z_to_bv 8 0) -> ov_read_bytes rsegs m (Z_to_bv 64 (Z.shiftr y 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof using All.
  intros m y x MU Hy -> H. pose proof (shadow_big y Hy) as SBg.
  apply mrd_ov1; [lia|]. unfold mrd. rewrite (MU (wa (Z.shiftr y 3 + 2147450880))). { exact H. }
  unfold DG_W. cbn [outside]. rewrite wa_unsigned by lia. unfold SP0, app_buf in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition dg_post (Ks : Z) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (res len kappa : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch DG_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (SP0 - 96) SP0
    /\ u8arr rsegs m' buf bs /\ length bs = 21%nat
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 (Ks + kappa))] /\ (-18 <= kappa <= 2)%Z
    /\ (res = 0 \/ res = 1)%Z.

(* [comment removed for export] *)
Definition dg_mem (m : word -> option byte) (j8 : list byte) (len Kv : Z) (bs : list byte) : Prop :=
  stk rsegs m (SP0 - 96) (SP0 - 96) /\
  rw_cells rsegs m (SP0 - 96) [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  munch DG_W m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  u8arr rsegs m buf bs /\ length bs = 21%nat /\
  rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] /\ rw_cells rsegs m kp [C4 (Z_to_bv 64 Kv)].

Ltac dg_mem_intro H := destruct H as (ST & FR & MU & WM & MI & BU & BL & LE & KC); unfold DG_W in MU.

(* [comment removed for export] *)
Lemma dg_ret : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (res len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  a0' = Z_to_bv 64 res -> (res = 0 \/ res = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc598) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Ha0 Hres. dg_mem_intro HM. subst a0'.
  do 13 zstep.
  replace (Z_to_bv 64 (SP0 - 96 + 96)) with sp by (unfold SP0; rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST SP0.
  finish. all: first [eassumption | lia].
Qed.

(* [comment removed for export] *)
Lemma dg_xori : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (x len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (x = 0 \/ x = 1)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 x) a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc594) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR Hx. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_ret; [exact HM0 | exact LR | exact KR | reflexivity | ]. destruct Hx as [-> | ->]; cbv; auto.
Qed.

(* [comment removed for export] *)
Lemma dg_or : forall t0' t1' t2' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (b1 b2 : bool) (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (Z.b2z b1)) (Z_to_bv 64 (Z.b2z b2)) a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc590) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR. pose proof HM as HM0. dg_mem_intro HM.
  zstep. eapply dg_xori; [exact HM0 | exact LR | exact KR | apply b2z_lor01].
Qed.

(* [comment removed for export] *)
Lemma dg_weed1 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc510) fc None m (seg_rom rsegs)).
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

(* [comment removed for export] *)
Lemma dg_weed2 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (len kappa Ks : Z) (bs : list byte),
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc548) fc None m (seg_rom rsegs)).
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

(* [comment removed for export] *)
Lemma dg_rw2_loop : forall (n : nat) (D r one len : Z) t0' s0' s1' a1' a2' a3' a5' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= one)%Z -> (r + one <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' (Z_to_bv 64 0) (Z_to_bv 64 1) s0' s1'
                                  (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) a5' (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) a7'
                                  (Z_to_bv 64 (D - r - one)) s3' s4' s5' s6' s7' s8' s9' s10 s11
                                  t3' t4' (Z_to_bv 64 r) t6')
                              F (Z_to_bv 64 0xcc4b4) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r one len t0' s0' s1' a1' a2' a3' a5' a7' s3' s4' s5' s6' s7' s8' s9' t3' t4' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall s1x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 (D - r - one)) s1x
              (Z_to_bv 64 (buf + len + -1)) a1' a2' a3' (Z_to_bv 64 one) (Z_to_bv 64 (r + one)) (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880)) a7'
              (Z_to_bv 64 (D - r - one)) s3' s4' s5' s6' s7' s8' s9' s10 s11
              t3' t4' (Z_to_bv 64 r) t6')
         F (Z_to_bv 64 0xcc4c8) fc None m (seg_rom rsegs))).
  { intros s1x.
    zstep. if_cases Kt1; [cbv in Kt1; discriminate | ].
    zstep. if_cases Kt2; [cbv in Kt2; discriminate | ].
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

(* [comment removed for export] *)
Lemma dg_rw1_loop : forall (n : nat) (D r tk len : Z) t0' t1' t2' s0' s1' a2' a4' s2' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' (m : word -> option byte) j8 (kappa Ks : Z) (bs : list byte),
  Z.to_nat (D - r) = n ->
  dg_mem m j8 len (Ks + kappa) bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= 2)%Z ->
  (0 <= r)%Z -> (1 <= tk)%Z -> (r + tk <= D)%Z -> (D < 2 ^ 64)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1' t2' s0' s1'
                                  (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) a4' (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880))
                                  (Z_to_bv 64 1) (Z_to_bv 64 0) s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11
                                  t3' t4' t5' t6')
                              F (Z_to_bv 64 0xcc2d4) fc None m (seg_rom rsegs)).
Proof using All.
  induction n as [n IH] using lt_wf_ind.
  intros D r tk len t0' t1' t2' s0' s1' a2' a4' s2' s3' s5' s6' s7' s8' s9' t3' t4' t5' t6' m j8 kappa Ks bs Hn HM LR KR Hr Ho Hro HD.
  pose proof HM as HM0. dg_mem_intro HM.
  assert (BODY : forall t1x t2x, evt rsegs (dg_post Ks)
     (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp t0' t1x t2x s0' s1'
              (Z_to_bv 64 (buf + len + -1)) (Z_to_bv 64 tk) a2' (Z_to_bv 64 D) (Z_to_bv 64 (r + tk)) (Z_to_bv 64 (Z.shiftr (buf + len + -1) 3 + 2147450880))
              (Z_to_bv 64 1) (Z_to_bv 64 0) s2' s3' (Z_to_bv 64 r) s5' s6' s7' s8' s9' s10 s11
              t3' t4' t5' t6')
         F (Z_to_bv 64 0xcc2e8) fc None m (seg_rom rsegs))).
  { intros t1x t2x.
    zstep. if_cases Kt1; [cbv in Kt1; discriminate | ].
    zstep. if_cases Kt2; [cbv in Kt2; discriminate | ].
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

(* [comment removed for export] *)
Lemma dg_l2exit : forall (Dold r one len kappa Ks : Z) t2' t3' t4' t6' s1' a1' a2' s2' s4' s5' s6' s7' s8' s9' (m : word -> option byte) j8 (bs : list byte),
  dg_mem m j8 len Ks bs -> (1 <= len <= 21)%Z -> (-18 <= kappa <= -1)%Z -> (- 2 ^ 31 + 18 <= Ks <= 2 ^ 31 - 3)%Z ->
  (0 <= r < 10 * Dold)%Z -> (1 <= one <= 2 ^ 59)%Z -> (10 * Dold < 2 ^ 63)%Z ->
  evt rsegs (dg_post Ks) (MS (mkR ra (Z_to_bv 64 (SP0 - 96)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr lenp 3 + 2147450880)) t2' (Z_to_bv 64 Dold) s1'
                                  (Z_to_bv 64 kp) a1' a2' (Z_to_bv 64 (10 * Dold)) (Z_to_bv 64 one) (Z_to_bv 64 2147450880) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                                  s2' (Z_to_bv 64 kappa) s4' s5' s6' s7' s8' s9' s10 s11 t3' t4' (Z_to_bv 64 r) t6')
                              F (Z_to_bv 64 0xcc400) fc None m (seg_rom rsegs)).
Proof using All.
  intros until bs. intros HM LR KR KsR Hr Ho HD.
  pose proof HM as HM0. dg_mem_intro HM.
  pose proof (sh_read m kp (Z.shiftr kp 3 + 2147450880) MU ltac:(lia) eq_refl SHK) as SHk.
  zstep. if_cases Kz; [zify_cond Kz; lia | ].
  zstep. zstep. if_cases Ka; [zify_cond Ka; rewrite (land3_0 kp KA) in Ka; lia | ].
  do 4 zstep. if_cases K0; [cbv in K0; discriminate | ].
  zstep. rewrite sx32_small by lia.
  zstep. zstep. zstep. if_cases Kov; [zify_cond Kov; rewrite swrap32_mod64 in Kov by lia; exfalso; exact (Kov eq_refl) | ].
  zstep. zstep. if_cases K0b; [cbv in K0b; discriminate | ].
  clear SHk.
  zstep.
  assert (HM1 : dg_mem m1 j8 len (Ks + kappa) bs).
  { unfold dg_mem. split; [exact ST|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BU|].
    split; [exact BL|]. split; [exact LE | exact KC]. }
  do 4 zstep. if_cases K1.
  - zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
  - zstep. if_cases K2; zify_cond K2.
    + zstep. eapply dg_weed2; [exact HM1 | exact LR | lia].
    + pose proof (sh_read m1 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold DG_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
      zstep. zstep. if_cases K5; [cbv in K5; discriminate | ].
      clear SHl.
      zstep. rewrite sx32_small by lia. do 23 zstep.
      rewrite (swrap32_small (len + -1)) by lia.
      ub_norm.
      replace (len + -1 + buf)%Z with (buf + len + -1)%Z by lia.
      replace (Z_to_bv 64 (Dold * 10 - (one + r))) with (Z_to_bv 64 (10 * Dold - r - one)) by (f_equal; lia).
      eapply (dg_rw2_loop (Z.to_nat (10 * Dold - r)) (10 * Dold) r one len); [reflexivity | exact HM1 | exact LR | lia | lia | lia | lia | lia].
Qed.


End DGB.
