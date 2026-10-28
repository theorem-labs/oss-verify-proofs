(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import DgWalkX_u5 G3PureX_u5 G3LemX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.TUX Require Import G3CeilUbs.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @swrap32_id]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @swrap32_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_eq]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @TT]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@stdpp; @bitvector; @definitions; @bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_mod64]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@stdpp; @bitvector; @definitions; @bv_wrap_small]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_0_r]; [@stdpp; @bitvector; @definitions; @bv_extract_unsigned]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @tactics; @f_equal_help]; [@stdpp; @bitvector; @definitions; @bv_half_modulus]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @signed_of_extract]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @NArith; @BinNat; @N; @lt]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @N2Z; @inj_lt]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_low]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_spec_low]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_spec_high]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_high]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pow2_bits_low]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_0]; [@Stdlib; @Bool; @Bool; @andb_false_l]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_mod_distr_r]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEmul]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEpow]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @ZArith; @BinInt; @Z; @to_N]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Corelib; @Init; @Datatypes; @pair]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @GSP]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @frm0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @rsegs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @G3_W]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Stdlib; @Lists; @List; @firstn_skipn]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @u8arr_app]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_post]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @Lists; @List; @length_firstn]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @Lists; @List; @length_skipn]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @proj1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @rw_cells_app]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgWalkX_u5; @dg_post]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgWalkX_u5; @dg_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgWalkX_u5; @SP0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgWalkX_u5; @rsegs]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_transport]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@Corelib; @Init; @Logic; @eq_sym]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Lists; @List; @length_app]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Stdlib; @Lists; @List; @nth_error]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @nth_error_upd_same]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @DgWalkX_u5; @sx32_small]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @mcode]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @shr32_range]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @negw_small]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_call]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @ezext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_shl_shr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @FLoad]; [@LinuxProcessSemantics; @Riscv; @Instr; @FMT_D]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_cells_image]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_bytes_b]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @bv_lit_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells_read_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sll]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sll]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @fcvt_d_w]; [@LinuxProcessSemantics; @Riscv; @Fpu; @RNE]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@LinuxProcessSemantics; @Riscv; @Fpu; @fflags_bits]; [@Corelib; @Init; @Datatypes; @snd]; [@LinuxProcessSemantics; @Riscv; @Fpu; @fflags]; [@LinuxProcessSemantics; @Riscv; @Fpu; @fp_of_int]; [@LinuxProcessSemantics; @Riscv; @Fpu; @fmt_double]; [@LinuxProcessSemantics; @Riscv; @Instr; @Fcvt]; [@LinuxProcessSemantics; @Riscv; @Instr; @FC_D]; [@LinuxProcessSemantics; @Riscv; @Instr; @FC_W]; [@LinuxProcessSemantics; @Riscv; @Sem; @eff]; [@LinuxProcessSemantics; @Riscv; @Sem; @EDone]; [@LinuxProcessSemantics; @Riscv; @Sem; @fset]; [@LinuxProcessSemantics; @Riscv; @Sem; @rget]; [@LinuxProcessSemantics; @Riscv; @Sem; @accrue]; [@LinuxProcessSemantics; @Riscv; @Sem; @with_pc]; [@LinuxProcessSemantics; @Riscv; @Sem; @c_pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @exec_fcvt_d_w]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @rmode_static]; [@LinuxProcessSemantics; @Riscv; @Fpu; @rmode]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @frm0_accrue]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @fmul_d]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @fari_fl]; [@LinuxProcessSemantics; @Riscv; @Instr; @F_MUL]; [@LinuxProcessSemantics; @Riscv; @Instr; @Fari]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @fari_d]; [@LinuxProcessSemantics; @Riscv; @Sem; @fget]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @bvmap_set_set_same']; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @bvmap_set_set_comm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @freg_get_same]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @freg_get_other]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @exec_fari_d]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @rmode_dyn]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @fcvt_w_d]; [@LinuxProcessSemantics; @Riscv; @Fpu; @RUP]; [@LinuxProcessSemantics; @Riscv; @Fpu; @fp_to_int]; [@LinuxProcessSemantics; @Riscv; @Sem; @rset]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @exec_fcvt_w_d]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @kc_facts]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @KCZ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PEZ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @KCW]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @zbv_signed]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @zbv_eqm]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod_idemp_l]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PT_BASE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @pt_read]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PT_BYTES]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @bytes_le_to_Z]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @pt_facts]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PTZ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PE_BASE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @pe_read]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @PE_BYTES]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @land_mask_low]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_mul]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @hi32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @prod32b]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_mod]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MULHU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mulhu]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mulhu]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @split32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @mcode_mult]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @MULT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @mult_lo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @mult_mono]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @mult_hi]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3PureX_u5; @mult_lo62]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_mul]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @mulhu_lo32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @sext_extract32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @extract64_id]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @shl_small]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @mi_shift]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @kc_arg]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_tail]; [@Stdlib; @micromega; @RingMicromega; @PsatzLet]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @False_ind]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @Arith; @Wf_nat; @lt_wf_ind]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @micromega; @RingMicromega; @PsatzSquare]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @nrm_unique]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_join]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_gt_dec]; [@Stdlib; @ZArith; @BinInt; @Z; @gt]; [@Stdlib; @micromega; @RingMicromega; @OpGt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @land_bit]; [@Corelib; @Init; @Logic; @iff]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_loopB]; [@Corelib; @Classes; @RelationClasses; @reflexivity]; [@Corelib; @Classes; @RelationClasses; @PreOrder_Reflexive]; [@Stdlib; @ZArith; @BinInt; @Z; @le_preorder]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Fmv]; [@LinuxProcessSemantics; @Riscv; @Instr; @FMV_X_F]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@Stdlib; @ZArith; @BinInt; @Z; @succ]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_succ_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3WalkX_u5; @G3; @g3_loopA]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_0_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @lor_hidden]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @mant_bits]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @TUX; @G3LemX_u5; @exp_bits]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma swrap32_id : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SR0|10;!1,50|4f;!1,52!2'413!2+1!2'2!1'34#1!2'6#14!2'8#24!2';13!2'6,<1%~R!2'2,<3!2'6,<4%~R89!2'2,<1$Ha;R;$~R+=!3'>13#2%Ha;R;%~R+=!2'2,<4vd!2,?+@!2'A,<18!1#2>!1,B+C!1+D+C!2,E+0#2!1+F+0!1+H+0!2,O+0,P!2,R+01!3,Q+0F!1,S2!3,N+0EG!2'VD,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2|500;!1,5K!2'41L%~R!2'2,<L!2'6,<M!1,SK!2'41!1'^8O!2'^7P1$x;R+0$Hx;R5vdvd!6'7+06$z;R+0!3+9+0!2':#14#3&__sat1;R7:&__sat0;R<=&__sat1;R?9&__arith;R$__x1;R+0&__wit;R@A&__varmap;RBC&__ff;R!7,GD'I+J+J,K!4,L+0!3,M+0HG,TE,UIJ%__x1;R+0!3+9+0!2':!2'8#144#1!1#1#6!2'\6M!3'^06M&__sat3;R!2';1L%~R8N&__sat2;R$Ha;R;$~R+=!3'>1L#2%Ha;R;%~R+=!2'2,<M&__sat1;R7:&__sat0;R<=&__sat1;R?9&__sat3;R!1#5>N&__arith;R$__x1;R+0&__wit;R@A&__varmap;RBC&__ff;R!8,^1D'I+J+J,K!7,^2D'I+J+J,K!7,GD'I+J+J,K!4,L+0!2,^3+0G,^4E,U!7,GD'I+J+J,K!4,L+0E,^5G,U!1,^6+J!7,^2D'I+J+J,K!7,GD'I+J+J,K!4,L+0!2,R+0,<,^4H,U!7,GD'I+J+J,K!4,L+0H,^5!3,Q+0FO,UIJ%__x1;R+0%~R5!2+1!2'2,<6!2'66M!2#1#9#8!3+9+0!2':!2'\!2'8#2QPQ#2!3+9+0!2'^9O#2#2").
Qed.
Lemma swrap32_mod : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "ST0|10;!1,50|500;!1,52!2';13!2'6,<1!2'413%~R!2'2,<3!2'6,<6%~R57!2'2,<1$Ha;R9$~R+=!3'>13#2!2'2,<6%Ha;R9%~R+=;!2'^761vd!2,?+@!2'A,<15!1,B+C!1+D+C!1+F+0!1+H+0!2,O+0,P!2,O+00!1,S2!3,Q+0!2,R+01E!3,^<+0!2,O+0|11;F!2'VB,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2'^=#36!2'^=#16!2'8#2K!2'8#3=!2'^=#26!2'8MN!2':!2'\!2'8#4=6=!2'\M6!2'41!1'^8E!2'^7R1$x;R+0$k;R+0vdvd&H;R&__sat2;R48&__sat1;R:<&__sat0;R!2'^:61%~R;%~R9!2'2,<=&__sat2;R!1#3>7&__arith;R$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R?@&__varmap;R!4,^;+0!2,E+0#3#2!2,E+0#4A&__ff;R!7,GB'I+J+J,K!4,L+0!3,N+0!3,N+0CDG,T!3,N+0!3,N+0CGD,UHI%__x3;R+0%__x2;R+0%__x1;R+0!3+9+0!2'8!2'8#1#2J!2'8!2'8#1J#2!3#1#6=#7!3+9+0!2'8!2'8#2=K!2'8L=!6'^>+0O$z;R+0!3+9+0!2':!2'\#16=P!6'7+0Q$z;R+0!3+9+0!2':#1=P!2,?+0!2':Q=!2'\O6!4'^?M#26&__sat1;R48&__sat0;R:<&__sat1;R!1#2>7&__arith;R&__wit;R?@&__varmap;R!1,^@+0A&__ff;R!6,^AB'I+J+J,K!7,GB'I+J+J,K!4,L+0F,T!2,R+0,<,UHI%~R!3+9+06,<+^B#1!2'8!2'8#3N=#1!3+9+0!2':!2'\!2'8LSRS!2':!2'\!2'8#2SRS!3+9+0!2'^9EL!2'^9E#2").
Qed.
(* [comment removed for export] *)
Lemma kc_arg : forall ple, (-1127 <= ple <= 971)%Z -> bv_swrap 32 (18446744073709551566 - ple mod 18446744073709551616) = (-50 - ple)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S\0!1,^C|:067;!1,5|91cb;!2+1!2'20#1!2'2#11!1,5|^C0000000000000000;!2'^7#23!2':#2!2'^=34|500;!1,S6!1,5|^B7fffffffffffffce;!1,^C|512;!2':9#3|10;!1,5;!1,56!2'6,<<!2'4<=%~R!2'2,<=!2'6,<?!2'2,<<vd!2,?+@!2'A,<<>!1,B+C!1+D+C!1,^@+0!1+F+0!1+H+0!2,O+0,P!3,M+0!2,R+09H|P00000000;!1,5J!2,R+0K!2,O+0;!2,R+0<!2,R+03!2'VG,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2':9#2!2'^7#33!2'8K!2'^=KS!2'8:!2'^=T?!2':9#4|4f;!1,5W!2'4<X%~R!2'2,<X!2'6,<Y!3,Q+0N!1,SW$ple;R+0$Hp;R2!6'7+05$z;R+0!3+9+0!2'^97!2':8#1:&H;R&__sat2;R!2';<=%~R>@&__sat1;R$Ha;RA$~R+=!3'><=#2%Ha;RA%~R+=!2'2,<?&__sat0;R!2'^:#43%~R!2'2,<#4%~R!2'2,<3!2'2,<!2'^7#63&__sat2;R!1#3B@&__arith;R$__x2;R+0$__x1;R+0&__wit;RCD&__varmap;R!4,^;+0!2,E+0#3#2EF&__ff;R!7,GG'I+J+J,K!4,L+0!3,N+0I!3,^<+0!3,N+0L!3,^<+0LM!3,Q+0N7,T!3,M+0!2,R+08!3,M+0H!3,^<+0OM,UPQ%__x2;R+0%__x1;R+0!3+9+0!2'8!2':9#1!2'^=!2'8K!2'^=K#2?!2':8!2':#1!2'^=3#2!2#1!2'^7#73#7!3+9+0!2'8R!2'^=!2'8K!2'^=K4?!2':85!6'^>+0U$z;R+0!3+9+0!2'^97#1V!6'7+0!2'^97:$z;R+0!3+9+0#1V!2'^D:&__sat1;R!2';<X%~R>Z&__sat0;R$Ha;RA$~R+=!3'><X#2%Ha;RA%~R+=!2'2,<Y&__sat1;R!1#2BZ&__arith;R$__x1;R+0&__wit;RCD&__varmap;R!2,E+0#2F&__ff;R!8,^1G'I+J+J,K!7,^2G'I+J+J,K!7,GG'I+J+J,K!4,L+0!2,R+00,^4H,U!7,GG'I+J+J,K!4,L+0H,^4!2,R+01,U!1,^6+J!7,^2G'I+J+J,K!7,GG'I+J+J,K!4,L+0!2,^3+0[,^4I,U!7,GG'I+J+J,K!4,L+0I,^5[,UPQ%__x1;R+0%~R2!2+1!2'2!1'3YR!2'6RY!2#1#7#6!2'^97U!2'^E:T!2':8!2':#3!2'^=3S#1!2'\#23!3'^F#23&__arith;R&__wit;RCD&__varmap;REF&__ff;R!6,^AG'I+J+J,K!7,GG'I+J+J,K!4,L+0O,T!2,R+0,<,UPQ%~R!3+9+03,<+^B#1").
Qed.
(* [comment removed for export] *)
Lemma mi_shift : forall mie ple, (-1127 <= ple <= 971)%Z -> (9 <= mie - ple + 10 <= 62)%Z ->
  ((bv_swrap 32 (mie mod 18446744073709551616 - (ple + -10) mod 18446744073709551616) mod 18446744073709551616) mod 64 = mie - ple + 10)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_:0!1,5|31;|32;!1,51!2'8!2':#3#22!1,5|51e;!1,5|^C0000000000000000;!2'^7#45!2':#4!2'^=56|500;!1,S8!1,^C1!2'8#4:|600;!1,5<!2'8!2':#5#42!2'8#3:!2'^7?5!2':?!2'^=5@!2'^7#55!2':#5!2'^=5B!2'2,<5|10;!1,5E!1,58!2'6,<F!2'4FG%~R!2'2,<G!2'6,<I!2'2,<F!1#2vd!2,?+@!2'A,<FH!1,B+C!1+D+C!1,^@+0!4,^;+0!4,^;+0!2,E+0#5#3O#2!2,E+0#4!1+F+0!1+H+0!2,O+0,P!2,O+0E!2,R+02!3,N+0!3,M+0STU|P00000000;!1,5W!2,R+0X|11;!2,O+0Z|20;!2,O+0\!2,R+0F!2,R+05!3,^<+0^2^0!2'VR,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2'8!2':#1#22!2'^7;5!2':!2'^=X^7!2'^=XB!2'8>!2'^=^8I!2'8!2':#6#52!2'^99>$z;R+0!3+9+0!2'\!2'\#15=^:!2'\>5$z;R+0!3+9+0#1^:!4,^;+0!2,E+0#3#2O!2,R+00!2,R+04!7,^2R'I+J+J,K!7,GR'I+J+J,K!4,L+0^@,^4V,U!7,GR'I+J+J,K!4,L+0V,^4^A,U!1,^6+J!2,R+0,<!2+1!2'20^6!2'2^64!2'8!2':#2#32!2'2,<>!2'8!2':#7#62!2'\^H5!3+9+05,<!2'6,<5!2'8!2':#8#72!2'\^L5!2'8!2':#9#82!2'\^N5!2'8!2':#:#92!2'8!2':#;#:2!2'^O^Q5!2'\!2'8!2':#<#;25!2'2,<^S!2,^S+0}5}4}2!2,^S+0^W}1!6,^AR'I+J+J,K!7,GR'I+J+J,K!4,L+0^2,T^D,U!3,N+0!3,M+0[TU!7,GR'I+J+J,K!4,L+0^D,^4S,U%~R^J+^B!2'2,<#5!2'8!2':#>#=2!2'\_25|4f;!1,5_4!2'4F_5%~R!2'2,<_5!2'6,<_6!3,Q+0^1!1,S_4&__arith;R&__wit;RMN&__varmap;ROQ&__ff;R^Z^4^5_0#1$mie;R+0$ple;R+0$Hp;R!2+1!2'2!1,^C|:067;#1!2'2#1!1,5|91cb;$Hx;R!2+1!2'203!2'234!6'7+07$z;R+0!3+9+0!2'\!2'\!2'^99!2':#1!2'\;55=>!6'7+0A$z;R+0!3+9+0!2'\!2'\!2'^99!2':C#15=>&H;R&__sat3;R!2'^:#45%~R!2'2,<#4%~RD!2'2,<!2'^7#65&__sat2;R!2'^:;5%~R!2'2,<;%~RD!2'2,<!2'^7!2'8#6:5&__sat1;R!2';FG%~RHJ&__sat0;R$Ha;RK$~R+=!3'>FG#2%Ha;RK%~R+=!2'2,<I&__sat1;RLJ&__arith;R$__x4;R+0$__x3;R+0$__x2;R+0$__x1;R+0&__wit;RMN&__varmap;RPQ&__ff;R!7,GR'I+J+J,K!4,L+0!3,N+0V!3,^<+0!3,M+0!3,^<+0Y[!3,^<+0Y^0!3,Q+0^19,T!3,M+0!3,M+0S^3!3,M+0!3,N+0T!2,R+0:!3,^<+0^2[,U^4^5%__x4;R+0%__x3;R+0%__x2;R+0%__x1;R+0!3+9+0!2'8^6!2'^=!2':!2'^=X#3!2'^=X#4I!2':!2':#1!2'^=5#4!2':!2'8#2:!2'^=5#3!4#1!2'^7#:5!2'^7!2'8#9:5#9#:!3+9+0!2'8!2'8!2':#4#32!2'^=!2':!2'^=X@!2'^=X6I!2':7A!6'^>+0^9$z;R+0!3+9+0!2'\!2'\!2'^99#15=^:!6'7+0^;^<!6'7+0>^<!6'7+0^=^>!6'7+0>^>!2,?+0>^=!3'^0>5&__arith;R$__x2;R+0$__x1;R+0&__wit;RMN&__varmap;R^?Q&__ff;R!8,^1R'I+J+J,K^B^C!7,^2R'I+J+J,K!7,GR'I+J+J,K!4,L+0^D,^4V,U!7,GR'I+J+J,K!4,L+0V,^5^2,U^4^5%__x2;R+0%__x1;R+0%~R^E!2+1!2'2,<^F!2'6^F5!3#1#5#6#3!2'\^==!3'^0^==&__sat0;R!2'^G>5%~R^G%~RD!2'2,<^I&H;R!2'^H^:5%~R!1'^I^J!3+9+0^H!2'8!2'^=5!2'^7^H5^I&H0;R!2'^J^H5%~R^K!2+1!2'2,<^M!2'6^M5&H1;R!2'^K^L5%~R!2'65,<!2+1!2'65^O!2'2^O,<&H2;R!2'^L^N5%~R^J!3+9+0!2'^7^P5,<&H3;R!2'^M^P5%~R^J!3+9+0!2'\^Q5^Q&H4;Rvd,^N^R^Rvd&H0;R!1#5vd!2,?+@!2'A,<5^K!2+1^T!2'6^S5&__arith;R$__p1;Rw$__x4;R+0$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R!3,^P+C!2,^Q!3,^R+0^U!3,^R+0!2,^S+0^V^X!2,^T!3,^R+0!3,^U+0!2,^V+05!2,^S+0,^W!3,^R+0!3,^X+0!2,^Y+0!1,^C,P^U!3,^R+0^X!2,^S+0^Y,^ZMN&__varmap;RPQ&__ff;R!8,^1R'I+J+J,K!7,^2R'I+J+J,K!6,^[R'I+J+J,K#7!7,GR'I+J+J,K!4,L+0S,^5^2,U^C!8,^1R'I+J+J,K!8,^1R'I+J+J,K^Z^C!7,GR'I+J+J,K!4,L+0^[,T!3,N+0^3S,U^C!8,^1R'I+J+J,K!8,^1R'I+J+J,K!7,GR'I+J+J,K!4,L+0^D,^4^[,U^C!8,^1R'I+J+J,K!7,GR'I+J+J,K!4,L+0^D,^4^2,U^C^\^C!8,^1R'I+J+J,K!7,^2R'I+J+J,K!7,GR'I+J+J,K!4,L+0^@,^4^[,U!7,GR'I+J+J,K!4,L+0^[,^4^A,U^C!7,^2R'I+J+J,K^\!7,GR'I+J+J,K!4,L+0S,^5!2,R+0=,U^4^5%__p1;Rw%__x4;R+0%__x3;R+0%__x2;R+0%__x1;R+0%~R!2+1#5!2'6#15%~R%~R_0!3+9+0>!2'8!2'^=5#6#3%~R%~R^G%~RD_1%~R!2+1!2'20^:!2'2^:4!2+1_1!2'6#5=!9#1!2'2,<_3!2'^7_25#>#=_3#2#8#9#;!2+1^T!2'6^S=^;!2'^D>&__sat1;R!2';F_5%~RH_7&__sat0;R$Ha;RK$~R+=!3'>F_5#2%Ha;RK%~R+=!2'2,<_6&__sat1;RL_7&__arith;R$__x2;R+0$__x1;R+0&__wit;RMN&__varmap;R^?Q&__ff;R!8,^1R'I+J+J,K^B^C!7,^2R'I+J+J,K!7,GR'I+J+J,K!4,L+0!2,^3+0_8,^4V,U!7,GR'I+J+J,K!4,L+0V,^5_8,U^4^5%__x2;R+0%__x1;R+0%~R^E!2+1!2'2!1'3_6^F!2'6^F_6!3#1#8#9#6!2'^99^9!2'^E>^8!2':C!2':;!2'^=5^7#1!2'\?5!3'^F?5_9!2'\#45!3'^F#45_9").
Qed.
Lemma shl_small : forall x k, (0 <= k)%Z -> (0 <= x)%Z -> (x * 2 ^ k < 2 ^ 64)%Z -> ((x ≪ k) mod 18446744073709551616 = x * 2 ^ k)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SX0!2'2,<#1!2'2,<#3|10;!1,52|600;!1,54!2'435!2'^=#5!2'43#4!1,5|^C0000000000000000;!2';35!2'6,<3%~R!2'2,<5!2'6,<6%~R:;!2'2,<3$Ha;R=$~R+=!3'>35#2%Ha;R=%~R+=!2'2,<6!2';3#6%~R:%~R!2'2,<#7!2'6,<!2'43#8$Ha;R=$~R+=!3'>3#9#2!2'43#9%Ha;R=%~R+=!2'2,<Cvd!2,?+@!2'A,<3:!1#2E%~R!2'2,<#8!2'6,<C!1#5E}2!1,B+C!1+D+C!1+F+0!1+H+0!2,R+0,<!2,R+03!1,^6+J!2,O+02!2,O+0,P!3,^<+0RQ!7,GM'I+J+J,K!4,L+0N,^4R,U!2'VM,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2'^=#5#6$x;R+0$k;R+0$Hk;R0$Hx;R1$H;R!2'6!2'^=#4!2'43#36!6'7+07$z;R+0!3+9+0!2'\#18!2'^=#6!2'43#5!3'^078&__sat3;R9<&__sat2;R>?&__sat1;R@A&__sat0;RBD&__sat1;RFG&__sat3;RH;&__arith;R$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R!3,^P+C!2,^T!3,^R+0!3,^U+0!2,^S+0}4!2,^S+0I!2,^S+0,^W,^ZJK&__varmap;R!4,^;+0!2,E+0#3#2!2,E+0#4L&__ff;R!8,^1M'I+J+J,K!8,^1M'I+J+J,K!7,GM'I+J+J,K!4,L+0N,^4O,UP!8,^1M'I+J+J,K!5,^\M'I+J+J,KP!7,GM'I+J+J,K!4,L+0N,^4Q,UP!8,^1M'I+J+J,K!7,GM'I+J+J,K!4,L+0S,^5!3,Q+0O!1,S4,UP!8,^1M'I+J+J,KTP!8,^1M'I+J+J,K!7,GM'I+J+J,K!4,L+0N,^4!2,O+0|11;,UP!7,^2M'I+J+J,K!7,GM'I+J+J,K!4,L+0N,^4S,U!7,GM'I+J+J,K!4,L+0S,^5!2,R+08,UUV%__x3;R+0%__x2;R+0%__x1;R+0%~R%~R=%~R+=!2'2,<#4%~R!2'6!2'^=#2#36%~R1%~R!2'2,<#6!2+1!2'2,<W!2'6W8!7#1#;!2'43#;#<#4#8#9#:!2'_0#5#4!3'_1#5#4&__sat3;R9<&__sat2;R>?&__sat1;R@A&__sat0;RBD&__sat1;RFG&__sat3;RH;&__arith;R$__x1;R+0&__wit;RJK&__varmap;R!2,E+0#2L&__ff;R!8,^1M'I+J+J,KTPTUV%__x1;R+0%~R0!2'2,<#2!2#1#;#:").
Qed.

Lemma zbv_eqm : forall a b, (a mod 2 ^ 64 = b mod 2 ^ 64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S:0|10;|600;!2'4!1,50!1,51!2'\#22!1,S1!1+_24!2'\#32!2'_346!2'_34#3!2'_343$a;R+0$b;R+0$H;R!3+9+03!2'\#12!6'^>57$b;R5!3+95#18!6'^>59$b;R5!3+95!2'_34!2'\#42#1!6'7+03$z;R+0!3+95!2'_34#17!2,?596#1!2'_34#2!1'_4#28!1'_4#3").
Qed.

Lemma extract64_id : forall z, bv_extract 0 64 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+_2#1!1+_2#2%~R!3+9!1+_2#3#2#1!3+9+0!2'_7#4#3!2'_7#4#2%~R!3+9+0!2'_7#3#2!2'_7#3#1!3+9!1+_2#4#3#2!1,S|600;!2'_34#2!4'_94,_:45!2'_745!2'_74!2'_34#3$z;R+0&H;R$n;R+_5$b1;R0$b2;R1!5'_623%~R!3+9+0!2'_7#3#2!2'_7#3#1!3+9!1+_2#4#3#2$~R2$~R%~R!3+9+0!2'_7#4#3!2'_7#4#2!3+9!1+_2#5#4#3#1!3'_8#3#2#1%n;R+_5%b1;R0%b2;R13!4#1465!6'7+0!2'_;4!2'_<7!1'^8,_:$z;R+0!3+9+0#18!6'7+07$z;R+0!3+9+0!2'_;4#18!3'_=47!2'_>45!2'_<7,<!1'_?7!2'_746!4'_@4,_:45").
Qed.
Lemma sext_extract32 : forall z, sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 (bv_swrap 32 z).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SZ0|600;!1,S0!1+_21|500;!1,S3!2'_31#1!4'_91,_:45!2'_A46!2'^94#2!1'_31!2'^94#1!2'_715!2'_;1#1!1'_C4!2'_;4!2'8<=!2'8#1=!2'_;4?%~R+0+0|10;!1,5B!2'4C!1,50!2'\#1D!1,53!2'4CF!2'\EG!2'\=G!2'\#1G!2'\!2'8JIG!2'6,<C%~R!2'2,<F!2'6,<G!2'2,<C!1,B+C!1+D+C!1,^@+0!1+F+0!1+H+0!2,R+0,<!2'VS,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2&__sat1;R!2';CF%~RLM&__sat0;R$Ha;RN$~R+=!3'>CF#2%Ha;RN%~R+=!2'2,<G&__sat1;R!1#2vd!2,?+@!2'A,<CLM&__arith;R&__wit;ROP&__varmap;RQR&__ff;R!6,^AS'I+J+J,K!7,GS'I+J+J,K!4,L+0!3,Q+0!2,R+0C4,TT,UUV%~R!3+9+0G,<+^B#1!2'4C!1'^84!2'6,<F$z;R+0!6'72!2'_317$b;R2!3+92#1!2'_318!8'_B+02997:!2,?%~R+029!6'7+0!2'^94;$z;R+0!3+9+0#18!6'7+0<$z;R+0!3+9+0:8vd!8'_B+0+0!1':>!1':@==!8'_B+0A':':>@!2,?%~R+0A':vdvd!6'7+0!2'\!2'8HIG$z;R+0!3+9+0#1!2'\!2'8#2=G!6'7+0K$z;R+0!3+9+0!2'\!2'8!2'\!2'\#2DGIG#1!6'7+0J$z;R+0!3+9+0!2'\!2'8#1IG!2'\!2'8!2'\#2GIG!2,?+0KH!4'_D#1DG!4,_E+0$z;R+0!3+9+0D!2'^=#1GG!2,?+0!2'^=GG!2'\?G!4'_F#1=GW!2'\!2'8E=G!4'_FE=GW!3+9+0!2'\!2'8!2'\#1!2'4C!1'^81=X!2'\?X!3+9+0>@!2,?+0=!3+9+0!2'^94<:;!2'_G1#17!3'_H45!4'_I!2'_J,_:4Y!<'_K+_5+0'_J'^8'6'_L,_:,<!2,?+0,<4F!2,?+0F&__arith;R&__wit;ROP&__varmap;RQR&__ff;R!7,GS'I+J+J,K!4,L+0T,^5!2,R+0F,UUVY#1!3'_M416!2'_N46").
Qed.

Lemma land_mask_low : forall x k, (0 <= k <= 32)%Z -> (0 <= x)%Z -> (x mod 2 ^ k = 0)%Z -> Z.land x (2 ^ 32 - 2 ^ k) = (x mod 2 ^ 32)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SaC0!2'2,<#1|500;!1,51!2'2#12!2'2,<#3|10;!1,55!2'462!1'_O7!1'_P#5!2':7!2'46#5!2'46#4!2':8#1!2';62!2'6,<6!2'2,<2%~R?!2'6,<7%~R>@!2'2,<6$Ha;RB$~R+=!3'>62#2%Ha;RB%~R+=!2'2,<7!2'46#6!2'46#7!2'46#:!2'2,<Gvd!2,?+@!2'A,<6>!1#2I%~R!2'2,<#9!2'6,<G!1,B+C!1+D+C!2,E+0#2!1+F+0!1+H+0!3,Q+0!2,R+06!1,S1!1,5,P!2,R+0R!3,M+0QS!2,O+0,P!3,M+0US!2'VP,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2':7R!2'46#<!1'_P#4!1'_P2!1'_Q2!2':\9!2'_U#8#2!1'_P#7!2':\^3!2'_U^4#2!2'_R#8\!1'_P#8!2':\^7!2'_U^8#3!2'_T!2'_U#9#3^9!2':2#7!1'_P^;!2'46^;!2'46#8!2':2#8!2'^=!1'_O!2'46^?^>!2'8^;#7!1'46!3'^G#8F#5%~R!2'2,<F!2'2,<!2'\#9^>!2';6#8%~R>K$Ha;RB$~R+=!3'>6#;#2!2'46#;%Ha;RB%~R+=!2'2,<^H%~R!2'2,<#:!2'6,<^H!2,R+02!3,M+0^KU!2'^=^=F!6,^[P'I+J+J,K#4!7,GP'I+J+J,K!4,L+0U,^4^K,U!1,^6+J!2,R+0,<!7,GP'I+J+J,K!4,L+0^Q,^4^L,U!7,GP'I+J+J,K!4,L+0^Q,^4U,U!2'2,<#2&__sat2;R^C^D&__sat1;R^E^F&__sat0;R^G^I&__sat1;RJ^J&__arith;R$__p1;Rw$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!8,^1P'I+J+J,K!7,^2P'I+J+J,K^S^N^P^SWX%__p1;Rw%__x1;R+0%~R!2+10#2^T!3#1!2'2#<2#<#;!2':2#<!2':2#>!2';6#=%~R>%~R!2'2,<#>!2'6,<!2'46#?$Ha;RB$~R+=!3'>6#@#2!2'46#@!2'2,<^[%Ha;RB%~R+=^\%~R!2'2,<#?!2'6,<^[!2':2#@!2,E+0#3!2,O+0|11;!7,GP'I+J+J,K!4,L+0^Q,^4_4,U!2,O+05!2'46#C!2'_0^<#7!2'_Y#3#8!3+_Z!2'6#3#8!2'2#8#3!2'_X#3#8!2'_X#4#9!1'_P^V!2'_U!2'_0_<#<#7!2'_W#<#7!2'_T_>!2'_X#72!2'6#5#:!2'6#6#;!2'_W#=#8!2'_T_B!2'_X#82$b;R+X!3+9+X#1_C!2'_\#<#7!3+_Z!2'2#<#7!2'6#7#<_>!2'_X#;2!2'_T#2_G!2'2#>#9!2'2#?#:!3'^G#A^[#>!2'46#A%~R^\!2'2,<!2'\#B_L!2';6#A%~R>%~R!2'2,<#B!2'6,<_7$Ha;RB$~R+=!3'>6#D#2!2'46#D!2'2,<_Q%Ha;RB%~R+=_R%~R!2'2,<#C!2'6,<_Q!1,^@+0!4,^;+0_3#2_U!7,GP'I+J+J,K!4,L+0_6,^4U,U!7,GP'I+J+J,K!4,L+0U,^5_6,U!6,^[P'I+J+J,K#5!2'6#2#3!2'_X#@2!2'6#9#>!2'6#:#?!2'_T,_[_G!3'^G#=Z#:!2'\#>!2'46#=%~R!2'2,<Z!2'2,<`3!2'6#1#2&__sat2;R`2`4&__sat1;R^X^Y&__sat0;R^Z_0&__sat1;RJ_1&__arith;R$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K_X^P_XWX%__x2;R+0%__x1;R+0%~R`5_Z!3#1#A#<#6!2'2#:#5!2'2#;#6!2'_U!1'_P_2!2':#;#@!2'_X#<2!2':2#D!2':#?#D!2'6#>2!3'^G#E_Q#B!2'46#E%~R_R!2'2,<!2'\#F`?!2';6#E!2'46#G%~R>%~R!2'2,<#F!2'6,<`B$Ha;RB$~R+=!3'>6#H#2!2'46#H%Ha;RB%~R+=!2'2,<`E%~R!2'2,<#G!2'6,<`E!7,GP'I+J+J,K!4,L+0U,^5^K,U!3,M+0U_6!2'6#12!2'2#3#2!2':#3#4!2'22#>!2'22#2!2':2#3!2'2,<#I!2'_T,Y_G$__p1;Rw$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K_X^P!8,^1P'I+J+J,K_W^P_YWX%__p1;Rw%__x2;R+0%__x1;R+0%~R`5%~R`K#5!7,GP'I+J+J,K!4,L+0U,^4_6,U!2'_U#:#4!2'_U#=#7!2'_U#>#8!2'_U\#9!2,?+X,_[!2'_U\#8!2'_U!2':\!1'_P#@#;!2'_U#B#<!2'_T`\!2'_U\#<!2'_U!2':\!1'_P#E#@!2'_U#G#A!2'_U\#A!2'_Ta2a3!2'_U#H#B!2'_Ta5#1$b;R+X!3+9+X#1#1!2'46#F!3'^G#Ga8#D%~R!2'2,<a8!2'2,<!2'\#H`B!2';6#G%~R>%~R!2'2,<#H!2'6,<!2'46#I$Ha;RB$~R+=!3'>6#J#2!2'46#J%Ha;RB%~R+=!2'2,<a>%~R`P!2'6,<a>!7,GP'I+J+J,K!4,L+0^K,^4U,U!7,GP'I+J+J,K!4,L+0^Q,^4^K,U$x;R+0$k;R+0$Hk;R!2+103$Hx;R4$H;R!3+9+0!2'\#4!2'46#3,<&H0;R!6'7+08$z;R+0!3+9+0!2':#19:!6'7+0!1'_O;$z;R+0!3+9+0<:&__sat4;R=A&__sat3;RCD&__sat2;R!3'^G#7E#4%~R!2'2,<E!2'2,<!2'\#8F&__sat1;R!2';6#7%~R>%~R!2'2,<#8!2'6,<!2'46#9&__sat0;R$Ha;RB$~R+=!3'>6#:#2%Ha;RB%~R+=H&__sat1;RJK&__sat4;R!1#6I@&__arith;R$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!7,GP'I+J+J,K!4,L+0!3,M+0TV,T!3,M+0QU,UWX%__x1;R+0!3+9+0!2':Y!2':#1R!2':7#1!1#1Z[!1'_Q#4\^0!3+9+0!2':\[!2':7;!6'^>+0^1$z;R+0!3+9+0!2'_R#7#1!2'\#77!3'_S!2'_R#6^1!2'\#67$i;R+0$Hi;R0!6'7+X!2'_T^2^5$b;R+X!3+9+X#1!2'_U!2'\#97#3!6'^>+0^6$z;R+0!3+9+X^:!2'_U#1#3!6'7+X!2'_T^2!2'_U\#2$b;R+X!3+9+X^:#1&E;R&H0;R!6'7+0!2'^=^<F$z;R+0!3+9+0#1^8!6'7+0!1'_O^=$z;R+0!3+9+0!2'^=#1^>^8!6'7+08$z;R+0!3+9+0^@!2':#1^7!6'7+0!1'_OF$z;R+0!3+9+0^@<&P;R!6'^>+0!2'46^A$z;R+0!3+9+0#17!8'_B+0+0^B^B^A2!2,?%~R+0+0^B&__sat2;R^C^D&__sat1;R^E^F&__sat0;R^G^I&__sat1;RJ^J&__arith;R$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!7,GP'I+J+J,K!4,L+0!3,N+0^LU,T^K,UWX%__x1;R+0!3+9+0!2'8!2':2#1#12!1#1#<^M!5'_V6^;#7&__sat2;R^C^D&__sat1;R^E^F&__sat0;R^G^I&__sat1;RJ^J&__arith;R$__p1;Rw$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!8,^1P'I+J+J,K!7,^2P'I+J+J,K^N^O^P^RWX%__p1;Rw%__x1;R+0%~R!2+1#23!2'2,<!2':2#2!3#1!2'2,<#<#<#;^U!3+9+0^M7&__sat6;R=A&__sat5;RCD&__sat4;R!3'^G#;G#8%~RH!2'2,<!2'\#<^H&__sat3;R!2';6!2':2#;%~R>%~R!2'2,<^V!2'6,<!2'46!2':2#=&__sat2;R$Ha;RB$~R+=!3'>6^W#2%Ha;RB%~R+=!2'2,<!2'46^W&__sat1;R^X^Y&__sat0;R^Z_0&__sat1;RJ_1&__sat3;R!1#5I%~R!2'2,<_2!2'6,<!2'46!2':2#A&__sat6;R!1#9I@&__arith;R$__x3;R+0$__x2;R+0$__x1;R+0&__wit;R!3,^P+C!2,^T!3,^R+0!3,^X+0!2,^Y+0!1,^C,P!2,^S+0}3!2,^S+0,^W,^ZLM&__varmap;R!4,^;+0_3#2!2,E+0#4O&__ff;R!8,^1P'I+J+J,K!8,^1P'I+J+J,K_5^P!7,GP'I+J+J,K!4,L+0^Q,^5_6,U^P!8,^1P'I+J+J,K!7,GP'I+J+J,K!4,L+0!3,^<+0U_6,TQ,U^P!8,^1P'I+J+J,K!7,^2P'I+J+J,K_5!7,GP'I+J+J,K!4,L+0_4,^4^K,U^P!7,GP'I+J+J,K!4,L+0!3,^<+0V_6,T!3,M+0T!3,M+0_6S,UWX%__x3;R+0%__x2;R+0%__x1;R+0%~R%~R4!2'6,<#3%~R!3+9+0!2'^=#2#37%~R!2+1!2'2,<#5!2'2#52!3+9+0!2'^=!2':#4R#5!2':Y!2':#5R!6#1#C_7!2'46!2':2#C#4#<#B^3!1'_Q#7\^0^<!1'_Q^;_8!3'_1^<#7^U!3+9+0_8^4!6'^>+0!2'_0!1'_P^?#8$z;R+0!3+9+X!2'_U#1#4!2'_T!2'_W#9#4!2'_X#42&b;R_9_:&b0;R_;+X-_ZRN$b;R+X$~R!3+_Z!2'6#6#;!2'2#;#6#1!3+9+X_=_?#22$~R_@!1$Hik;R_A!6'7+X,_[_D&b;R_E_F&b0;R_B+X-_ZRN$b;R+X$~R!3+_Z!2'2#?#:!2'6#:#?#1!3+9+X,_[_H#22$~R_I!1$H0;R_J&__sat3;R_K_M&__sat2;R_N_O&__sat1;R_P_S&__sat2;RJ_T&__arith;R$__p1;Rw$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K_W^P!8,^1P'I+J+J,K_X^P_YWX%__p1;Rw%__x2;R+0%__x1;R+0%~R!2'2#2#1%~R_Z#5!5#1!3+9+X,_[!2'_T,Y_[#E#@#6#:#1$~R_\!1$H0;R`0!2,?+X`1#1_=!4'`0_<#<#7`6#1$~R`7!1$Hik;R`8!6'7+X!2'_U_<!2':#7#<_D&b;R_E_F&b0;R_B+X-_ZRN$b;R+X$~R!3+_Z!2'2#?#:!2'6#:#?#1!3+9+X`9_H#22$~R_I!1$H0;R_Jvd&b;R!2'_Y#;2!3+_Z!2'6#;2!2'22#;_G&b0;R`:+X-_ZRN$b;R+X$~R!3+_Z!2'6#>2!2'22#>#1!3+9+X!2'_U!1'_P`;`<#2#22$~R!2'6#=2!1$H1;R`=!3'`1`;`<&__sat4;R`>`@&__sat3;R`A`C&__sat2;R`D`F&__sat3;RJ`G&__arith;R$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K`H^P!8,^1P'I+J+J,K_W^P!7,^2P'I+J+J,K!7,GP'I+J+J,K!4,L+0^Q,^4`I,U!7,GP'I+J+J,K!4,L+0`I,^5!3,M+0^K_6,UWX%__x2;R+0%__x1;R+0%~R`J%~R`K!2+1!2'2,<`L!2'6`L!2':2#4!4#1#I#D#6#>#1$~R!2'22#=!1$H1;R`M!3'`2`;`<&__sat4;R`>`@&__sat3;R`A`C&__sat2;R`D`F&__sat3;RJ`G&__arith;R$__p1;Rw$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K!7,GP'I+J+J,K!4,L+0^K,^4_6,U^P!8,^1P'I+J+J,K!7,^2P'I+J+J,K_Y^O^P!7,^2P'I+J+J,K^R!7,GP'I+J+J,K!4,L+0^L,^4!3,M+0_6U,UWX%__p1;Rw%__x2;R+0%__x1;R+0%~R`N%~R!2+1#4!2'2#22!2+1!2'2,<`O!2'2`O!2':#4#3!5#1`P#D#I#6#H#1!3+9+X`9`Q#1$~R_\!1$H0;R`0&__sat3;R_K_M&__sat2;R_N_O&__sat1;R_P_S&__sat2;RJ_T&__arith;R`R`S!5#1!3+9+X!2'_U!1'_P!2':2#E!2':#@#E!2'_T,_[_[#E#@#6#:#1_=!5'`3_<#<#7&__sat2;R`2`4&__sat1;R^X^Y&__sat0;R^Z_0&__sat1;RJ_1&__arith;R$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!8,^1P'I+J+J,K^S^P^SWX%__x1;R+0%~R0^T!2#1#<#;&__sat2;R`2`4&__sat1;R^X^Y&__sat0;R^Z_0&__sat1;RJ_1&__arith;R$__x2;R+0$__x1;R+0&__wit;RLM&__varmap;R_VO&__ff;R!8,^1P'I+J+J,K`T^P`TWX%__x2;R+0%__x1;R+0%~R!2'2#1#2!2'2#2#3!3#1#<#A#6#1^8#1!3+9+X^5!2'_T!2'_W#7#2!2'_X#22!6'7+X!2'_T!2'_W#8#3!2'_X#32$b;R+X!3+9+X!2'_T`U#1!2'_T`U!2'_U\#4&b;R_9_:&b0;R_;+X-_ZRN$b;R+X$~R!3+_Z!2'6#6#;!2'2#;#6#1!3+9+X!2'_T`V_?!2'_T`V!2'_U\#7#22$~R_@!1$Hik;R_A&H0;R&H0;R!4'`4#=#<#7`6!3+9+X!2'_U!2'\#=Z#7`V!6'^>+X!2'_U`3#8$b;R+X!3+9+X#1,_[!6'7+0,<$z;R+0!3+9+X!2'_U#1#9,_[!1'`5#8`3#:`W#1!3+9+X`V,_[!6'7+X,_[$b;R+X!3+9+X!2'_T#1!2'_T!2'_W#>#9!2'_X#92!2'_T#1`X!6'7+X,_[$b;R+X!3+9+X#1!2'_T,_[`X!6'7+X,_[$b;R+X!3+9+X,_[#1`Y!2'_T,_[`Z!1'`6`Z!2'_T,_[_C!1'`6_C`W#1#1$~R`7!1$Hik;R`8&b;R_E_F&b0;R_B+X!1-_ZRN$b;R+X$~R!3+_Z!2'2#?#:!2'6#:#?#1%E;R!3+9+X`[_H!3+9+X!2'_T`\!2'_T#3`:a0#22$~R_I!1$H0;R_J$E;R!3+9+X`[`Qvd&b;R!2'_Y#<2!3+_Z!2'6#<2!2'22#<`:&b0;R!2'_X#=2+X!1-_ZRN$b;R+X$~R!3+_Z!2'6#?2!2'22#?#1%E;R!3+9+Xa1!2'_T,Y#2!3+9+X!2'_Ta2#3a4#22$~R`=!1$H1;R!2'6#?2$E;R!3+9+Xa1!2'_T,Y,Y!6'7+X,Y$b;R+X!3+9+X!2'_Ta5,Ya6!6'7+Xa2a7!2,?+Xa2!2'_Ta2,Y!1'`7a2a3!3'`12#A&__sat4;Ra9a:&__sat3;Ra;a<&__sat2;Ra=a?&__sat3;RJa@&__arith;R$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!8,^1P'I+J+J,K`H^P!8,^1P'I+J+J,K^S^P!7,^2P'I+J+J,K^S`HWX%__x1;R+0%~R`J%~R^T!2+14!2'6#32!3#1#F#7#E#1$~R`M!1$H1;R!2'22#?$E;R!3+9+Xa1!2'_T,Y,_[!6'7+X,_[$b;R+X!3+9+X!2'_Ta5,_[a6!6'7+X,_[a7`Y!2'_Ta2,_[!1'`8a2a3!3'`22#A&__sat4;Ra9a:&__sat3;Ra;a<&__sat2;Ra=a?&__sat3;RJa@&__arith;R$__x1;R+0&__wit;RLM&__varmap;RNO&__ff;R!8,^1P'I+J+J,KaA^P!7,^2P'I+J+J,KaBaAWX%__x1;R+0%~R!2'22#1!2+1?`N!2#1#F#7#1#3!3+9+X!2'_T`\!2'_T,Y`:a0#1$~R_\!1$H0;R`0$E;R!3+9+X`[`1&__sat3;R!3'^G#B_L#?%~R!2'2,<_L!2'2,<!2'\#C!2'46#B&__sat2;R!2';6#B%~R>_T&__sat1;R$Ha;RB$~R+=!3'>6#E#2%Ha;RB%~R+=!2'2,<`?&__sat2;RJ%~R!2'2,<#D!2'6,<`?&__arith;R`R`S!5#1!3+9+X!2'_Ta2!2'_T,_[!2'_X#A2a4#F#A#7#;#1#7#1^9#1!2'_U^6#2!3'`9#8\#2!2'\#87!3'`:#82&__sat2;R^C^D&__sat1;R^E^F&__sat0;R^G^I&__sat1;RJ^J&__arith;R&__wit;RLM&__varmap;R_UO&__ff;RaBWX?#1!2'_U!2'_R#8^4#2!3'`9#8^4#2:#1").
Qed.
Lemma prod32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (0 <= a * b < 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^00!2'2,<#2|10;!1,51|500;!1,53!2'424!2+10!2'6#25!2'^=#4#3|600;!1,58!2'429!2';24!2'6,<2%~R!2'2,<4!2'6,<5%~R<=!2'2,<2$Ha;R?$~R+=!3'>24#2%Ha;R?%~R+=!2'2,<5vd!2,?+@!2'A,<2<!1#2B!1,B+C!1+D+C!2,E+0#2!1+F+0!1+H+0!2,O+0,P!7,GH'I+J+J,K!4,L+0!2,R+0,<,^4I,U!6,^[H'I+J+J,K#4!1,^6+J!2'VH,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2$__p1;Rw$__x1;R+0&__wit;RDE&__varmap;RFG&__ff;R!8,^1H'I+J+J,K!7,^2H'I+J+J,KJKLJMN%__p1;Rw%__x1;R+0%~R!2+1!2'2,<#1#20&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;ROP!3#1!2'6#85#8#6&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;ROP!3#1!2'6#75#7#5!1,5,P!2':5S!2,R+02!3,Q+0U!1,S3!3,M+0V!2,R+0S$__p1;Rw$__x1;R+0&__wit;RDE&__varmap;RFG&__ff;R!8,^1H'I+J+J,K!7,^2H'I+J+J,KK!7,GH'I+J+J,K!4,L+0I,^5V,UL!7,GH'I+J+J,K!4,L+0I,^4W,UMN%__p1;Rw%__x1;R+0%~R!2+1#2!2'6#15!2'2#2T!2'^=TT%~R!2'2,<9!2'6,<:!3,^<+0I!2,O+01$a;R+0$b;R+0$Ha;R6$Hb;R6!4,`;!2'2,<7!2'67:!4'`<#4#3QR&H;R!8'`=#4T#3TQ&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;RXY!3#1!2'2,<#8#8#6R&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;RXY!3#1!2'2,<#7#7#5!2'27Z&__sat3;R;>&__sat2;R@A&__sat1;R!2';29%~R<[&__sat0;R$Ha;R?$~R+=!3'>29#2%Ha;R?%~R+=!2'2,<:&__sat1;RC[&__sat3;R!1#5B=&__arith;R$__x2;R+0$__x1;R+0&__wit;RDE&__varmap;R!4,^;+0!2,E+0#3#2!1,^@+0G&__ff;R!8,^1H'I+J+J,K!7,GH'I+J+J,K!4,L+0\,^4!3,^<+0WW,UL!7,GH'I+J+J,K!4,L+0\,^5!3,Q+0U!1,S8,UMN%__x2;R+0%__x1;R+0%~R!2'2!2'^=#1#2Z!2'6!2'^=#2#3:!3#1#;#<#8").
Qed.
Lemma hi32 : forall x, (0 <= x < 2 ^ 64)%Z -> (0 <= Z.shiftr x 32 < 2 ^ 32)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S\0!2'2,<#1|10;!1,51|600;!1,53!2'424!2'6#15|500;!1,57!2'428!2'^7#29!2';24!2'6,<2%~R!2'2,<4!2'6,<5%~R<=!2'2,<2$Ha;R?$~R+=!3'>24#2%Ha;R?%~R+=!2'2,<5vd!2,?+@!2'A,<2<!1#2B!1,B+C!1+D+C!2,E+0#2!1+F+0!1+H+0!2,R+0,<!2,O+0,P!7,GH'I+J+J,K!4,L+0I,^4J,U!6,^[H'I+J+J,K#4!1,^6+J!2'VH,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2!2';28!2'2,<8!2'6,<9%~RQR%~R<S$Ha;R?$~R+=!3'>28#2%Ha;R?%~R+=!2'2,<9!1#5B!1,^@+0!2,R+02!3,Q+0Y!1,S7&__sat3;RPT&__sat2;RUV&__sat1;R;>&__sat0;R@A&__sat1;RC=&__sat3;RWS&__arith;R&__wit;RDE&__varmap;RXG&__ff;R!7,GH'I+J+J,K!4,L+0I,^5Z,UNOR#1$x;R+0$Hx;R!2+106!6'7+0:$z;R+0!2+10!2'6#19!4,`;!2'2,<:!2'6:9!4'`>#29&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;R$__p1;Rw$__x1;R+0&__wit;RDE&__varmap;RFG&__ff;R!8,^1H'I+J+J,K!7,^2H'I+J+J,KKLMKNO%__p1;Rw%__x1;R+0%~R!2+10#2!2'2,<#2!3#1!2'6#65#6#5[!5'`?#299[&__sat3;RPT&__sat2;RUV&__sat1;R;>&__sat0;R@A&__sat1;RC=&__sat3;RWS&__arith;R$__p1;Rw$__x1;R+0&__wit;RDE&__varmap;RFG&__ff;R!8,^1H'I+J+J,K!7,^2H'I+J+J,KL!7,GH'I+J+J,K!4,L+0J,^5!3,Q+0Y!1,S3,UM!7,GH'I+J+J,K!4,L+0J,^5!3,^<+0ZZ,UNO%__p1;Rw%__x1;R+0%~R!2+1#26!2'6#2!2'^=99!3#1!2'2,<#9#9#8!2'_<#28!3'`@#28&__sat1;R;>&__sat0;R@A&__sat1;RC=&__arith;R&__wit;RDE&__varmap;RXG&__ff;R!7,GH'I+J+J,K!4,L+0I,^4!2,R+08,UNOQ#1").
Qed.
Lemma lo32_of_shl : forall x, (0 <= x)%Z -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32 = x mod 4294967296)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|10;!1,50|500;!1,52!2'413!2'^=#24!1,5|^C0000000000000000;|P00000000;!1,57!2'\#38!2'\56!2'^=44!2'\#48!2'\#34!2'^==4!2'6,<1!2'2,<3%~R@!2'6,<4!2'2,<1!1,B+C!1+D+C!1,^@+0!1+F+0!1+H+0!2,R+0,<!2'VG,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2&__sat1;R!2';13%~R?A&__sat0;R$Ha;RB$~R+=!3'>13#2%Ha;RB%~R+=!2'2,<4&__sat1;R!1#2vd!2,?+@!2'A,<1?A&__arith;R&__wit;RCD&__varmap;REF&__ff;R!6,^AG'I+J+J,K!7,GG'I+J+J,K!4,L+0!3,Q+0!2,R+01!1,S2,TH,UIJ%~R!3+9+04,<+^B#1&__arith;R&__wit;RCD&__varmap;REF&__ff;R!7,GG'I+J+J,K!4,L+0H,^4!2,R+03,UIJ@#1$x;R+0$Hx;R!2'2,<#1!6'7+05$z;R+0!3+9+0!2'_<!2'\#1639!6'7+0!2'^7:4$z;R+0!3+9+0#19&H;R!2,?+06!3+9+0;6!6'^>+0;$z;R+0!3+9+0!2'^7!2'\!2'^=#44#14<!6'7+0>$z;R+0!3+9+0!2'^7#14<!6'7+0=$z;R+0!3+9+0#1<!2,?+09!2'^7>4!3'`A=4K!2'\!2'^=#34;!5'`B#344KK6#1!2'_<:3!3'`@:3L!2'_0#23!3'_1#23L").
Qed.
Lemma mulhu_shl32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (Z.shiftr ((a * 4294967296) * (b * 4294967296)) 64 = a * b)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SZ0|10;!1,50|500;!1,52!2'413!2+1!2'2,<#2!2'6#24!1,5|P00000000;!2'^=#46!2'^=7!2'^=#36|600;!1,59!2'41:!2'^=#5#4!1+`D+0!2+`C==!2,`H+0,P!2,`H+00!3,`G+0!3,`G+0?@!3,`I+0!2,`J+01!1'`K:!2,`J+06!3,`G+0!3,`G+0?B!3,`G+0@B!2,?+X,Y!1,5,P!3+9+0!2'^=!2'^=#4#3;8!2';13!2'6,<1%~R!2'2,<3!2'6,<4%~RHI!2'2,<1$Ha;RK$~R+=!3'>13#2%Ha;RK%~R+=!2'2,<4!2'2,<:%~RN!2'6,<;vd!2,?+@!2'A,<1H!1#2P!1,B+C!1+D+C!1,^@+0!1+F+0!1+H+0!2,R+0,<!2'VV,K!4'W#1#3vvD!3+9+X!2'Z#1#3,Y!3'[+0,<#2$a;R+0$b;R+0$Ha;R5$Hb;R5!6'7+0!2'^78;$z;R+0!3+9+0#1<&H;Rvd&hyp_list;R!1,B>!1+D>&fv_list;R!3,^P+0#5!3,^P+0#4!1,B+0!1+D+0!7'`E'`F#1#2AC,^NvvD!3+9+X&lmp;R!:'`L+0,<E'8'^=':'3'`M'`N#2!1+D!2+`C!2+`C+0+`O!1+`P+0!4'`Q+0'`M!<'`R+0,<E'8'^=':'3'`M'`N'`F#1A!<'`R+0,<E'8'^=':'3'`M'`N'`F#1C,YFF!6'^>+0!2'^=<;$z;R+0!3+9+0!2'^7#1;!2'^=#6#5!3'`A<;&__sat3;RGJ&__sat2;RLM&__sat1;R!2';1:%~RHO&__sat0;R$Ha;RK$~R+=!3'>1:#2%Ha;RK%~R+=!2'2,<;&__sat1;RQO&__sat3;R!1#5PI&__arith;R&__wit;RRS&__varmap;RTU&__ff;R!6,^AV'I+J+J,K!7,GV'I+J+J,K!4,L+0!3,Q+0!2,R+01!1,S9,TW,UXY%~R!3+9+0;,<+^B#1!2'^=!2'^=#567#1!2'_<8:!3'`@8:&__sat1;RGJ&__sat0;RLM&__sat1;RQI&__arith;R&__wit;RRS&__varmap;RTU&__ff;R!7,GV'I+J+J,K!4,L+0W,^4!2,R+0:,UXYN#1").
Qed.

Lemma shl32_mod : forall x, (0 <= x)%Z -> ((Z.shiftl x 32) mod 18446744073709551616 = (x mod 4294967296) * 4294967296)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SA0|10;|500;!1,51!2'4!1,502!1,5|^C0000000000000000;|P00000000;!1,55!2'^=33!1,B+C!1+D+C!1,^@+0!1+F+0!1+H+0!2,R+0,<!2'V<,K!4'W#1#3vv!2,?+X,Y!3+9+X!2'Z#1#3,Y!3'[+0,<#2&__arith;R&__wit;R89&__varmap;R:;&__ff;R!6,^A<'I+J+J,K!7,G<'I+J+J,K!4,L+0!2,R+06,T=,U>?%~R!3+9+06,<+^B#1$x;R+0$Hx;R!2'2,<#1!6'7+0!2'^=#23$z;R+0!3+9+0!2'\#14!2'^=!2'\#366&H;R!2,?+04!3+9+074!6'^>+07$z;R+0!3+9+0!2'\!2'^=#43#1!2'^=!2'\#466!5'`B#366@@4#1!2'_0#22!3'_1#22&__arith;R&__wit;R89&__varmap;R:;&__ff;R!7,G<'I+J+J,K!4,L+0=,^4!2,R+02,U>?!2'2,<2#1").
Qed.

Notation rsegs := DgWalkX_u5.rsegs.

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
Ltac dg_lia := first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].
Ltac dg_norm :=
  rewrite ?Z.add_0_r;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by dg_lia end;
  repeat match goal with |- context [v_divuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_divuw_small x y) by dg_lia end;
  repeat match goal with |- context [v_remuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_remuw_small x y) by dg_lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl x y) by dg_lia end;
  repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by dg_lia end;
  repeat match goal with |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by dg_lia end;
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) by dg_lia end;
  repeat match goal with |- context [Z.ltb ?a ?b] =>
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
Ltac dg_xstep := first [ zstep; dg_u8fix; dg_norm | if_true | if_false | dg_hs; zstep; dg_u8fix; dg_norm
                       | dg_rd; zstep; dg_u8fix; dg_norm ].
Ltac dg_inl x l := lazymatch l with cons ?y ?r => first [constr_eq x y | dg_inl x r] | nil => fail end.
Ltac dg_at l := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?x) _ _ _ _) => dg_inl x l end.
Ltac dg_run l := repeat (tryif dg_at l then fail else dg_xstep).
Ltac dg_swrap_in K :=
  unfold bv_swrap, bv_wrap in K;
  try change (bv_half_modulus 32%N) with 2147483648%Z in K; try change (bv_modulus 32%N) with 4294967296%Z in K;
  try change (bv_half_modulus 64%N) with 9223372036854775808%Z in K; try change (bv_modulus 64%N) with 18446744073709551616%Z in K.
Ltac dg_prune K := exfalso; rewrite ?land3_mod4, ?land7_mod8 in K;
  repeat match type of K with context [bv_signed (Z_to_bv 64 ?x)] =>
    rewrite (sgn_small64 x) in K by (first [lia | Z.div_mod_to_equations; nia]) end;
  first [ lia | dg_swrap_in K; Z.div_mod_to_equations; lia ].
Ltac dg_solve d l :=
  lazymatch d with
  | O => fail 100 "dg_solve: out of fuel"
  | S ?d' =>
    dg_run l;
    tryif dg_at l then idtac
    else lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "K" in if_cases K; zify_cond K;
        [ first [ dg_prune K | dg_solve d' l ] | first [ dg_prune K | dg_solve d' l ] ]
    end
  end.
Lemma swrap32_m64 : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 (x mod 18446744073709551616) = x.
Proof.
  intros x Hx. rewrite Z.mod_eq by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616))%Z
    with (x + (- (4294967296 * (x / 18446744073709551616))) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod. apply swrap32_small. exact Hx.
Qed.
Ltac g3_lia := lia.
Lemma land_pow2_testbit : forall a n, (0 <= n)%Z -> Z.land a (2 ^ n) = (if Z.testbit a n then 2 ^ n else 0)%Z.
Proof.
  intros a n Hn. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec n k) as [<-|Hne].
  - destruct (Z.testbit a n); [rewrite Z.pow2_bits_true by lia | rewrite Z.bits_0]; reflexivity.
  - rewrite andb_false_r. destruct (Z.testbit a n); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.
Lemma land52_cases : forall x, (0 <= x < 2 ^ 53)%Z ->
  (x < 2 ^ 52 /\ Z.land x 4503599627370496 = 0)%Z \/ (2 ^ 52 <= x /\ Z.land x 4503599627370496 = 4503599627370496)%Z.
Proof.
  intros x Hx. change 4503599627370496%Z with (2 ^ 52)%Z. rewrite land_pow2_testbit by lia.
  pose proof (Z.testbit_spec' x 52 ltac:(lia)) as T.
  assert (B : (0 <= x / 2 ^ 52 < 2)%Z).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (Z_lt_le_dec x (2 ^ 52)) as [L|L].
  - left. rewrite (Z.div_small x (2 ^ 52)) in T by lia.
    destruct (Z.testbit x 52); cbn in T; [discriminate | split; [exact L | reflexivity]].
  - right. assert (Q : (x / 2 ^ 52 = 1)%Z).
    { assert (1 <= x / 2 ^ 52)%Z by (apply Z.div_le_lower_bound; lia). lia. }
    rewrite Q in T. destruct (Z.testbit x 52); cbn in T; [split; [exact L | reflexivity] | discriminate].
Qed.
Lemma land52_0 : forall x, (0 <= x < 2 ^ 53)%Z -> Z.land x 4503599627370496 = 0%Z -> (x < 2 ^ 52)%Z.
Proof. intros x Hx H. destruct (land52_cases x Hx) as [[A _]|[_ B]]; [exact A | rewrite B in H; discriminate]. Qed.
Lemma land52_1 : forall x, (0 <= x < 2 ^ 53)%Z -> Z.land x 4503599627370496 <> 0%Z -> (2 ^ 52 <= x)%Z.
Proof. intros x Hx H. destruct (land52_cases x Hx) as [[_ B]|[A _]]; [contradiction | exact A]. Qed.
Lemma swrap32_sub64 : forall x y, bv_swrap 32 (x mod 18446744073709551616 - y mod 18446744073709551616) = bv_swrap 32 (x - y).
Proof.
  intros x y. rewrite !(Z.mod_eq _ 18446744073709551616) by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616) - (y - 18446744073709551616 * (y / 18446744073709551616)))%Z
    with ((x - y) + (4294967296 * (y / 18446744073709551616 - x / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  apply swrap32_mod.
Qed.
Lemma swrap32_add64 : forall x y, bv_swrap 32 (x mod 18446744073709551616 + y mod 18446744073709551616) = bv_swrap 32 (x + y).
Proof.
  intros x y. rewrite !(Z.mod_eq _ 18446744073709551616) by lia.
  replace (x - 18446744073709551616 * (x / 18446744073709551616) + (y - 18446744073709551616 * (y / 18446744073709551616)))%Z
    with ((x + y) + (- (4294967296 * (x / 18446744073709551616 + y / 18446744073709551616))) * 2 ^ 32)%Z by lia.
  apply swrap32_mod.
Qed.
Lemma sub_mod64 : forall x y, ((x mod 18446744073709551616 - y mod 18446744073709551616) mod 18446744073709551616 = (x - y) mod 18446744073709551616)%Z.
Proof. intros x y. symmetry. apply Zminus_mod. Qed.
Lemma add_mod64 : forall x y, ((x mod 18446744073709551616 + y mod 18446744073709551616) mod 18446744073709551616 = (x + y) mod 18446744073709551616)%Z.
Proof. intros x y. symmetry. apply Zplus_mod. Qed.
Lemma zbv_sub64 : forall x y, Z_to_bv 64 (x mod 18446744073709551616 - y mod 18446744073709551616) = Z_to_bv 64 (x - y).
Proof. intros x y. apply zbv_eqm. change 18446744073709551616%Z with (2 ^ 64)%Z. rewrite <- Zminus_mod. reflexivity. Qed.
Lemma zbv_add64 : forall x y, Z_to_bv 64 (x mod 18446744073709551616 + y mod 18446744073709551616) = Z_to_bv 64 (x + y).
Proof. intros x y. apply zbv_eqm. change 18446744073709551616%Z with (2 ^ 64)%Z. rewrite <- Zplus_mod. reflexivity. Qed.
Lemma swrap32_subl : forall x y, bv_swrap 32 (x - y mod 18446744073709551616) = bv_swrap 32 (x - y).
Proof.
  intros x y. rewrite (Z.mod_eq y 18446744073709551616) by lia.
  replace (x - (y - 18446744073709551616 * (y / 18446744073709551616)))%Z
    with ((x - y) + (4294967296 * (y / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  apply swrap32_mod.
Qed.
Lemma sub_mod64_r : forall x y, ((x - y mod 18446744073709551616) mod 18446744073709551616 = (x - y) mod 18446744073709551616)%Z.
Proof. intros x y. apply Zminus_mod_idemp_r. Qed.
Lemma zbv_mod64 : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros x. apply zbv_eqm. change 18446744073709551616%Z with (2 ^ 64)%Z. apply Z.mod_mod. lia. Qed.
Lemma mod_neg64 : forall x, (- 18446744073709551616 <= x < 0)%Z -> (x mod 18446744073709551616 = x + 18446744073709551616)%Z.
Proof.
  intros x Hx. rewrite <- (Z.mod_small (x + 18446744073709551616) 18446744073709551616) by lia.
  replace (x + 18446744073709551616)%Z with (x + 1 * 18446744073709551616)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Ltac g3_modn_goal := repeat match goal with |- context [Z.modulo ?x 18446744073709551616] =>
  first [ rewrite (Z.mod_small x 18446744073709551616) by lia | rewrite (mod_neg64 x) by lia ] end.
Ltac g3_modg := repeat match goal with |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia end.
Ltac g3_modn_in K := repeat match type of K with context [Z.modulo ?x 18446744073709551616] =>
  first [ rewrite (Z.mod_small x 18446744073709551616) in K by lia | rewrite (mod_neg64 x) in K by lia ] end.
Ltac g3_freg := repeat match goal with
  | H : bv_unsigned (reg_get ?F0 ?r0) = ?bb |- context [bv_unsigned (reg_get ?FF ?r)] =>
      is_var bb; rewrite (H : bv_unsigned (reg_get FF r) = bb)
  end.
Ltac g3_swk := repeat match goal with H : bv_swrap 32 ?e = ?v |- context [bv_swrap 32 ?e] => rewrite H end.
Ltac g3_swk_in K := repeat match goal with H : bv_swrap 32 ?e = ?v |- _ =>
  lazymatch type of K with context [bv_swrap 32 e] => rewrite H in K end end.
Ltac g3_norm :=
  g3_freg; g3_swk; rewrite ?zbv_sub64, ?zbv_add64, ?zbv_mod64, ?swrap32_sub64, ?swrap32_add64, ?sub_mod64, ?add_mod64;
  rewrite ?Z.add_0_r;
  rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  repeat match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_small x) by g3_lia end;
  repeat match goal with |- context [v_divuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_divuw_small x y) by g3_lia end;
  repeat match goal with |- context [v_remuw (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] => rewrite (v_remuw_small x y) by g3_lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?y)] => rewrite (swrap32_modl x y) by g3_lia end;
  repeat match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616)] => rewrite (swrap32_m64 x) by g3_lia end;
  repeat match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by g3_lia end;
  repeat match goal with |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor63 x) by g3_lia end;
  repeat match goal with |- context [Z.ltb ?a ?b] =>
    first [ rewrite (proj2 (Z.ltb_lt a b)) by g3_lia | rewrite (proj2 (Z.ltb_ge a b)) by g3_lia ] end;
  cbn [Z.b2z]; rewrite ?Z.lxor_0_l, ?Z.lxor_0_r.
Ltac g3_xstep := first [ zstep; dg_u8fix; g3_norm | if_true | if_false | dg_hs; zstep; dg_u8fix; g3_norm
                       | dg_rd; zstep; dg_u8fix; g3_norm ].
Ltac g3_run l := repeat (tryif dg_at l then fail else g3_xstep).
Lemma lor52 : forall x, (0 <= x < 2 ^ 52)%Z -> Z.lor x 4503599627370496 = (x + 4503599627370496)%Z.
Proof.
  intros x Hx. assert (L : Z.land x 4503599627370496 = 0%Z).
  { destruct (land52_cases x ltac:(lia)) as [[_ B]|[A _]]; [exact B | lia]. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.
Lemma div0_lt : forall x c, (0 < c)%Z -> (0 <= x)%Z -> (x / c = 0)%Z -> (x < c)%Z.
Proof. intros x c Hc Hx H. destruct (Z_lt_le_dec x c) as [L|L]; [exact L|]. assert (1 <= x / c)%Z by (apply Z.div_le_lower_bound; lia). lia. Qed.
Lemma div0_ge : forall x c, (0 < c)%Z -> (0 <= x)%Z -> (x / c <> 0)%Z -> (c <= x)%Z.
Proof. intros x c Hc Hx H. destruct (Z_lt_le_dec x c) as [L|L]; [|exact L]. exfalso. apply H. apply Z.div_small. lia. Qed.
Definition g3_mk (P : Prop) : Prop := P.
Ltac g3_mdk_in K := repeat match goal with H : g3_mk (?e mod 18446744073709551616 = ?v)%Z |- _ =>
  lazymatch type of K with context [e mod 18446744073709551616] => rewrite (H : (e mod 18446744073709551616 = v)%Z) in K end end.
Ltac g3_kfix K :=
  try (g3_swk_in K);
  try (g3_mdk_in K);
  try (match type of K with context [bv_unsigned (reg_get ?FF ?r)] =>
    lazymatch goal with
    | H : bv_unsigned (reg_get FF r) = _ |- _ => idtac
    | H : bv_unsigned (reg_get _ _) = ?bb |- _ => assert (bv_unsigned (reg_get FF r) = bb) by exact H
    end end);
  try (rewrite ?swrap32_sub64, ?swrap32_add64, ?sub_mod64, ?add_mod64, ?Zmod_mod in K);
  try (rewrite ?swrap32_subl, ?sub_mod64_r in K);
  try (repeat match type of K with context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) in K by lia end);
  try (lazymatch type of K with
    | Z.land ?x 4503599627370496 = 0%Z => apply (land52_0 x ltac:(lia)) in K
    | Z.land ?x 4503599627370496 <> 0%Z => apply (land52_1 x ltac:(lia)) in K
    end);
  try (lazymatch type of K with
    | (?x / ?c = 0)%Z => is_Zlit c; apply (div0_lt x c ltac:(lia) ltac:(lia)) in K
    | (?x / ?c <> 0)%Z => is_Zlit c; apply (div0_ge x c ltac:(lia) ltac:(lia)) in K
    end);
  try (repeat match type of K with context [bv_swrap 32 (?x mod 18446744073709551616)] => rewrite (swrap32_m64 x) in K by lia end);
  try (repeat match type of K with context [bv_swrap 32 ?x] => rewrite (swrap32_small x) in K by lia end);
  try (repeat match type of K with context [bv_signed (Z_to_bv 64 ?x)] => rewrite (sgn_small64 x) in K by lia end).
Lemma g3_mod_sub_lt : forall a b, (0 <= a < 18446744073709551616)%Z -> (0 <= b < 18446744073709551616)%Z ->
  (a - b <> a mod 18446744073709551616 - b mod 18446744073709551616)%Z -> False.
Proof. intros a b Ha Hb H. rewrite !Z.mod_small in H by lia. lia. Qed.
Ltac g3_isar T := lazymatch T with
  | (_ <= _)%Z => idtac | (_ < _)%Z => idtac | (_ <= _ < _)%Z => idtac | (_ <= _ <= _)%Z => idtac
  | (_ < _ < _)%Z => idtac | (_ < _ <= _)%Z => idtac | @eq Z _ _ => idtac | ~ (@eq Z _ _) => idtac
  end.
Ltac g3_mprune K := lazymatch type of K with
  | context [Z.modulo ?x 18446744073709551616] =>
      first [ rewrite (Z.mod_small x 18446744073709551616) in K by lia
            | rewrite (mod_neg64 x) in K by lia ]; first [ lia | g3_mprune K ]
  end.
Ltac g3_prune K := exfalso; rewrite ?land3_mod4, ?land7_mod8 in K; g3_kfix K;
  first [ lia | g3_mprune K ].
Ltac g3_kn K := g3_kfix K.
Ltac g3_hnorm := repeat match goal with
  | H : context [Z.modulo ?x 18446744073709551616] |- _ =>
      lazymatch type of H with
      | (_ <= _)%Z => idtac | (_ < _)%Z => idtac | (_ = _)%Z => idtac | (_ <> _)%Z => idtac
      end;
      rewrite (Z.mod_small x 18446744073709551616) in H by lia
  end.
Ltac g3_solve_k d l lastK :=
  lazymatch d with
  | O => fail 100 "g3_solve: out of fuel"
  | S ?d' =>
    g3_run l;
    tryif dg_at [0x4484c]%Z then (let T := type of lastK in fail 100 "g3_solve: check exit after" T)
    else tryif dg_at l then (try (g3_hnorm; exfalso; lia))
    else lazymatch goal with
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "K" in if_cases K; zify_cond K;
        [ first [ g3_prune K | let KR := fresh "KR" in pose proof K as KR; g3_kn K; g3_solve_k d' l KR ] | first [ g3_prune K | let KR := fresh "KR" in pose proof K as KR; g3_kn K; g3_solve_k d' l KR ] ]
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => let T := type of lastK in fail 100 "g3_solve: stuck at" pc "after" T
    end
  end.
Ltac g3_solve d l := g3_solve_k d (0x4484c%Z :: l) I.
Ltac g3_cmpR R E :=
  lazymatch R with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
  lazymatch E with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
    first [ unify x1 y1; unify x2 y2; unify x3 y3; unify x4 y4; unify x5 y5; unify x6 y6; unify x7 y7; unify x8 y8; unify x9 y9; unify x10 y10; unify x11 y11; unify x12 y12; unify x13 y13; unify x14 y14; unify x15 y15; unify x16 y16; unify x17 y17; unify x18 y18; unify x19 y19; unify x20 y20; unify x21 y21; unify x22 y22; unify x23 y23; unify x24 y24; unify x25 y25; unify x26 y26; unify x27 y27; unify x28 y28; unify x29 y29; unify x30 y30; unify x31 y31 | fail 100 "register mismatch" ]
  end end.
Ltac g3_fold_R := lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      lazymatch R with
      | TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) => change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
      end
  end.
Ltac g3_head t := lazymatch t with ?f _ => g3_head f | _ => t end.
Ltac g3_eqs := repeat match goal with H : ?x = 0%Z |- context [Z_to_bv 64 ?x] => assert_fails (is_var x); assert_fails (constr_eq x 0%Z); rewrite H end.
Ltac g3_expect E := g3_eqs; lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ _ _) => try g3_fold_R;
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      tryif (lazymatch R with mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac end) then g3_cmpR R E
      else (let h := g3_head R in fail 100 "regfile head" h) end
  | |- ?G => let h := g3_head G in fail 100 "goal head" h
  end.

Section G3.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Definition GSP : Z := bv_unsigned sp.
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis LENR : (4096 <= lenp /\ lenp + 4 <= 2^47)%Z.
Hypothesis KPR : (4096 <= kp /\ kp + 4 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP <= 2^47)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 160 \/ GSP <= buf)%Z.
Hypothesis SEP_L : (lenp + 4 <= GSP - 160 \/ GSP <= lenp)%Z.
Hypothesis SEP_K : (kp + 4 <= GSP - 160 \/ GSP <= kp)%Z.
Hypothesis SEP_BL : (buf + 22 <= lenp \/ lenp + 4 <= buf)%Z.
Hypothesis SEP_BK : (buf + 22 <= kp \/ kp + 4 <= buf)%Z.
Hypothesis SEP_LK : (lenp + 4 <= kp \/ kp + 4 <= lenp)%Z.
Hypothesis LA : (lenp mod 4 = 0)%Z.
Hypothesis KA : (kp mod 4 = 0)%Z.
Definition G3_W : list (Z * Z) := [(GSP - 160, GSP); (buf, buf + 22); (lenp, lenp + 4); (kp, kp + 4)]%Z.
(* [comment removed for export] *)
Definition g3_post : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (res len K : Z) (bs : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch G3_W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ frm0 fc'
    /\ stk rsegs m' (GSP - 160) GSP
    /\ u8arr rsegs m' buf bs /\ length bs = 22%nat /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)
    /\ rw_cells rsegs m' lenp [C4 (Z_to_bv 64 len)] /\ (1 <= len <= 21)%Z
    /\ rw_cells rsegs m' kp [C4 (Z_to_bv 64 K)] /\ (-343 <= K <= 309)%Z
    /\ (res = 0 \/ res = 1)%Z.

Ltac g3_plits := repeat match goal with
  | |- context [(2 ^ ?n)%Z] => is_Zlit n; let v := eval vm_compute in (2 ^ n)%Z in change (2 ^ n)%Z with v
  | H : context [(2 ^ ?n)%Z] |- _ => is_Zlit n; let v := eval vm_compute in (2 ^ n)%Z in change (2 ^ n)%Z with v in H
  end.
Ltac g3_side := first [ eassumption | reflexivity | lia | (intros; repeat split; first [ reflexivity | lia | (exfalso; lia) ]) | (g3_plits; lia) ].
Ltac g3_open := lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "open evt at" pc
  | |- ?G => fail 100 "open side goal" G
  end.

Lemma g3m_wr_at_app : forall m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; (split; [lia | split; [lia | ]]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hl1 & Hw1) & (Ha2 & Hl2 & Hw2)). split; [lia | split; [lia | ]].
    intros i Hi. destruct (Z_lt_le_dec i n1) as [L|L].
    + apply Hw1. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply Hw2. lia.
Qed.
Lemma g3m_u8arr_app : forall m A bs1 bs2,
  u8arr rsegs m A (bs1 ++ bs2) <-> u8arr rsegs m A bs1 /\ u8arr rsegs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite bytes_at_app, app_length, Nat2Z.inj_add.
  rewrite g3m_wr_at_app by lia. tauto.
Qed.
Lemma g3m_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <-> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app, Nat2Z.inj_add.
  rewrite g3m_wr_at_app by lia. split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite cells_bytes_length in B2 by exact W1. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
Lemma g3m_rw_cells_hd : forall m A c cs, rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (g3m_rw_cells_app m A [c] cs) H)). Qed.
Lemma g3m_stk_close : forall m lo A hi cs, stk rsegs m lo A -> rw_cells rsegs m A cs -> (lo <= A)%Z ->
  (A + Z.of_nat (cells_size cs) = hi)%Z -> stk rsegs m lo hi.
Proof. intros m lo A hi cs S C L E. rewrite <- E. exact (stk_release rsegs m lo A cs S C L). Qed.
Ltac g3m_solve_k d l lastK :=
  lazymatch d with
  | O => fail 100 "g3m_solve: out of fuel"
  | S ?d' =>
    g3_run l;
    tryif dg_at [0x4484c]%Z then (let T := type of lastK in fail 100 "g3_solve: check exit after" T)
    else tryif dg_at l then (try (g3_hnorm; exfalso; lia))
    else lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => idtac
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let K := fresh "K" in if_cases K; zify_cond K;
        [ first [ g3_prune K | let KR := fresh "KR" in pose proof K as KR; g3_kn K; g3m_solve_k d' l KR ] | first [ g3_prune K | let KR := fresh "KR" in pose proof K as KR; g3_kn K; g3m_solve_k d' l KR ] ]
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => let T := type of lastK in fail 100 "g3_solve: stuck at" pc "after" T
    end
  end.
Ltac g3m_solve d l := g3m_solve_k d (0x4484c%Z :: l) I.
Ltac g3m_spfix := repeat match goal with |- context [Z_to_bv 64 ?e] =>
  lazymatch e with context [bv_unsigned sp] => idtac end;
  assert_fails (constr_eq e (bv_unsigned sp));
  let E := fresh "E" in assert (E : e = bv_unsigned sp) by lia; rewrite E; clear E end;
  rewrite ?Z_to_bv_lit_self.

(* [comment removed for export] *)
Lemma g3_ret : forall a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' s8' (F' : bvmap 5 word) fc (m : word -> option byte) (res len K : Z) (bs : list byte) j8,
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [C8 (Z_to_bv 64 kp); CB 8 j8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat ->
  rw_cells rsegs m lenp [C4 (Z_to_bv 64 len)] -> (1 <= len <= 21)%Z ->
  rw_cells rsegs m kp [C4 (Z_to_bv 64 K)] -> (-343 <= K <= 309)%Z -> (res = 0 \/ res = 1)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0x447e0) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
     F' (Z_to_bv 64 0x447e0) fc None m (seg_rom rsegs)).
Proof.
  intros a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' s8' F' fc m res len K bs j8
    FRM ST FR MU WM MI BU BL LE Hlen KC HK Hres.
  unfold G3_W in MU. unfold GSP in *.
  assert (IDX : dg_idx buf len) by exact I.
  g3m_solve 6%nat (@nil Z).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
        g3_fold_R; g3m_spfix;
        g3_expect open_constr:(mkR ra sp gp tp _ _ _ s0 s1 (Z_to_bv 64 res) _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _);
        apply evt_done; unfold g3_post, G3_W, GSP;
        do 17 eexists; exists res, len, K; eexists;
        split; [ reflexivity | ];
        repeat match goal with |- _ /\ _ => split end
    end.
  all: try eassumption.
  all: try (eapply g3m_stk_close; [ eassumption | eassumption | lia | cbn [cells_size csize Nat.add]; lia ]).
  all: try (rewrite upd_length; assumption).
  all: try (apply nth_error_upd_same; lia).
  all: try lia.
  all: g3_open.
Qed.

(* [comment removed for export] *)
Lemma g3_call : forall t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' s8' (F' : bvmap 5 word) fc (m : word -> option byte) (Wm W Wp s K0 : Z) (bs : list byte) lj j8,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [C8 (Z_to_bv 64 kp); CB 8 j8; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 K0)] ->
  (56 <= s <= 59)%Z -> (1 <= Wm <= W)%Z -> (W <= Wp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wp + 1)%Z -> (-325 <= K0 <= 307)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0x447e0) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
                             (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 W) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 Wp) (Z_to_bv 64 (2 ^ 32 - s))
                             (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) s3' s4' s5' s6' s7' s8' s9 s10 s11 t3' t4' t5' t6')
                        F' (Z_to_bv 64 0x44d38) fc None m (seg_rom rsegs)).
Proof.
  intros t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' s8' F' fc m Wm W Wp s K0 bs lj j8
    FRM ST FR MU WM MI BU BL LJ KC Hs HWm HWp HWp1 HK0.
  unfold G3_W in MU. unfold GSP in *.
  rewrite <- (firstn_skipn 21 bs) in BU.
  apply g3m_u8arr_app in BU. destruct BU as [BU1 BU2].
  assert (L1 : length (firstn 21 bs) = 21%nat) by (rewrite firstn_length; lia).
  assert (L2 : length (skipn 21 bs) = 1%nat) by (rewrite skipn_length; lia).
  rewrite L1 in BU2.
  pose proof (g3m_rw_cells_hd _ _ _ _ FR) as FK.
  replace (Z_to_bv 64 W) with (Z_to_bv 64 (Wm + (W - Wm))) by (f_equal; lia).
  replace (Z_to_bv 64 Wp) with (Z_to_bv 64 (Wm + (W - Wm) + (Wp - W))) by (f_equal; lia).
  eapply evt_cut; [ eapply DgWalkX_u5.dg_spec | ].
  all: unfold DgWalkX_u5.SP0 in *; rewrite ?unsigned_lit by lia.
  all: try eassumption.
  all: try reflexivity.
  all: try lia.
  all: try (replace (bv_unsigned sp - 96 - 64)%Z with (bv_unsigned sp - 160)%Z by lia; exact ST).
  all: lazymatch goal with
    | |- forall _, _ -> _ =>
        let ms' := fresh "ms'" in let P := fresh "P" in intros ms' P;
        unfold DgWalkX_u5.dg_post, DgWalkX_u5.DG_W, DgWalkX_u5.SP0 in P; rewrite ?unsigned_lit in P by lia;
        destruct P as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' & res & len & kappa & bs' &
                       -> & MUc & WMc & MIc & STc & BUc & BLc & LEc & Hlen & KCc & Hk & Hres)
    | _ => idtac
    end.
  all: lazymatch goal with |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
    rewrite (ret_pc_even 0x447e0) by (first [lia | reflexivity]);
    lazymatch type of STc with stk _ _ ?lo ?hi =>
      replace lo with (bv_unsigned sp - 160)%Z in STc by lia; replace hi with (bv_unsigned sp - 96)%Z in STc by lia end;
    pose proof (rw_cells_transport rsegs _ m m' _ _ FR MUc WMc ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR';
    pose proof (u8arr_transport rsegs _ m m' _ _ BU2 MUc WMc ltac:(cbn [disjoint_from]; rewrite L2; lia)) as BU2';
    assert (MUw : munch [(bv_unsigned sp - 160, bv_unsigned sp); (buf, buf + 22); (lenp, lenp + 4); (kp, kp + 4)]%Z m m')
      by (eapply munch_weaken; [ | exact MUc ]; intros y; cbn [outside]; first [lia | intuition lia]);
    pose proof (munch_trans _ m0 m m' MU MUw) as MU';
    pose proof (wmono_trans rsegs m0 m m' WM WMc) as WM';
    assert (BU' : u8arr rsegs m' buf (bs' ++ skipn 21 bs))
      by (apply g3m_u8arr_app; split; [exact BUc | rewrite BLc; exact BU2']);
    clear BUc;
    eapply (g3_ret a1c a2c a3c a4c a5c a6c a7c t0c t1c t2c t3c t4c t5c t6c)
    | _ => idtac end.
  all: try eassumption.
  all: try (rewrite app_length, BLc, L2; reflexivity).
  all: try lia.
  all: g3_open.
Qed.

Lemma g3m_land32 : forall x, Z.land x 4294967295 = (x mod 4294967296)%Z.
Proof. intros x. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac g3m_mc_tac Lw Lp := unfold mcode; rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 32)%Z with 4294967296%Z;
  rewrite ?Lw, ?Lp, ?g3m_land32; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Lemma g3_mul : forall (acw bcw adw bdw acp bcp adp bdp acm bcm adm bdm : Z) (s mk : Z) (F' : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) lj kj j16 rax a6' s8' t4',
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (0 <= acw <= 18446744065119617025)%Z -> (0 <= bcw <= 18446744065119617025)%Z -> (0 <= adw <= 18446744065119617025)%Z -> (0 <= bdw <= 18446744065119617025)%Z ->
  (0 <= acp <= 18446744065119617025)%Z -> (0 <= bcp <= 18446744065119617025)%Z -> (0 <= adp <= 18446744065119617025)%Z -> (0 <= bdp <= 18446744065119617025)%Z ->
  (0 <= acm <= 18446744065119617025)%Z -> (0 <= bcm <= 18446744065119617025)%Z -> (0 <= adm <= 18446744065119617025)%Z -> (0 <= bdm <= 18446744065119617025)%Z ->
  Z.land bcw 4294965248 = (bcw mod 4294967296)%Z -> Z.land bcp 4294966272 = (bcp mod 4294967296)%Z ->
  (56 <= s <= 59)%Z -> (-307 <= mk <= 325)%Z ->
  (1 <= mcode acm adm bcm bdm)%Z -> (mcode acm adm bcm bdm <= mcode acw adw bcw bdw)%Z -> (mcode acw adw bcw bdw <= mcode acp adp bcp bdp)%Z ->
  (mcode acp adp bcp bdp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= mcode acp adp bcp bdp + 1)%Z ->
  evt rsegs g3_post (MS (mkR rax (Z_to_bv 64 (GSP - 96)) gp tp (Z_to_bv 64 adm) (Z_to_bv 64 4294965248) (Z_to_bv 64 4294966272) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 (- s)) (Z_to_bv 64 (- s)) (Z_to_bv 64 4294967295) (Z_to_bv 64 bdw) (Z_to_bv 64 bdm) (Z_to_bv 64 (- mk)) a6' (Z_to_bv 64 adp)
        (Z_to_bv 64 kp) (Z_to_bv 64 bcw) (Z_to_bv 64 acp) (Z_to_bv 64 bcp) (Z_to_bv 64 acm) (Z_to_bv 64 adw) s8' s9 s10 s11
        (Z_to_bv 64 bdp) t4' (Z_to_bv 64 bcm) (Z_to_bv 64 acw))
     F' (Z_to_bv 64 0x4471c) fc None m (seg_rom rsegs)).
Proof.
  intros acw bcw adw bdw acp bcp adp bdp acm bcm adm bdm s mk F' fc m bs lj kj j16 rax a6' s8' t4'
    FRM ST FR MU WM MI BU BL LJ KC Racw Rbcw Radw Rbdw Racp Rbcp Radp Rbdp Racm Rbcm Radm Rbdm Lw Lp Hs Hmk M1 M2 M3 M4 M5.
  unfold G3_W in MU. unfold GSP in *.
  g3_solve 4%nat [0x44d38]%Z.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44d38%Z) _ _ _ _) =>
        g3_fold_R;
        lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?x0) (Z_to_bv 64 ?x1) (Z_to_bv 64 ?x2) _ (Z_to_bv 64 ?x4) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
          replace x0 with (mcode acm adm bcm bdm) by (g3m_mc_tac Lw Lp);
          replace x2 with (mcode acw adw bcw bdw) by (g3m_mc_tac Lw Lp);
          replace x4 with (mcode acp adp bcp bdp) by (g3m_mc_tac Lw Lp);
          replace x1 with (2 ^ 32 - s)%Z by (assert (s = 56 \/ s = 57 \/ s = 58 \/ s = 59)%Z as HS by lia;
                                             destruct HS as [ -> | [ -> | [ -> | -> ] ] ]; reflexivity)
        end;
        g3_expect open_constr:(mkR (Z_to_bv 64 0x447e0) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          (Z_to_bv 64 (mcode acm adm bcm bdm)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 (mcode acw adw bcw bdw)) (Z_to_bv 64 (2 ^ 32 - s))
          (Z_to_bv 64 (mcode acp adp bcp bdp)) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          (Z_to_bv 64 kp) _ _ _ _ _ _ s9 s10 s11 _ _ _ _);
        eapply g3_call
    end.
  all: try g3_side.
  all: g3_open.
Qed.

Lemma g3t_lo32 : forall c, (0 <= c)%Z -> ((c * 4294967296) mod 18446744073709551616 / 4294967296 = c mod 4294967296)%Z.
Proof.
  intros c Hc. change 18446744073709551616%Z with (4294967296 * 4294967296)%Z.
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma g3t_hi32 : forall c, (0 <= c < 2 ^ 64)%Z -> (0 <= c / 4294967296 < 2 ^ 32)%Z.
Proof. intros c Hc. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma g3_tail3 : forall (a0v a1v a2v a3v a5v wf plf x mif s mk idx : Z) rax t0' t1' t2' a4' a6' a7' s6' s8' t3' t4' t5' t6' (F3 : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) lj kj j16,
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  (0 <= idx < 687)%Z -> (a3v + a2v = PT_BASE + 8 * idx)%Z ->
  (-307 <= mk <= 325)%Z -> (56 <= s <= 59)%Z ->
  a0v = (- s)%Z -> a1v = (- s)%Z -> a5v = (- mk)%Z ->
  evt rsegs g3_post (MS (mkR rax (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) (Z_to_bv 64 a3v) a4' (Z_to_bv 64 a5v) a6' a7'
        (Z_to_bv 64 kp) (Z_to_bv 64 wf) (Z_to_bv 64 plf) (Z_to_bv 64 x) s6' (Z_to_bv 64 mif) s8' s9 s10 s11 t3' t4' t5' t6')
     F3 (Z_to_bv 64 0x44698) fc None m (seg_rom rsegs)).
Proof.
  intros a0v a1v a2v a3v a5v wf plf x mif s mk idx rax t0' t1' t2' a4' a6' a7' s6' s8' t3' t4' t5' t6' F3 fc m bs lj kj j16
    FRM ST FR MU WM MI BU BL LJ KC Hplf Hwf Hx Hmif Hxm Hxw Hidx Ha2 Hmk Hs Ha0 Ha1 Ha5.
  subst a0v a1v a5v.
  unfold G3_W in MU. unfold GSP in *.
  assert (Hpx : (2 ^ 9 <= 2 ^ x <= 2 ^ 62)%Z) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (pt_read m idx MI ltac:(lia)) as RDPT.
  pose proof (pt_facts idx ltac:(lia)) as HPT.
  change G3PureX_u5.rsegs with DgWalkX_u5.rsegs in RDPT.
  unfold PT_BASE in *.
  g3_solve 4%nat [0x446bc]%Z.
  all: try (unfold le_bytes_to_word); try rewrite extract64_id.
  all: try change (bytes_le_to_Z (firstn 8 (skipn (Z.to_nat (8 * idx)) PT_BYTES))) with (PTZ idx).
  all: set (cf := PTZ idx) in *; clearbody cf; clear RDPT.
  all: g3_solve 4%nat [0x4471c]%Z.
  all: g3_fold_R.
  all: rewrite (Z.mod_small x 64) by lia.
  all: set (xm := (mif * 2 ^ x)%Z) in *.
  all: rewrite (Z.mod_small xm 18446744073709551616) by lia.
  all: rewrite (g3t_lo32 cf) by lia.
  all: set (xw := (wf * 2048)%Z) in *; set (xp := (plf * 1024)%Z) in *.
  all: assert (Rxw : (2 ^ 63 <= xw < 2 ^ 64)%Z) by (unfold xw; lia).
  all: assert (Rxp : (2 ^ 63 <= xp < 2 ^ 64)%Z) by (unfold xp; lia).
  all: assert (Rxm : (2 ^ 61 <= xm <= xw)%Z) by (unfold xm, xw in *; lia).
  all: assert (Ewl : Z.land xw 4294965248 = (xw mod 4294967296)%Z)
         by (apply (land_mask_low xw 11); [lia | lia | unfold xw; replace 2048%Z with (2 ^ 11)%Z by reflexivity; apply Z.mod_mul; lia]).
  all: assert (Epl : Z.land xp 4294966272 = (xp mod 4294967296)%Z)
         by (apply (land_mask_low xp 10); [lia | lia | unfold xp; replace 1024%Z with (2 ^ 10)%Z by reflexivity; apply Z.mod_mul; lia]).
  all: assert (Eml : Z.land xm 4294967295 = (xm mod 4294967296)%Z)
         by (change 4294967295%Z with (Z.ones 32); rewrite Z.land_ones by lia; reflexivity).
  all: rewrite ?Ewl, ?Epl, ?Eml.
  all: set (ch := (cf / 4294967296)%Z) in *; set (cl := (cf mod 4294967296)%Z) in *.
  all: set (wh := (xw / 4294967296)%Z) in *; set (wl := (xw mod 4294967296)%Z) in *.
  all: set (ph := (xp / 4294967296)%Z) in *; set (pl := (xp mod 4294967296)%Z) in *.
  all: set (mh := (xm / 4294967296)%Z) in *; set (ml := (xm mod 4294967296)%Z) in *.
  all: assert (Rch : (0 <= ch < 2 ^ 32)%Z) by (unfold ch; apply g3t_hi32; lia).
  all: assert (Rcl : (0 <= cl < 2 ^ 32)%Z) by (unfold cl; apply Z.mod_pos_bound; lia).
  all: assert (Rwh : (0 <= wh < 2 ^ 32)%Z) by (unfold wh; apply g3t_hi32; lia).
  all: assert (Rwl : (0 <= wl < 2 ^ 32)%Z) by (unfold wl; apply Z.mod_pos_bound; lia).
  all: assert (Rph : (0 <= ph < 2 ^ 32)%Z) by (unfold ph; apply g3t_hi32; lia).
  all: assert (Rpl : (0 <= pl < 2 ^ 32)%Z) by (unfold pl; apply Z.mod_pos_bound; lia).
  all: assert (Rmh : (0 <= mh < 2 ^ 32)%Z) by (unfold mh; apply g3t_hi32; lia).
  all: assert (Rml : (0 <= ml < 2 ^ 32)%Z) by (unfold ml; apply Z.mod_pos_bound; lia).
  all: assert (Xc : (ch * 2 ^ 32 + cl = cf)%Z) by (unfold ch, cl; pose proof (Z.div_mod cf 4294967296 ltac:(lia)); lia).
  all: assert (Xw : (wh * 2 ^ 32 + wl = xw)%Z) by (unfold wh, wl; pose proof (Z.div_mod xw 4294967296 ltac:(lia)); lia).
  all: assert (Xp : (ph * 2 ^ 32 + pl = xp)%Z) by (unfold ph, pl; pose proof (Z.div_mod xp 4294967296 ltac:(lia)); lia).
  all: assert (Xm : (mh * 2 ^ 32 + ml = xm)%Z) by (unfold mh, ml; pose proof (Z.div_mod xm 4294967296 ltac:(lia)); lia).
  all: assert (Hwl11 : (wl mod 2 ^ 11 = 0)%Z)
         by (clear - Hwf; unfold wl, xw; replace 4294967296%Z with (2 ^ 21 * 2048)%Z by reflexivity;
             rewrite Z.mul_mod_distr_r by lia; replace (2 ^ 11)%Z with 2048%Z by reflexivity; apply Z.mod_mul; lia).
  all: assert (Hpl10 : (pl mod 2 ^ 10 = 0)%Z)
         by (clear - Hplf; unfold pl, xp; replace 4294967296%Z with (2 ^ 22 * 1024)%Z by reflexivity;
             rewrite Z.mul_mod_distr_r by lia; replace (2 ^ 10)%Z with 1024%Z by reflexivity; apply Z.mod_mul; lia).
  all: assert (Lxw : (xw <= xp)%Z) by (unfold xw, xp; clear - Hxw; lia).
  all: clearbody ch cl wh wl ph pl mh ml; clearbody xm xw xp.
  all: assert (Eb : Z.land (ch * wl) 4294965248 = ((ch * wl) mod 4294967296)%Z)
         by (clear - Rch Rwl Hwl11; apply (land_mask_low (ch * wl) 11); [lia | apply Z.mul_nonneg_nonneg; lia |
             rewrite Z.mul_mod by lia; rewrite Hwl11; rewrite Z.mul_0_r; reflexivity]).
  all: assert (Ep : Z.land (ch * pl) 4294966272 = ((ch * pl) mod 4294967296)%Z)
         by (clear - Rch Rpl Hpl10; apply (land_mask_low (ch * pl) 10); [lia | apply Z.mul_nonneg_nonneg; lia |
             rewrite Z.mul_mod by lia; rewrite Hpl10; rewrite Z.mul_0_r; reflexivity]).
  all: pose proof (prod32b ch wh Rch Rwh) as Pacw; pose proof (prod32b cl wh Rcl Rwh) as Padw;
       pose proof (prod32b ch wl Rch Rwl) as Pbcw; pose proof (prod32b cl wl Rcl Rwl) as Pbdw.
  all: pose proof (prod32b ch ph Rch Rph) as Pacp; pose proof (prod32b cl ph Rcl Rph) as Padp;
       pose proof (prod32b ch pl Rch Rpl) as Pbcp; pose proof (prod32b cl pl Rcl Rpl) as Pbdp.
  all: pose proof (prod32b ch mh Rch Rmh) as Pacm; pose proof (prod32b cl mh Rcl Rmh) as Padm;
       pose proof (prod32b ch ml Rch Rml) as Pbcm; pose proof (prod32b cl ml Rcl Rml) as Pbdm.
  all: pose proof (mcode_mult wh wl ch cl Rwh Rwl Rch Rcl) as Mw; rewrite Xw, Xc in Mw.
  all: pose proof (mcode_mult ph pl ch cl Rph Rpl Rch Rcl) as Mp; rewrite Xp, Xc in Mp.
  all: pose proof (mcode_mult mh ml ch cl Rmh Rml Rch Rcl) as Mm; rewrite Xm, Xc in Mm.
  all: pose proof (mult_lo xm cf ltac:(clear - Rxm; lia) ltac:(clear - HPT; lia)) as L1.
  all: pose proof (mult_mono xm xw cf ltac:(clear - Rxm; lia) ltac:(clear - HPT; lia)) as L2.
  all: pose proof (mult_mono xw xp cf ltac:(clear - Lxw Rxw; lia) ltac:(clear - HPT; lia)) as L3.
  all: pose proof (mult_hi xp cf ltac:(clear - Rxp; lia) ltac:(clear - HPT; lia)) as L4.
  all: pose proof (mult_lo62 xp cf ltac:(clear - Rxp; lia) ltac:(clear - HPT; lia)) as L5.
  all: eapply (g3_mul (ch * wh)%Z (ch * wl)%Z (cl * wh)%Z (cl * wl)%Z (ch * ph)%Z (ch * pl)%Z (cl * ph)%Z (cl * pl)%Z
                      (ch * mh)%Z (ch * ml)%Z (cl * mh)%Z (cl * ml)%Z s mk).
  all: try eassumption.
  all: try (rewrite Mm; clear - L1; lia).
  all: try (rewrite Mm, Mw; clear - L2; lia).
  all: try (rewrite Mw, Mp; clear - L3; lia).
  all: try (rewrite Mp; clear - L4; lia).
  all: try (rewrite Mp; clear - L5; lia).
  all: g3_open.
Qed.

Lemma kc_arg_u1 : forall ple, (-1127 <= ple <= 971)%Z ->
  bv_swrap 32 ((18446744073709551557 - (ple + 54) mod 18446744073709551616) mod 18446744073709551616 + 63) = (-50 - ple)%Z.
Proof.
  intros ple H. rewrite Zminus_mod_idemp_r.
  destruct (Z_lt_le_dec 0 (ple + 113)) as [P|P].
  - rewrite (Z.mod_small (18446744073709551557 - (ple + 54)) 18446744073709551616) by lia.
    replace (18446744073709551557 - (ple + 54) + 63)%Z with ((-50 - ple) + 4294967296 * 2 ^ 32)%Z
      by (change (2 ^ 32)%Z with 4294967296%Z; lia).
    rewrite swrap32_mod. rewrite swrap32_small by lia. lia.
  - replace (18446744073709551557 - (ple + 54))%Z with ((- (ple + 113)) + 1 * 18446744073709551616)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    rewrite swrap32_small by lia. lia.
Qed.
Lemma kc_arg_u2 : forall ple, (-1127 <= ple <= 971)%Z ->
  bv_swrap 32 ((18446744073709551557 - (ple + 54) mod 18446744073709551616) mod 18446744073709551616) = (-113 - ple)%Z.
Proof.
  intros ple H. rewrite Zminus_mod_idemp_r.
  destruct (Z_lt_le_dec 0 (ple + 113)) as [P|P].
  - rewrite (Z.mod_small (18446744073709551557 - (ple + 54)) 18446744073709551616) by lia.
    replace (18446744073709551557 - (ple + 54))%Z with ((-113 - ple) + 4294967296 * 2 ^ 32)%Z
      by (change (2 ^ 32)%Z with 4294967296%Z; lia).
    rewrite swrap32_mod. rewrite swrap32_small by lia. lia.
  - replace (18446744073709551557 - (ple + 54))%Z with ((- (ple + 113)) + 1 * 18446744073709551616)%Z by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    rewrite swrap32_small by lia. lia.
Qed.

Lemma g3t_neg64 : forall k, Z_to_bv 64 (0 - k mod 18446744073709551616) = Z_to_bv 64 (- k).
Proof.
  intros k. change (0 - k mod 18446744073709551616)%Z with (0 mod 18446744073709551616 - k mod 18446744073709551616)%Z.
  rewrite zbv_sub64; f_equal; lia.
Qed.

Lemma kc_arg_u3 : forall ple, (-1127 <= ple <= 971)%Z ->
  bv_swrap 32 (18446744073709551557 - (ple + 54) mod 18446744073709551616) = (-113 - ple)%Z.
Proof.
  intros ple H. rewrite swrap32_subl.
  replace (18446744073709551557 - (ple + 54))%Z with ((-113 - ple) + 4294967296 * 2 ^ 32)%Z
    by (change (2 ^ 32)%Z with 4294967296%Z; lia).
  rewrite swrap32_mod. rewrite swrap32_small by lia. lia.
Qed.
Lemma kc_arg_u4 : forall ple,
  ((18446744073709551557 - (ple + 54) mod 18446744073709551616) mod 18446744073709551616 = (-113 - ple) mod 18446744073709551616)%Z.
Proof.
  intros ple. rewrite Zminus_mod_idemp_r.
  replace (18446744073709551557 - (ple + 54))%Z with ((-113 - ple) + 1 * 18446744073709551616)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma g3_tail2 : forall a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' (F2 : bvmap 5 word) fc (m : word -> option byte) (plf ple wf we mif x : Z) (bs : list byte) lj kj j16,
  reg_get F2 10 = ceil_m (KCX (-50 - ple)) ->
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (-1127 <= ple <= 971)%Z -> we = (ple + 1)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0x445f8) (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
     a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) (Z_to_bv 64 wf) (Z_to_bv 64 plf)
     (Z_to_bv 64 x) (Z_to_bv 64 (ple + -10)) (Z_to_bv 64 mif) (Z_to_bv 64 (we + -11)) s9 s10 s11 t3' t4' t5' t6')
     F2 (Z_to_bv 64 0x445f8) fc None m (seg_rom rsegs)).
Proof.
  intros a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' F2 fc m plf ple wf we mif x bs lj kj j16
    HF2 FRM ST FR MU WM MI BU BL LJ KC Hple Hwe Hplf Hwf Hx Hmif Hxm Hxw.
  unfold G3_W in MU. unfold GSP in *.
  destruct (kcb_facts ple Hple) as (KR1 & KR2 & KR3).
  destruct (kc_facts ple Hple) as (Hidx & Hse).
  unfold FLO, FHI in KR1, KR2.
  g3_solve 2%nat [0x44604]%Z.
  all: fx_goal F2 (ceil_m (KCX (-50 - ple))) HF2; rewrite KR1.
  all: g3_solve 2%nat [0x44614]%Z.
  all: fx_goal F2 (ceil_m (KCX (-50 - ple))) HF2; rewrite KR2.
  all: g3_solve 2%nat [0x4461c]%Z.
  all: fx_goal F2 (ceil_m (KCX (-50 - ple))) HF2.
  all: change (fcvt_w_d RTZ (ceil_m (KCX (-50 - ple)))) with (KCWB (-50 - ple)).
  all: replace (KCWB (-50 - ple)) with (Z_to_bv 64 (KCZ (-50 - ple))) by (rewrite <- KR3; apply zbv_signed).
  all: set (mk := KCZ (-50 - ple)) in *; clearbody mk.
  all: pose proof (pe_read m (mk + 343) MI ltac:(lia)) as RDPE.
  all: change G3PureX_u5.rsegs with DgWalkX_u5.rsegs in RDPE.
  all: unfold PE_BASE, PT_BASE in *.
  all: g3_solve 8%nat [0x4465c]%Z.
  all: try (unfold le_bytes_to_word); try rewrite sext_extract32.
  all: try change (bv_swrap 32 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * (mk + 343))) PE_BYTES)))) with (PEZ (mk + 343)).
  all: set (ce := PEZ (mk + 343)) in *; clearbody ce; clear RDPE.
  all: assert (HR1 : (- 2 ^ 31 <= we + -11 + ce < 2 ^ 31 - 64)%Z) by (clear - Hwe Hple Hse; lia).
  all: assert (HR2 : (- 2 ^ 31 <= ple + -10 + ce < 2 ^ 31 - 64)%Z) by (clear - Hple Hse; lia).
  all: g3_solve 12%nat [0x44698]%Z.
  all: g3_fold_R.
  all: rewrite ?g3t_neg64.
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x44698%Z) _ _ _ _) =>
         eapply (g3_tail3 _ _ _ _ _ wf plf x mif (- (ce + ple + 54))%Z mk (mk + 343)%Z) end.
  all: try eassumption.
  all: try (unfold PT_BASE; lia).
  all: try lia.
  all: g3_open.
Qed.

(* [comment removed for export] *)
Lemma g3_tail : forall a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s8' fc (m : word -> option byte) (plf ple wf we mif x : Z) (bs : list byte) lj kj j16,
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (-1127 <= ple <= 971)%Z -> we = (ple + 1)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> (2 ^ 52 <= wf < 2 ^ 53)%Z ->
  (9 <= x <= 62)%Z -> (1 <= mif < 2 ^ 54)%Z -> (2 ^ 61 <= mif * 2 ^ x <= wf * 2 ^ 11)%Z -> (wf * 2 ^ 11 <= plf * 2 ^ 10)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
     (Z_to_bv 64 we) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) (Z_to_bv 64 wf) (Z_to_bv 64 plf)
     (Z_to_bv 64 x) (Z_to_bv 64 (ple + -10)) (Z_to_bv 64 mif) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x445b8) fc None m (seg_rom rsegs)).
Proof.
  intros a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s8' fc m plf ple wf we mif x bs lj kj j16
    FRM ST FR MU WM MI BU BL LJ KC Hple Hwe Hplf Hwf Hx Hmif Hxm Hxw.
  unfold G3_W in MU. unfold GSP in *.
  destruct (kcb_facts ple Hple) as (KR1 & KR2 & KR3).
  pose proof (kc_arg_u1 ple Hple) as KCA1. pose proof (kc_arg_u2 ple Hple) as KCA2.
  pose proof (kc_arg_u3 ple Hple) as KCA3. pose proof (kc_arg_u4 ple : g3_mk _) as KCA4.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = (bv_unsigned sp + -96)%Z) by (apply unsigned_lit; lia).
  assert (USP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  g3_solve 8%nat [0xb1888]%Z.
  all: g3_fold_R.
  all: eapply evt_cut; [ eapply ceil_spec | ].
  all: unfold CSP; rewrite ?USP, ?USP2.
  all: try eassumption.
  all: try reflexivity.
  all: try lia.
  all: lazymatch goal with
    | |- forall _, _ -> _ =>
        cbv beta; let ms' := fresh "ms'" in let P := fresh "P" in intros ms' P;
        unfold ceil_post, CSP in P; rewrite ?USP, ?USP2 in P;
        let F' := fresh "F'" in let fc' := fresh "fc'" in let m' := fresh "m'" in
        let MUc := fresh "MUc" in let WMc := fresh "WMc" in
        destruct P as (a0c & a1c & a2c & F' & fc' & m' & -> & HF' & FRM' & MUc & WMc & MI' & ST');
        replace (ret_pc (Z_to_bv 64 0x445f8)) with (Z_to_bv 64 0x445f8) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
        lazymatch type of MUc with munch _ ?mm _ =>
          assert (MU2 : munch [(bv_unsigned sp - 160, bv_unsigned sp); (buf, buf + 22); (lenp, lenp + 4); (kp, kp + 4)]%Z m0 m')
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUc]; intros z Hz; cbn in Hz |- *;
                 rewrite ?USP, ?USP2 in Hz |- *; destruct Hz as (Hz1 & _); split; [first [lia | lazymatch goal with |- ?G => let T := type of Hz1 in fail 100 "munchw goal" G "hz1" T end] | exact I]]);
          assert (WM2 : wmono rsegs m0 m') by (eapply wmono_trans; [exact WM | exact WMc]);
          transport_after_call rsegs mm m' MUc WMc
        end;
        g3_fold_R;
        g3_expect open_constr:(mkR (Z_to_bv 64 0x445f8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          _ _ _ _ _ _ _ _ (Z_to_bv 64 kp) _ _ _ _ _ _ s9 s10 s11 _ _ _ _);
        eapply g3_tail2;
        [ first [ (rewrite HF'; rewrite freg_get_same by reflexivity; unfold KCX; reflexivity)
                | (rewrite HF'; rewrite freg_get_same by reflexivity; unfold KCX, KC_CONST; reflexivity)
                | (rewrite HF'; reflexivity) | (rewrite HF'; unfold KCX; reflexivity)
                | (rewrite HF'; unfold KCX; repeat f_equal; first [ lia | g3_plits; lia ])
                | (let T := type of HF' in fail 100 "ceil arg" T) ] | .. ]
    | _ => idtac
    end.
  all: try g3_side.
  all: g3_open.
Qed.

Lemma pow_norm_unique : forall vf i k, (1 <= vf)%Z -> (0 <= i)%Z -> (0 <= k)%Z ->
  (2 ^ 52 <= vf * 2 ^ i < 2 ^ 53)%Z -> (2 ^ 53 <= (2 * vf + 1) * 2 ^ k < 2 ^ 54)%Z -> i = k.
Proof.
  intros vf i k Hv Hi Hk [A1 A2] [B1 B2].
  change (2 ^ 52)%Z with 4503599627370496%Z in *. change (2 ^ 53)%Z with 9007199254740992%Z in *.
  change (2 ^ 54)%Z with 18014398509481984%Z in *.
  assert (Pi : (0 < 2 ^ i)%Z) by (apply Z.pow_pos_nonneg; lia).
  assert (Pk : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.lt_trichotomy i k) as [L|[E|L]]; [exfalso | exact E | exfalso].
  - assert (P : (2 * 2 ^ i <= 2 ^ k)%Z).
    { replace (2 * 2 ^ i)%Z with (2 ^ (i + 1))%Z by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    set (X := (2 ^ k)%Z) in *. set (Y := (2 ^ i)%Z) in *. clearbody X Y.
    assert (Q : (2 * vf * (2 * Y) <= 2 * vf * X)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (R : ((2 * vf + 1) * X = 2 * vf * X + X)%Z) by ring.
    assert (S : (2 * vf * (2 * Y) = 4 * (vf * Y))%Z) by ring.
    lia.
  - assert (I53 : (i < 53)%Z).
    { destruct (Z_lt_le_dec i 53) as [H|H]; [exact H | exfalso].
      assert (T : (2 ^ 53 <= 2 ^ i)%Z) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 53)%Z with 9007199254740992%Z in T.
      assert (U : (1 * 2 ^ i <= vf * 2 ^ i)%Z) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    assert (WY : (2 ^ (53 - i) * 2 ^ i = 9007199254740992)%Z)
      by (rewrite <- Z.pow_add_r by lia; replace (53 - i + i)%Z with 53%Z by lia; reflexivity).
    assert (P : (2 * 2 ^ k <= 2 ^ i)%Z).
    { replace (2 * 2 ^ k)%Z with (2 ^ (k + 1))%Z by (rewrite Z.pow_add_r by lia; lia). apply Z.pow_le_mono_r; lia. }
    set (X := (2 ^ k)%Z) in *. set (Y := (2 ^ i)%Z) in *. set (W := (2 ^ (53 - i))%Z) in *. clearbody X Y W.
    assert (Vw : (vf < W)%Z).
    { destruct (Z_lt_le_dec vf W) as [H|H]; [exact H | exfalso].
      assert (T : (W * Y <= vf * Y)%Z) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    assert (T1 : (vf * Y <= (W - 1) * Y)%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (T2 : ((W - 1) * Y = W * Y - Y)%Z) by ring.
    assert (T3 : (vf * (2 * X) <= vf * Y)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (T4 : ((2 * vf + 1) * X = vf * (2 * X) + X)%Z) by ring.
    lia.
Qed.

Lemma g3_loopB : forall (n : nat) (i kA vf a0v a1v plf xv mif pl : Z) t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  Z.to_nat (52 - i) = n ->
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> a0v = (-1074 - i)%Z -> a1v = (vf * 2 ^ i)%Z -> (a1v < 2 ^ 52)%Z ->
  (1 <= kA <= 52)%Z -> plf = ((2 * vf + 1) * 2 ^ kA)%Z -> (2 ^ 53 <= plf < 2 ^ 54)%Z -> xv = (kA + 10)%Z -> mif = (2 * vf - 1)%Z -> pl = (-1075 - kA)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 kp) s3'
        (Z_to_bv 64 plf) (Z_to_bv 64 xv) (Z_to_bv 64 (pl + -10)) (Z_to_bv 64 mif) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x4459c) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i kA vf a0v a1v plf xv mif pl t0' t1' t2' a2' a3' a4' a5' a6' a7' s3' s8' t3' t4' t5' t6' fc m bs lj kj j16
    Hn FRM ST FR MU WM MI BU BL LJ KC Hvf Hi Ha0 Ha1 Ha1r HkA Hplf Hplr Hxv Hmif Hpl.
  - exfalso. assert (Hi52 : (52 <= i)%Z) by lia.
    pose proof (Z.pow_le_mono_r 2 52 i ltac:(lia) Hi52) as P.
    assert (H3 : (2 ^ i <= a1v)%Z)
      by (rewrite Ha1; replace (2 ^ i)%Z with (1 * 2 ^ i)%Z at 1 by lia; apply Z.mul_le_mono_nonneg_r; lia).
    lia.
  - assert (Hi52 : (i < 52)%Z) by lia.
    pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi) as Pi.
    assert (E2 : (2 ^ (i + 1) = 2 * 2 ^ i)%Z) by (rewrite Z.pow_add_r by lia; lia).
    assert (A0 : (0 <= a1v)%Z) by (rewrite Ha1; apply Z.mul_nonneg_nonneg; lia).
    g3_xstep. g3_solve 6%nat [0x4459c; 0x445b8]%Z.
    all: try (g3_hnorm; exfalso; lia).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x4459c%Z) _ _ _ _) => g3_fold_R; eapply (IH (i + 1)%Z kA vf)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x445b8%Z) _ _ _ _) =>
          g3_expect open_constr:(mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
            _ _ _ _ _ _ _ _ (Z_to_bv 64 kp) _ _ _ _ _ _ s9 s10 s11 _ _ _ _);
          assert (W1 : (2 ^ 52 <= a1v * 2)%Z) by (g3_hnorm; lia);
          assert (Ei : (i + 1)%Z = kA)
            by (apply (pow_norm_unique vf (i + 1) kA); [lia | lia | lia | rewrite E2; lia | lia]);
          assert (Y51 : (2 ^ i <= 2 ^ 51)%Z) by (apply Z.pow_le_mono_r; lia);
          assert (PX : (2 ^ xv = 2 ^ i * 2048)%Z)
            by (rewrite Hxv, <- Ei; replace (i + 1 + 10)%Z with (i + 11)%Z by lia; rewrite Z.pow_add_r by lia; reflexivity);
          assert (MX : (mif * 2 ^ xv = 4096 * a1v - 2048 * 2 ^ i)%Z) by (rewrite PX, Hmif, Ha1; ring);
          assert (PL : (plf = 4 * a1v + 2 * 2 ^ i)%Z) by (rewrite Hplf, <- Ei, Z.pow_add_r, Ha1 by lia; ring);
          eapply g3_tail
      end.
    all: try (rewrite MX; g3_plits; lia).
    all: try g3_side.
    all: g3_open.
Qed.

(* [comment removed for export] *)
Lemma g3_mid : forall (vf ve k E a0v a1v a4v a5v a7v s4v s7v : Z) t0' t1' t2' a6' s3w s5' s6' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (0 <= E <= 2047)%Z -> (0 <= k <= 52)%Z -> (1 <= vf < 2 ^ 53)%Z -> (2 ^ 53 <= (2 * vf + 1) * 2 ^ k < 2 ^ 54)%Z ->
  (E <> 0 -> k = 0 /\ 2 ^ 52 <= vf /\ a0v = ve /\ s3w = Z_to_bv 64 vf /\ ve = E - 1075)%Z ->
  (E = 0 -> 1 <= k /\ vf < 2 ^ 52 /\ a1v = vf /\ ve = -1074)%Z ->
  a4v = ve -> a5v = (ve - 1)%Z -> a7v = (ve - 1 - k)%Z -> s4v = ((2 * vf + 1) * 2 ^ k)%Z -> s7v = (2 * vf)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp t0' t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 E) (Z_to_bv 64 vf) (Z_to_bv 64 a4v) (Z_to_bv 64 a5v) a6' (Z_to_bv 64 a7v)
        (Z_to_bv 64 kp) s3w (Z_to_bv 64 s4v) s5' s6' (Z_to_bv 64 s7v) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x44544) fc None m (seg_rom rsegs)).
Proof.
  intros vf ve k E a0v a1v a4v a5v a7v s4v s7v t0' t1' t2' a6' s3w s5' s6' s8' t3' t4' t5' t6' fc m bs lj kj j16
    FRM ST FR MU WM MI BU BL LJ KC HE Hk Hvf Hnk HEn HE0 Ha4 Ha5 Ha7 Hs4 Hs7.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Pk.
  destruct (Z.eq_dec E 0) as [E0|En];
    [ destruct (HE0 E0) as (Hk1 & Hvf2 & Ha1 & Hve) | destruct (HEn En) as (Hk0 & Hvf2 & Ha0 & Hs3 & Hve); subst k s3w ].
  all: g3_solve 10%nat [0x4459c; 0x445b8]%Z.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x4459c%Z) _ _ _ _) =>
        g3_expect open_constr:(mkR ra (Z_to_bv 64 (GSP - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          _ _ _ _ _ _ _ _ (Z_to_bv 64 kp) _ _ _ _ _ _ s9 s10 s11 _ _ _ _);
        eapply (g3_loopB _ 0 k vf)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x445b8%Z) _ _ _ _) =>
        g3_expect open_constr:(mkR ra (Z_to_bv 64 (GSP - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          _ _ _ _ _ _ _ _ (Z_to_bv 64 kp) _ _ _ _ _ _ s9 s10 s11 _ _ _ _);
        eapply g3_tail
    end.
  all: try (assert (X10 : (a5v - (a7v + -10))%Z = 10%Z) by lia; rewrite X10; clear X10).
  all: try (assert (X9 : (a4v + -2 - (a7v + -10))%Z = 9%Z) by lia; rewrite X9; clear X9).
  all: try g3_side.
  all: g3_open.
Qed.

(* [comment removed for export] *)
Lemma g3_loopA : forall (n : nat) (i vf t0v a7v a0v a2v a3v a4v a5v a6v s7v : Z) t1' t2' s3' s4' s5' s6' s8' t3' t4' t5' t6' fc (m : word -> option byte) (bs : list byte) lj kj j16,
  Z.to_nat (52 - i) = n ->
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 96) ->
  rw_cells rsegs m (GSP - 96) [CB 16 j16; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  (1 <= vf < 2 ^ 52)%Z -> (0 <= i)%Z -> t0v = ((2 * vf + 1) * 2 ^ i)%Z -> a7v = (-1075 - i)%Z -> (t0v < 2 ^ 53)%Z ->
  a2v = 0%Z -> a3v = vf -> a4v = (-1074)%Z -> a5v = (-1075)%Z -> a6v = (2 ^ 52)%Z -> s7v = (2 * vf)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 96)) gp tp (Z_to_bv 64 t0v) t1' t2' (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
        (Z_to_bv 64 a0v) (Z_to_bv 64 vf) (Z_to_bv 64 a2v) (Z_to_bv 64 a3v) (Z_to_bv 64 a4v) (Z_to_bv 64 a5v) (Z_to_bv 64 a6v) (Z_to_bv 64 a7v)
        (Z_to_bv 64 kp) s3' s4' s5' s6' (Z_to_bv 64 s7v) s8' s9 s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 0x44528) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i vf t0v a7v a0v a2v a3v a4v a5v a6v s7v t1' t2' s3' s4' s5' s6' s8' t3' t4' t5' t6' fc m bs lj kj j16
    Hn FRM ST FR MU WM MI BU BL LJ KC Hvf Hi Ht0 Ha7 Hlt Ha2 Ha3 Ha4 Ha5 Ha6 Hs7; subst a2v a3v a4v a5v a6v s7v.
  - exfalso. assert (Hi52 : (52 <= i)%Z) by lia.
    pose proof (Z.pow_le_mono_r 2 52 i ltac:(lia) Hi52) as P.
    assert (H3 : (3 * 2 ^ i <= t0v)%Z) by (rewrite Ht0; apply Z.mul_le_mono_nonneg_r; lia).
    change (2 ^ 53)%Z with (2 * 2 ^ 52)%Z in Hlt. lia.
  - assert (Hi52 : (i < 52)%Z) by lia.
    pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi) as Pi.
    assert (E2 : (2 ^ (i + 1) = 2 * 2 ^ i)%Z) by (rewrite Z.pow_add_r by lia; lia).
    assert (T0 : (0 <= t0v)%Z) by (rewrite Ht0; apply Z.mul_nonneg_nonneg; lia).
    g3_xstep. g3_solve 6%nat [0x44528; 0x44544]%Z.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44528%Z) _ _ _ _) => g3_fold_R; eapply (IH (i + 1)%Z)
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44544%Z) _ _ _ _) => g3_expect open_constr:(mkR ra (Z_to_bv 64 (GSP - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 _) (Z_to_bv 64 vf) (Z_to_bv 64 0) (Z_to_bv 64 vf) (Z_to_bv 64 _) (Z_to_bv 64 _) _ (Z_to_bv 64 _) (Z_to_bv 64 kp) _ (Z_to_bv 64 _) _ _ (Z_to_bv 64 _) _ s9 s10 s11 _ _ _ _); eapply (g3_mid vf (-1074) (i + 1) 0)
      end.
    all: try g3_side.
    all: g3_open.
Qed.

(* [comment removed for export] *)
Lemma g3_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc (m : word -> option byte) (b : Z) (bs : list byte) lj kj,
  bv_unsigned (reg_get F 10) = b -> (1 <= b < 2 ^ 63)%Z -> frm0 fc ->
  stk rsegs m (GSP - 160) GSP -> u8arr rsegs m buf bs -> length bs = 22%nat ->
  rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] -> mem_inv rsegs m -> m = m0 ->
  evt rsegs g3_post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 kp) a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x44498) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m b bs lj kj HF Hb FRM ST BU BL LJ KC MI E.
  pose proof (munch_refl G3_W m) as MU. pose proof (wmono_refl rsegs m) as WM.
  subst m. unfold G3_W in MU. unfold GSP in *.
  assert (EB : (0 <= (b * 2) / 9007199254740992 <= 2047)%Z).
  { assert (H2 : (b * 2 < 2048 * 9007199254740992)%Z) by lia.
    pose proof (Z.div_lt_upper_bound (b * 2) 9007199254740992 2048 ltac:(lia) H2).
    split; [apply Z.div_pos|]; lia. }
  assert (MB : (0 <= Z.land b 4503599627370495 < 4503599627370496)%Z)
    by (change 4503599627370495%Z with (Z.ones 52); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia).
  assert (DEC : b = ((b * 2) / 9007199254740992 * 4503599627370496 + Z.land b 4503599627370495)%Z)
    by (change 4503599627370495%Z with (Z.ones 52); rewrite Z.land_ones by lia;
        rewrite (Z.mul_comm b 2); change 9007199254740992%Z with (2 * 4503599627370496)%Z;
        rewrite Z.div_mul_cancel_l by lia; pose proof (Z_div_mod_eq_full b 4503599627370496); lia).
  carve_frame 96%nat ST.
  g3_solve 12%nat [0x44528; 0x44544]%Z.
  all: try (g3_hnorm; exfalso; lia).
  all: g3_modg.
  all: rewrite ?lor52 by lia.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44528%Z) _ _ _ _) =>
        g3_expect open_constr:(mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp (Z_to_bv 64 _) _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _)
          (Z_to_bv 64 kp) _ _ _ _ (Z_to_bv 64 _) _ s9 s10 s11 _ _ _ _);
        eapply (g3_loopA _ 0)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x44544%Z) _ _ _ _) =>
        g3_expect open_constr:(mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp _ _ _ (Z_to_bv 64 buf) (Z_to_bv 64 lenp)
          (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) (Z_to_bv 64 _) _ (Z_to_bv 64 _)
          (Z_to_bv 64 kp) _ (Z_to_bv 64 _) _ _ (Z_to_bv 64 _) _ s9 s10 s11 _ _ _ _);
        lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
          eapply (g3_mid _ (e - 1075) 0 e) end
    end.
  all: try g3_side.
  all: g3_open.
Qed.
End G3.
