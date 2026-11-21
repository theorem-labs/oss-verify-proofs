(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed extract64_id, g3_call, g3_mul and 18 more. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TU Require Import G3Pure G3Lem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.TUXA Require Import DgWalkXA DgSpecXA G3PureXA.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @swrap32_id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @swrap32_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_eq]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @TT]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@stdpp; @bitvector; @definitions; @bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_mod64]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@stdpp; @bitvector; @definitions; @bv_wrap_small]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_0_r]; [@stdpp; @bitvector; @definitions; @bv_extract_unsigned]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @tactics; @f_equal_help]; [@stdpp; @bitvector; @definitions; @bv_half_modulus]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @signed_of_extract]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @NArith; @BinNat; @N; @lt]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @N2Z; @inj_lt]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pred]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_equiv]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_low]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_spec_low]; [@Stdlib; @ZArith; @BinInt; @Z; @ones_spec_high]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_high]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pow2_bits_low]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_0]; [@Stdlib; @Bool; @Bool; @andb_false_l]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_mod_distr_r]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEmul]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEpow]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @ZArith; @BinInt; @Z; @to_N]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Corelib; @Init; @Datatypes; @option]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @wview]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@Corelib; @Init; @Datatypes; @app]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @iff_Transitive]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_app]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @Morphisms; @respectful]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @ZS; @wr_at_app]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf_app]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @G3A; @GSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @G3A; @G3_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mrd]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @shadow_big]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @mrd_ov1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @frm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Stdlib; @Lists; @List; @firstn_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @u8arr_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @G3A; @g3_post]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Stdlib; @Lists; @List; @length_firstn]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @Lists; @List; @length_skipn]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @proj1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @rw_cells_app]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @dg_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgSpecXA; @dg_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @SP0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @app_buf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @G3A; @g3_sh_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @nth_error_upd_same]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @DgWalkXA; @sx32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TU; @G3Lem; @mcode]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TU; @G3Lem; @shr32_range]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @ro_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @negw_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TUXA; @G3WalkXA; @G3A; @g3_call]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @TU; @G3Lem; @ezext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_shl_shr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]].

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation rsegs := DgWalkXA.rsegs.

Lemma swrap32_id : forall x, (- 2 ^ 31 <= x < 2 ^ 31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow]. change (2 ^ 32 / 2)%Z with (2 ^ 31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_mod : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.pow].
  replace (x + k * 2 ^ 32 + 2 ^ 32 / 2)%Z with ((x + 2 ^ 32 / 2) + k * 2 ^ 32)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma kc_arg : forall ple, (-1127 <= ple <= 971)%Z -> bv_swrap 32 (18446744073709551566 - ple mod 18446744073709551616) = (-50 - ple)%Z.
Proof.
  intros ple Hp. rewrite (Z.mod_eq ple 18446744073709551616) by lia.
  replace (18446744073709551566 - (ple - 18446744073709551616 * (ple / 18446744073709551616)))%Z
    with ((-50 - ple) + (4294967296 + 4294967296 * (ple / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod. apply swrap32_id. lia.
Qed.

Lemma mi_shift : forall mie ple, (-1127 <= ple <= 971)%Z -> (9 <= mie - ple + 10 <= 62)%Z ->
  ((bv_swrap 32 (mie mod 18446744073709551616 - (ple + -10) mod 18446744073709551616) mod 18446744073709551616) mod 64 = mie - ple + 10)%Z.
Proof.
  intros mie ple Hp Hx.
  rewrite (Z.mod_eq mie 18446744073709551616), (Z.mod_eq (ple + -10) 18446744073709551616) by lia.
  replace (mie - 18446744073709551616 * (mie / 18446744073709551616) - (ple + -10 - 18446744073709551616 * ((ple + -10) / 18446744073709551616)))%Z
    with ((mie - ple + 10) + (4294967296 * ((ple + -10) / 18446744073709551616) - 4294967296 * (mie / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod, swrap32_id by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma shl_small : forall x k, (0 <= k)%Z -> (0 <= x)%Z -> (x * 2 ^ k < 2 ^ 64)%Z -> ((x ≪ k) mod 18446744073709551616 = x * 2 ^ k)%Z.
Proof. intros x k Hk Hx H. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

Lemma zbv_eqm : forall a b, (a mod 2 ^ 64 = b mod 2 ^ 64)%Z -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b), H. reflexivity. Qed.

Lemma extract64_id : forall z, bv_extract 0 64 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma sext_extract32 : forall z, sext 64 (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 (bv_swrap 32 z).
Proof.
  intros z. rewrite sext_small. f_equal. rewrite signed_of_extract by lia. rewrite Z_to_bv_unsigned.
  unfold bv_swrap. f_equal. unfold bv_wrap, bv_modulus. cbn -[Z.pow].
  rewrite (Z.add_mod (z mod 2 ^ 64)), (Z.add_mod z) by lia. rewrite Z.mod_mod_divide by (exists (2 ^ 32)%Z; reflexivity). reflexivity.
Qed.

Lemma land_mask_low : forall x k, (0 <= k <= 32)%Z -> (0 <= x)%Z -> (x mod 2 ^ k = 0)%Z -> Z.land x (2 ^ 32 - 2 ^ k) = (x mod 2 ^ 32)%Z.
Proof.
  intros x k Hk Hx H. replace (2 ^ 32 - 2 ^ k)%Z with (Z.ones 32 - Z.ones k)%Z by (rewrite !Z.ones_equiv; lia).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec. rewrite <- Z.land_ones by lia. rewrite Z.land_spec.
  assert (E : Z.testbit (Z.ones 32 - Z.ones k) i = (Z.leb k i && Z.ltb i 32)%bool).
  { replace (Z.ones 32 - Z.ones k)%Z with (Z.shiftl (Z.ones (32 - k)) k).
    - destruct (Z.ltb_spec i k) as [Hik|Hik].
      + rewrite Z.shiftl_spec_low by lia. destruct (Z.leb_spec k i); [lia | reflexivity].
      + rewrite Z.shiftl_spec_high by lia. destruct (Z.leb_spec k i); [|lia]. cbn [andb].
        destruct (Z.ltb_spec i 32); [apply Z.ones_spec_low; lia | apply Z.ones_spec_high; lia].
    - rewrite Z.shiftl_mul_pow2 by lia. rewrite !Z.ones_equiv.
      assert (P : (2 ^ (32 - k) * 2 ^ k = 2 ^ 32)%Z) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia. }
  rewrite E. destruct (Z.ltb_spec i k) as [Hik|Hik].
  - assert (Z.testbit x i = false).
    { rewrite <- (Z.mod_pos_bound x (2 ^ k)) || idtac. replace (Z.testbit x i) with (Z.testbit (x mod 2 ^ k) i) by (apply Z.mod_pow2_bits_low; lia). rewrite H. apply Z.bits_0. }
    rewrite H0. rewrite !Bool.andb_false_l. reflexivity.
  - destruct (Z.leb_spec k i); [|lia]. cbn [andb]. destruct (Z.ltb_spec i 32); [rewrite Z.ones_spec_low by lia | rewrite Z.ones_spec_high by lia]; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
Qed.
Lemma prod32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (0 <= a * b < 2 ^ 64)%Z.
Proof. intros a b Ha Hb. split; [apply Z.mul_nonneg_nonneg; lia|]. assert (a * b <= (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z by (apply Z.mul_le_mono_nonneg; lia). lia. Qed.
Lemma hi32 : forall x, (0 <= x < 2 ^ 64)%Z -> (0 <= Z.shiftr x 32 < 2 ^ 32)%Z.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma lo32_of_shl : forall x, (0 <= x)%Z -> (Z.shiftr ((Z.shiftl x 32) mod 18446744073709551616) 32 = x mod 4294967296)%Z.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace 18446744073709551616%Z with (2 ^ 32 * 2 ^ 32)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma mulhu_shl32 : forall a b, (0 <= a < 2 ^ 32)%Z -> (0 <= b < 2 ^ 32)%Z -> (Z.shiftr ((a * 4294967296) * (b * 4294967296)) 64 = a * b)%Z.
Proof. intros a b Ha Hb. rewrite Z.shiftr_div_pow2 by lia. replace (a * 4294967296 * (b * 4294967296))%Z with ((a * b) * 2 ^ 64)%Z by ring. apply Z.div_mul. lia. Qed.

Lemma shl32_mod : forall x, (0 <= x)%Z -> ((Z.shiftl x 32) mod 18446744073709551616 = (x mod 4294967296) * 4294967296)%Z.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. replace 18446744073709551616%Z with (2 ^ 32 * 2 ^ 32)%Z by reflexivity. apply Z.mul_mod_distr_r; lia. Qed.

Lemma negw_small : forall mk, (-307 <= mk <= 325)%Z -> bv_swrap 32 (0 - mk mod 18446744073709551616) = (- mk)%Z.
Proof.
  intros mk Hm. rewrite (Z.mod_eq mk 18446744073709551616) by lia.
  replace (0 - (mk - 18446744073709551616 * (mk / 18446744073709551616)))%Z with ((- mk) + (4294967296 * (mk / 18446744073709551616)) * 2 ^ 32)%Z by lia.
  rewrite swrap32_mod. apply swrap32_id. lia.
Qed.

Section ZS.
Local Open Scope Z_scope.
Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; [split; [lia | split; [lia | intros i Hi; apply H; lia]] |].
    split; [lia | split; [lia | intros i Hi; replace (a + n1 + i) with (a + (n1 + i)) by lia; apply H; lia]].
  - intros ((Ha & Hl1 & Ha1) & (Hb & Hl2 & Hb2)). split; [lia | split; [lia |]].
    intros i Hi. destruct (Z.lt_ge_cases i n1); [apply Ha1; lia |].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply Hb2. lia.
Qed.
Lemma u8arr_app : forall m A bs1 bs2,
  u8arr rsegs m A (bs1 ++ bs2) <-> u8arr rsegs m A bs1 /\ u8arr rsegs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.
Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <-> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add, wr_at_app by lia.
  split.
  - intros (((W1 & W2) & B) & Wa & Wb). apply bytes_at_app in B as (B1 & B2). rewrite cells_bytes_length in B2 by assumption. tauto.
  - intros (((W1 & B1) & Wa) & ((W2 & B2) & Wb)). split; [split; [tauto|] | tauto].
    apply bytes_at_app. rewrite cells_bytes_length by assumption. tauto.
Qed.
End ZS.

Section G3A.

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m0 : word -> option byte.
Variables buf lenp kp : Z.
Definition GSP : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'_7!1,S|600;/sp;").
Hypothesis BUFR : (4096 <= buf /\ buf + 22 <= 2^47)%Z.
Hypothesis SPR0 : (2^41 <= GSP /\ GSP + 40 <= 2^47)%Z.   (* [comment removed for export] *)

Hypothesis KP : kp = (GSP + 32)%Z.   (* [comment removed for export] *)
Hypothesis KL : lenp = (kp + 4)%Z.
Hypothesis SEP_B : (buf + 22 <= GSP - 160 \/ GSP + 40 <= buf)%Z.   (* [comment removed for export] *)
Definition app_buf22 : Prop := (buf + 22 <= 0x7fff7000 \/ 0x10007fff8000 <= buf)%Z.
Hypothesis APP_B : app_buf22.
Hypothesis APP_S : (0x10007fff8000 <= GSP - 160)%Z.

Hypothesis SHL : mrd rsegs m0 (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHK : mrd rsegs m0 (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHBUF : forall k, (0 <= k < 22)%Z -> mrd rsegs m0 (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPT : forall i, (0 <= i < 687)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureXA.PT_BASE + 8 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SHPE : forall i, (0 <= i < 686)%Z -> mrd rsegs m0 (wa (Z.shiftr (G3PureXA.PE_BASE + 4 * i) 3 + 2147450880)) = Some (Z_to_bv 8 0).

Definition G3_W : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+`C+0+0!1,5|20;!3,^P0!4,aN+0+0!2':'aO!1,5|720;'aO!3,^P0!4,aN+0+0/buf;!2'8/buf;!1,5|46;!3,^P0!4,aN+0+0/lenp;!2'8/lenp;1!3,^P0!4,aN+0+0/kp;!2'8/kp;1!1,B0").

Lemma g3_sh_read : forall (m : word -> option byte) (y x : Z), munch G3_W m0 m -> (0 <= y < 2 ^ 47)%Z -> x = (Z.shiftr y 3 + 2147450880)%Z ->
  mrd rsegs m0 (wa x) = Some (Z_to_bv 8 0) -> ov_read_bytes rsegs m (Z_to_bv 64 (Z.shiftr y 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof using All.
  intros m y x MU Hy -> H. pose proof (shadow_big y Hy) as SBg.
  apply mrd_ov1; [lia|]. unfold mrd. rewrite (MU (wa (Z.shiftr y 3 + 2147450880))). { exact H. }
  unfold G3_W. cbn [outside]. rewrite wa_unsigned by lia. unfold GSP, app_buf22 in *. repeat split; lia.
Qed.

Definition g3_post : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S?0!1,S|600;!1+_20|21;!2'b0!1,S21|500;!1+_2!1,S4|30;!1,S6!1+_27!1+`S8%~R19!1+D8!1,B+aD!1,5,P|45;$ms';R+a[!2+a\1$t0';R1!2+a\1$t1';R1!2+a\1$t2';R1!2+a\1$a1';R1!2+a\1$a2';R1!2+a\1$a3';R1!2+a\1$a4';R1!2+a\1$a5';R1!2+a\1$a6';R1!2+a\1$a7';R1!2+a\1$t3';R1!2+a\1$t4';R1!2+a\1$t5';R1!2+a\1$t6';R1!2+a\3$F';R3!2+a\5$fc';R5!2+a\:$m';R:!2+a\+0$res;R+0!2+a\+0$len;R+0!2+a\+0$K;R+0!2+a\;$bs;R;!2+1!3+9+a[#F!7'b1!O'b2/ra;/sp;/gp;/tp;#E#D#C/s0;/s1;!2'_30#4#B#A#@#?#>#=#</s2;/s3;/s4;/s5;/s6;/s7;/s8;/s9;/s10;/s11;#;#:#9#8#7!1'b3/ra;#6!1,^61#5!1'aW'`U!2+1!3'aP'aQ/m0;#5!2+1!3'b4'`U/m0;#5!2+1!2'b5'`U#5!2+1!1'b6#6!2+1!4'b7'`U#5!2':'aO!1,5|720;'aO!2+1!4'aC'`U#5/buf;#1!2+1!3+9+a;!2'a28#1}F!2+1!3+99!3'b88#1!1'b9#3!2,aS8!2'_37,<!2+1!4'aM'`U#5/lenp;!3,^P+aD!1,b:!2'_30#3<!2+1!2+1!2'2=#3!2'2#3!1,5>!2+1!4'aM'`U#5/kp;!3,^P+aD!1,b:!2'_30#2<!2+1!2+1!2'2!1,^C|857;#2!2'2#2!1,5|835;!2+`X!3+9+0#4,<!3+9+0#4=").

Local Notation SB := 2147450880%Z.

Lemma g3_call : forall t0' t1' t2' t3' t4' t5' t6' s3' s4' s5' s6' s7' (F' : bvmap 5 word) fc (m : word -> option byte) (Wm W Wp s K0 : Z) (bs : list byte) lj,
  frm0 fc ->
  stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [C8 (Z_to_bv 64 kp); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 (Z_to_bv 64 K0)] ->
  ro_cells rsegs m 0x160c18 [C8 (Z_to_bv 64 0x169ef8)] -> ro_cells rsegs m 0x169ef8 [C8 (Z_to_bv 64 2147450880)] ->
  (56 <= s <= 59)%Z -> (1 <= Wm <= W)%Z -> (W <= Wp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= Wp + 1)%Z -> (-325 <= K0 <= 307)%Z ->
  evt rsegs g3_post (MS (mkR (Z_to_bv 64 0xc7e9c) (Z_to_bv 64 (GSP - 80)) gp tp t0' t1' t2' (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
                             (Z_to_bv 64 Wm) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 W) (Z_to_bv 64 (2 ^ 32 - s)) (Z_to_bv 64 Wp) (Z_to_bv 64 (2 ^ 32 - s))
                             (Z_to_bv 64 buf) (Z_to_bv 64 lenp) (Z_to_bv 64 2147450880) s3' s4' s5' s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
                        F' (Z_to_bv 64 0xc87ac) fc None m (seg_rom rsegs)).
Proof using All.
  intros until lj. intros FRM ST FR MU WM MI BU BL LE KC GOT SHV Hs HWm HW HWp HKs.
  unfold G3_W in MU. unfold GSP in *.
  rewrite <- (firstn_skipn 21 bs) in BU. apply u8arr_app in BU as [BU1 BU2].
  assert (BL1 : length (firstn 21 bs) = 21%nat) by (rewrite firstn_length; lia).
  rewrite BL1 in BU2. change (Z.of_nat 21) with 21%Z in BU2.
  assert (B21 : exists b21, skipn 21 bs = [b21]).
  { assert (L1 : length (skipn 21 bs) = 1%nat) by (rewrite length_skipn; lia).
    destruct (skipn 21 bs) as [|b21 [|? ?]]; cbn in L1; try lia. exists b21. reflexivity. }
  destruct B21 as [b21 B21]. rewrite B21 in BU2.
  apply (proj1 (rw_cells_app m (bv_unsigned sp - 80) [C8 (Z_to_bv 64 kp)] _)) in FR as [KPc FR]. cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp - 80 + Z.of_nat 8)%Z with (bv_unsigned sp - 72)%Z in FR by lia.
  replace (Z_to_bv 64 W) with (Z_to_bv 64 (Wm + (W - Wm))) by (f_equal; lia).
  replace (Z_to_bv 64 Wp) with (Z_to_bv 64 (Wm + (W - Wm) + (Wp - W))) by (f_equal; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) = (bv_unsigned sp - 80)%Z) by (apply unsigned_lit; lia).
  assert (SHLm : mrd rsegs m (wa (Z.shiftr lenp 3 + 2147450880)) = Some (Z_to_bv 8 0)).
  { unfold mrd. rewrite (MU _); [exact SHL|]. pose proof (shadow_big lenp ltac:(lia)). cbn [outside]. rewrite wa_unsigned by lia. unfold app_buf22 in *. repeat split; lia. }
  assert (SHKm : mrd rsegs m (wa (Z.shiftr kp 3 + 2147450880)) = Some (Z_to_bv 8 0)).
  { unfold mrd. rewrite (MU _); [exact SHK|]. pose proof (shadow_big kp ltac:(lia)). cbn [outside]. rewrite wa_unsigned by lia. unfold app_buf22 in *. repeat split; lia. }
  assert (SHBm : forall k, (0 <= k < 21)%Z -> mrd rsegs m (wa (Z.shiftr (buf + k) 3 + 2147450880)) = Some (Z_to_bv 8 0)).
  { intros k Hk. unfold mrd. rewrite (MU _); [exact (SHBUF k ltac:(lia))|]. pose proof (shadow_big (buf + k) ltac:(lia)). cbn [outside]. rewrite wa_unsigned by lia. unfold app_buf22 in *. repeat split; lia. }
  eapply evt_cut.
  { refine (DgSpecXA.dg_spec (Z_to_bv 64 0xc7e9c) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp (Z_to_bv 64 lenp) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) s3' s4' s5' s6' s7' s8 s9 s10 s11
              F' fc m buf lenp kp _ _ KL _ _ _ _ SHLm SHKm SHBm t0' t1' t2' t3' t4' t5' t6' m Wm (W - Wm) (Wp - W) s (- K0 - 0 + K0 + 0 + K0 - K0 + K0 - K0 + K0) (firstn 21 bs) lj
              _ _ _ _ _ _ _ _ _ BU1 BL1 LE _ GOT SHV MI eq_refl).
    all: unfold DgWalkXA.SP0, DgWalkXA.app_buf in *; rewrite ?USP.
    all: try (unfold app_buf22 in *; lia).
    all: try (replace (bv_unsigned sp - 80 - 80)%Z with (bv_unsigned sp - 160)%Z by lia; exact ST).
    all: try exact KPc.
    all: replace (- K0 - 0 + K0 + 0 + K0 - K0 + K0 - K0 + K0)%Z with K0 by lia; exact KC. }
  cbv beta. intros ms' P. unfold DgWalkXA.dg_post, DgWalkXA.DG_W, DgWalkXA.SP0 in P. rewrite USP in P.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & res & len & kappa & bs2 & -> & MUc & WMc & MI2 & ST2 & BU1' & BL1' & LE2 & LR & KC2 & KR & RES).
  replace (bv_unsigned sp - 80 - 80)%Z with (bv_unsigned sp - 160)%Z in ST2, MUc by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  replace (ret_pc (Z_to_bv 64 0xc7e9c)) with (Z_to_bv 64 0xc7e9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

  pose proof (g3_sh_read m2 lenp (Z.shiftr lenp 3 + 2147450880) ltac:(unfold G3_W; exact MU) ltac:(lia) eq_refl SHL) as SHl.
  do 4 zstep. if_cases KL0; [cbv in KL0; discriminate | ]. clear SHl.
  zstep. rewrite sx32_small by lia.
  zstep.
  pose proof (g3_sh_read m2 (buf + len) (Z.shiftr (buf + len) 3 + 2147450880) ltac:(unfold G3_W; exact MU) ltac:(lia) eq_refl (SHBUF len ltac:(lia))) as SHb.
  do 4 zstep. if_cases KB0; [cbv in KB0; discriminate | ]. clear SHb.
  assert (BUa : u8arr rsegs m2 buf (bs2 ++ [b21])) by (apply u8arr_app; split; [exact BU1' | rewrite BL1'; exact BU2]).
  clear BU1' BU2.
  assert (BLa : length (bs2 ++ [b21]) = 22%nat) by (rewrite length_app, BL1'; reflexivity).
  pose proof (u8arr_store_ok rsegs m2 buf (bs2 ++ [b21]) len (Z_to_bv 64 (buf + len)) BUa ltac:(rewrite BLa; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
  zstep.
  replace (write_to_mem m2 (Z_to_bv 64 (buf + len)) (le1 (Z_to_bv 64 0))) with (write_to_mem m2 (wa (buf + len)) [Z_to_bv 8 0])
    by (f_equal; symmetry; apply le1_lit).
  pose proof (u8arr_write rsegs m2 buf (bs2 ++ [b21]) len (Z_to_bv 8 0) BUa ltac:(rewrite BLa; lia)) as BU'.
  clear BUa. store_done.
  lazymatch goal with FRx : rw_cells rsegs ?mm (bv_unsigned sp - 72) _ |- _ =>
    assert (FRf : rw_cells rsegs mm (bv_unsigned sp - 80) ([C8 (Z_to_bv 64 kp)] ++ [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))
      by (apply rw_cells_app; split; [exact KPc | cbn [cells_size csize Nat.add]; replace (bv_unsigned sp - 80 + Z.of_nat 8)%Z with (bv_unsigned sp - 72)%Z by lia; exact FRx]) end.
  clear KPc FR. cbn [app] in FRf. rename FRf into FR.
  do 11 zstep.
  replace (Z_to_bv 64 (bv_unsigned sp - 80 + 80)) with sp by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  release_frame FR ST2 (bv_unsigned sp).
  finish.
  all: try exact BU'.
  all: try exact LE2.
  all: try exact KC2.
  all: try (rewrite upd_length; exact BLa).
  all: try (apply nth_error_upd_same; rewrite BLa; lia).
  all: lia.
Qed.

Lemma g3_mul : forall (acw bcw adw bdw acp bcp adp bdp acm bcm adm bdm : Z) (s mk : Z) (F' : bvmap 5 word) fc (m : word -> option byte) (bs : list byte) lj kj j8,
  frm0 fc -> stk rsegs m (GSP - 160) (GSP - 80) ->
  rw_cells rsegs m (GSP - 80) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch G3_W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  u8arr rsegs m buf bs -> length bs = 22%nat -> rw_cells rsegs m lenp [C4 lj] -> rw_cells rsegs m kp [C4 kj] ->
  ro_cells rsegs m 0x160c18 [C8 (Z_to_bv 64 0x169ef8)] -> ro_cells rsegs m 0x169ef8 [C8 (Z_to_bv 64 2147450880)] ->
  (0 <= acw <= 18446744065119617025)%Z -> (0 <= bcw <= 18446744065119617025)%Z -> (0 <= adw <= 18446744065119617025)%Z -> (0 <= bdw <= 18446744065119617025)%Z ->
  (0 <= acp <= 18446744065119617025)%Z -> (0 <= bcp <= 18446744065119617025)%Z -> (0 <= adp <= 18446744065119617025)%Z -> (0 <= bdp <= 18446744065119617025)%Z ->
  (0 <= acm <= 18446744065119617025)%Z -> (0 <= bcm <= 18446744065119617025)%Z -> (0 <= adm <= 18446744065119617025)%Z -> (0 <= bdm <= 18446744065119617025)%Z ->
  Z.land bcw 4294965248 = (bcw mod 4294967296)%Z -> Z.land bcp 4294966272 = (bcp mod 4294967296)%Z ->
  (56 <= s <= 59)%Z -> (-307 <= mk <= 325)%Z ->
  (1 <= mcode acm adm bcm bdm)%Z -> (mcode acm adm bcm bdm <= mcode acw adw bcw bdw)%Z -> (mcode acw adw bcw bdw <= mcode acp adp bcp bdp)%Z ->
  (mcode acp adp bcp bdp <= 2 ^ 64 - 2)%Z -> (2 ^ 62 <= mcode acp adp bcp bdp + 1)%Z ->
  forall cl ml, (0 <= cl < 2 ^ 32)%Z -> (0 <= ml < 2 ^ 32)%Z ->
  evt rsegs g3_post (MS (mkR ra (Z_to_bv 64 (GSP - 80)) gp tp (Z_to_bv 64 bdp) (Z_to_bv 64 (- s - 64)) (Z_to_bv 64 4294965248) (Z_to_bv 64 lenp) (Z_to_bv 64 buf)
        (Z_to_bv 64 bcm) (Z_to_bv 64 (cl * 4294967296)) (Z_to_bv 64 kp) (Z_to_bv 64 ml) (Z_to_bv 64 (- s - 53)) (Z_to_bv 64 mk) (Z_to_bv 64 bdw) (Z_to_bv 64 adp)
        (Z_to_bv 64 2147450880) (Z_to_bv 64 acw) (Z_to_bv 64 acp) (Z_to_bv 64 bcw) (Z_to_bv 64 bcp) (Z_to_bv 64 bdm) s8 s9 s10 s11
        (Z_to_bv 64 4294966272) (Z_to_bv 64 adw) (Z_to_bv 64 adm) (Z_to_bv 64 acm))
     F' (Z_to_bv 64 0xc7dbc) fc None m (seg_rom rsegs)).
Proof using All.
  intros until j8. intros FRM ST FR MU WM MI BU BL LE KC GOT SHV Racw Rbcw Radw Rbdw Racp Rbcp Radp Rbdp Racm Rbcm Radm Rbdm Eb Ep Hs Hmk HWm HW1 HW2 HW3 HW4 cl ml Hcl Hml.
  unfold G3_W in MU.
  pose proof (shr32_range _ Racw) as Sacw. pose proof (shr32_range _ Rbcw) as Sbcw. pose proof (shr32_range _ Racp) as Sacp. pose proof (shr32_range _ Rbcp) as Sbcp.
  pose proof (shr32_range _ Racm) as Sacm. pose proof (shr32_range _ Rbcm) as Sbcm. pose proof (shr32_range _ Radw) as Sadw. pose proof (shr32_range _ Rbdw) as Sbdw.
  pose proof (shr32_range _ Radp) as Sadp. pose proof (shr32_range _ Rbdp) as Sbdp. pose proof (shr32_range _ Radm) as Sadm. pose proof (shr32_range _ Rbdm) as Sbdm.
  pose proof (Z.mod_pos_bound bcw 4294967296 ltac:(lia)) as Mbcw. pose proof (Z.mod_pos_bound bcp 4294967296 ltac:(lia)) as Mbcp.
  pose proof (Z.mod_pos_bound bcm 4294967296 ltac:(lia)) as Mbcm. pose proof (Z.mod_pos_bound adw 4294967296 ltac:(lia)) as Madw.
  pose proof (Z.mod_pos_bound adp 4294967296 ltac:(lia)) as Madp. pose proof (Z.mod_pos_bound adm 4294967296 ltac:(lia)) as Madm.
  do 2 zstep. rewrite Eb.
  do 11 zstep. rewrite Ep.
  do 42 zstep.
  zstep.
  fold (mcode acw adw bcw bdw) (mcode acp adp bcp bdp) (mcode acm adm bcm bdm).
  rewrite !(ezext s 64), !(ezext s 53) by lia.
  rewrite (negw_small mk Hmk) in KC.
  unfold G3_W in MU.
  eapply g3_call; try eassumption; lia.
Qed.
End G3A.
