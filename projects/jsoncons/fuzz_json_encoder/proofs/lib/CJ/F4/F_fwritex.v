(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed fwritex_call, fwritex_spec, memcpy_callZ and 3 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/CJ/F8/F_fwritex.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 50-57, 63-70, 76-79, 102-106, 139-231, 275-289. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F4 Require Import F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec SeqExec Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Pm4RegionPoisoned Pm4AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJMX Require Import ShZero QcF IcptCells IcptMemcpyZ.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_memcpy; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @FILE_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @or]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @wfile]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Logic; @not]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @wview]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @iff_Transitive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf_app]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @Morphisms; @respectful]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @wr_at_app]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_length]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_app]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Numbers; @BinNums; @N]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @ZMicromega; @SplitProof]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @swrap32_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_memcpy; @memcpy_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @memcpy_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_memcpy; @memcpy_spec]; [@Corelib; @Init; @Peano; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @aenv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @QcF; @shk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @ShZero; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @ShZero; @zsh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @fwritex_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @aenv_rt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4RegionPoisoned; @rt_layout_globs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @aenv_mc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4AsanMemcpy; @mc_icpt_globs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_split_CB]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @sum_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @mk_CB_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @rw_cells_app]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @high_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @rt_layout_globs_munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @mc_icpt_globs_munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @QcF; @shk_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptCells; @high_in_app_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @ShZero; @zsh_transport]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @QcF; @shk_k]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4RegionPoisoned; @SB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyZ; @icpt_memcpy_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyZ; @icpt_memcpy_callZ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @ShZero; @app_in_app8]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyC; @lS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyC; @lD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyC; @fS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @ShZero; @zsh_porta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJMX; @IcptMemcpyC; @fD]; [@Corelib; @Init; @Logic; @proj2]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@Stdlib; @Lists; @List; @firstn_all2]; [@Stdlib; @Lists; @List; @length_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Stdlib; @Lists; @List; @length_app]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @sx32_neg]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @fwritex_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F4; @F_fwritex; @fwritex_spec]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition fwritex_entry := 0x149d68%Z.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S60|30;!1+0!1,10!1+21!1,1|600;}1}O$fl0;R1$j1;R2$WEND;R+3$WPOS;R+3$j2;R2$lbfw;R!1+03!3,4+5!2,64!3,41#6!1,71!3,4+5!2,65#5!3,4+5!1,8!2'93#4!3,4+5!1,8!2'93#3!3,4+5!2,6}_6#2!3,4+5!1,:#1!1,7+5").

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
    (B : Z) (content junk : list byte) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 9 "S>0|600;!1,10!1+01|30;!1,13!1+04!1+25!2'B5#2!2'@#3!1'A7!2'B5#1!2'@8!1'A9|500;|O00000000;|10;$m;R%~R2!1+;5$Fp;R+3$fl0;R5$j1;R6$j2;R6$lbfw;R2$B;R+3$content;R6$junk;R6!2+<!4'='>#9#8!6'?#7#6:8#5#4!2+<!4'='>#9#3!3,4+5!2,67#2!3,4+5!2,69#1!1,7+5!2+<!3+C+3!2'D!2'E4#7!1,F;,G!2+<!2'H!1,F<!2'I!2'E1#4!1,F|P00000000;!2+<!2'J,G#3!2+<!2'J:!2'K!1,F=!1,F0!2+L!2'H!2'@#8!1,F|714;#3!2'H:#8").

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 29 "S>0!1,1|600;!1+00|21;|500;|30;!1+0!1,14!1+25%~R1!1+;5!2'B5#B!1'A8!2+V+3+3!2'E0#\!2'X;!1,F|;0f8;!2'@#F!1'A!2'B5#E$ra;R1$sp;R1$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R!2'M!1,121$fc;R!1+0!1,13$Fp;R+3$fl0;R5$j1;R6$j2;R6$lbfw;R1$B;R+3$content;R6$junk;R6$S;R+3$bs;R6$m;R7$ms';R+N!2+O1$t0;R1!2+O1$t1;R1!2+O1$t2;R1!2+O1$a1;R1!2+O1$a2;R1!2+O1$a3;R1!2+O1$a4;R1!2+O1$a5;R1!2+O1$a6;R1!2+O1$a7;R1!2+O1$t3;R1!2+O1$t4;R1!2+O1$t5;R1!2+O1$t6;R1!2+O7$m';R7!2+<!3+C+N#@!7'P!O'Q#^0#\#[#Z#?#>#=#Y#X!2'909#<#;#:#9#8#7#6#W#V#U#T#S#R#Q#P#O#N#5#4#3#2#M!1'R#^0#L!1,S1#1!1'T'>!2+<!3'U!3,4:!4,W+3+3<;!3,4:!4,W+3+3=!2'@=9!3,4:!4,W+3+3!2'@#K!1,F|508;!2'@#K!1,F|510;!1,7:#A#1!2+<!3'Y'>#A#1!2+<!2'Z'>#1!2+<!4'['>#1<;!2+<!9'\#1#K#J#I#H#G#F!3'^05#E#B!3'^158#D!4'^2'>#1#C#B").

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
  (9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
  intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64)%Z with 18446744073709551616%Z in *.
  Z.div_mod_to_equations. lia.
Qed.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 23 "S80!1,1|600;!1+00|500;|30;!1+0!1,13%~R1!1+;4!2+V+3+3!2'E0#C$ra;R1$sp;R1$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R!2'M!1,1|21;1$fc;R!1+0!1,12$D;R+3$a1;R1$a2;R1$src;R!1+24$m;R5$ms';R+N!2+O1$t0;R1!2+O1$t1;R1!2+O1$t2;R1!2+O1$a1';R1!2+O1$a2';R1!2+O1$a3;R1!2+O1$a4;R1!2+O1$a5;R1!2+O1$a6;R1!2+O1$a7;R1!2+O1$t3;R1!2+O1$t4;R1!2+O1$t5;R1!2+O1$t6;R1!2+O5$m';R5!2+<!3+C+N#@!7'P!O'Q#W#V#U#T#?#>#=#S#R!2'90#E#<#;#:#9#8#7#6#Q#P#O#N#M#L#K#J#I#H#5#4#3#2#G!1'R#W#F!1,S1#1!1'T'>!2+<!3'U!3,46!4,W+3+3#E!2'@#E7!1,76#A#1!2+<!3'Y'>#A#1!2+<!2'Z'>#1!2+<!4'='>#1#E!3,4+5!2,6!1'`H7#B!1,7+5!4'^2'>#1!2'E0#D#B").
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte),
  bytes_at rsegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells rsegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (0 <= D < 2^64)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152aa0) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST HD SEP MI.
  assert (E : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D)); rewrite ?E; eauto. }
  intros ms' P. unfold memcpy_post in P. rewrite !E in P. exact P.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
  bytes_at rsegs m (bv_unsigned a0) bs ->
  Z.of_nat (length bs) = bv_unsigned a1 ->
  (length bs <= length junk)%nat ->
  stk rsegs m (bv_unsigned sp - 2296) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  (0x10007fff8000 + 2296 <= bv_unsigned sp <= 0x7fffffffff00)%Z ->
  (bv_unsigned a2 + 148 <= bv_unsigned sp - 2296 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= bv_unsigned sp - 2296 \/ bv_unsigned sp <= B)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 2296 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
   \/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->

  aenv m ->
  shk rsegs m (bv_unsigned a0) (Z.of_nat (length bs)) -> app (bv_unsigned a0) (Z.of_nat (length bs)) ->
  zsh m (B + Z.of_nat (length content)) (B + Z.of_nat (length content) + Z.of_nat (length bs)) ->
  (0x10007fff8000 <= B /\ B + Z.of_nat (length content) + Z.of_nat (length junk) <= 0x7fffffffff00)%Z ->
  (0x10007fff8000 <= bv_unsigned a2 /\ bv_unsigned a2 + 148 <= 0x7fffffffff00)%Z ->
  (Z.of_nat (length bs) <= 2 ^ 40)%Z ->
  evt rsegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x149d68) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI SPLO SEP1 SEP2 SEP3 SEP4 SEP5 AE ZS AS ZD HBh HFh LB40. pose proof (aenv_rt _ AE) as RTG. pose proof (aenv_mc _ AE) as MCI.
  pose_word_ranges.
  set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (S := bv_unsigned a0) in *.
  set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  pose proof (munch_refl [(bv_unsigned sp - 2296, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 64%nat ST.
  do 8 zstep.
  zstep. zstep. zstep. zstep.
  zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
  { exfalso. lia. }
  zstep. zstep.
  zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
  2:{ exfalso. lia. }
  zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
  2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
  zstep. zstep.

  apply (rw_cells_split_CB rsegs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
  cbn [mk_CB_cells app] in BUF.
  apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
  cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
  apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
  cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.
  assert (HW : high_all [(bv_unsigned sp - 2296, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z) by (cbn; lia).
  assert (RTG1 := rt_layout_globs_munch _ _ _ HW MU RTG). assert (MCI1 := mc_icpt_globs_munch _ _ _ HW MU MCI).
  lazymatch type of MU with munch _ _ ?mm =>
    assert (ZS1 : shk rsegs mm S (Z.of_nat lb));
    [ eapply shk_transport; [exact ZS | exact MU | apply high_in_app_all, HW | exact AS] | ];
    assert (ZD1 : (0 < Z.of_nat lb)%Z -> zsh mm (B + Z.of_nat nc) (B + Z.of_nat nc + Z.of_nat lb));
    [ intros Hp; eapply zsh_transport; [exact ZD | exact MU | apply high_in_app_all, HW | unfold app; right; lia | lia] | ]
  end.
  destruct (shk_k _ _ _ _ ZS1) as (kS0 & HLSk & HkSk & HZSk & HWSk).
  zstep. call icpt_memcpy_callZ.
  1:{ exact SRC. }
  1:{ unfold lb in LEN. rewrite <- LEN, Nat2Z.id. reflexivity. }
  1:{ rewrite <- LEN, Nat2Z.id. exact BUFb. }
  1:{ lia. } 1:{ lia. } 1:{ assumption. }
  1:{ replace (bv_unsigned sp + -64 - 2232)%Z with (bv_unsigned sp - 2296)%Z by lia. exact ST. }
  1:{ lia. }
  1:{ apply app_in_app8; [rewrite <- LEN; exact AS | lia]. }
  1:{ apply app_in_app8; [unfold app; right; rewrite <- LEN; lia | lia]. }
  1:{ lia. }
  1:{ unfold IcptMemcpyC.lS, Pm4RegionPoisoned.SB. unfold S in *. pose proof (Z.div_le_mono (bv_unsigned a0 + bv_unsigned a1 - 1) 0x7fffffffff00 8 ltac:(lia) ltac:(unfold app in AS; rewrite <- LEN; lia)) as Hdv. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in Hdv. lia. }
  1:{ unfold IcptMemcpyC.lD, Pm4RegionPoisoned.SB. rewrite unsigned_lit by lia. pose proof (Z.div_le_mono (B + Z.of_nat nc + bv_unsigned a1 - 1) 0x7fffffffff00 8 ltac:(lia) ltac:(rewrite <- LEN; lia)) as Hdv. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in Hdv. lia. }
  1:{ intros _. rewrite <- LEN. lia. }
  1:{ intros _. rewrite <- LEN. lia. }
  1:{ reflexivity. }
  1:{ exact RTG1. }
  1:{ exact MCI1. }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fS, IcptMemcpyC.lS. rewrite <- LEN. exact (HZSk Hp). }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fS, IcptMemcpyC.lS. rewrite <- LEN. exact (HLSk Hp). }
  1:{ unfold S. rewrite <- LEN. exact HkSk. }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fS, IcptMemcpyC.lS. rewrite <- LEN. exact (HWSk Hp). }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fD, IcptMemcpyC.lD. rewrite unsigned_lit by lia. rewrite <- LEN. exact (proj1 (zsh_porta rsegs _ (B + Z.of_nat nc) (Z.of_nat lb) (ZD1 Hp) Hp ltac:(unfold app; right; lia))). }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fD, IcptMemcpyC.lD. rewrite unsigned_lit by lia. rewrite <- LEN. exact (proj1 (proj2 (zsh_porta rsegs _ (B + Z.of_nat nc) (Z.of_nat lb) (ZD1 Hp) Hp ltac:(unfold app; right; lia)))). }
  1:{ left; reflexivity. }
  1:{ intros Hp. rewrite <- LEN in Hp. unfold IcptMemcpyC.fD, IcptMemcpyC.lD. rewrite unsigned_lit by lia. rewrite <- LEN. exact (proj2 (proj2 (zsh_porta rsegs _ (B + Z.of_nat nc) (Z.of_nat lb) (ZD1 (proj1 Hp)) (proj1 Hp) ltac:(unfold app; right; lia)))). }

  lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  replace (bv_unsigned sp + -64 - 2232)%Z with (bv_unsigned sp - 2296)%Z in ST by lia.
  rewrite <- !LEN in *. rewrite !Nat2Z.id in *.
  rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
  match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb end.
  zstep. zstep. zstep. zstep.
  replace (0 + bv_unsigned a1)%Z with (Z.of_nat lb) by lia.
  replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
  do 9 zstep. release_frame FR ST (bv_unsigned sp).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BUF : rw_cells rsegs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
    [ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [ exact BUFa |];
      cbn [cells_size csize]; rewrite Nat.add_0_r;
      apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [ exact BUFb |];
      cbn [cells_size csize]; rewrite Nat.add_0_r; exact BUFc
    | apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
      rewrite Nat.add_0_r, app_nil_r in BUF; clear BUFa BUFb BUFc ]
  end.
  apply evt_done. unfold fwritex_post.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [ ms_eq | ].
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try (replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; assumption).

  unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
  replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
  replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FC by lia.
  split; [exact FC|]. split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.

Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 29 "S=0!1,1|600;!1+00|21;|500;|30;!1+0!1,14!1+25%~R1!1+;5!2'B5#B!1'A8!2+V+3+3!2'X#\!1,F|;0f8;!2'@#F!1'A!2'B5#E$ra;R1$q;R+3$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R!2'M!1,121$fc;R!1+0!1,13$Fp;R+3$fl0;R5$j1;R6$j2;R6$lbfw;R1$B;R+3$content;R6$junk;R6$S;R+3$bs;R6$m;R7$ms';R+N!2+O1$t0;R1!2+O1$t1;R1!2+O1$t2;R1!2+O1$a1;R1!2+O1$a2;R1!2+O1$a3;R1!2+O1$a4;R1!2+O1$a5;R1!2+O1$a6;R1!2+O1$a7;R1!2+O1$t3;R1!2+O1$t4;R1!2+O1$t5;R1!2+O1$t6;R1!2+O7$m';R7!2+<!3+C+N#@!7'P!O'Q#^0!2'90#\#[#Z#?#>#=#Y#X!2'909#<#;#:#9#8#7#6#W#V#U#T#S#R#Q#P#O#N#5#4#3#2#M!1'R#^0#L!1,S1#1!1'T'>!2+<!3'U!3,4:!4,W+3+3;#\!3,4:!4,W+3+3<!2'@<9!3,4:!4,W+3+3!2'@#K!1,F|508;!2'@#K!1,F|510;!1,7:#A#1!2+<!3'Y'>#A#1!2+<!2'Z'>#1!2+<!4'['>#1;#\!2+<!9'\#1#K#J#I#H#G#F!3'^05#E#B!3'^158#D!4'^2'>#1#C#B").

Lemma fwritex_call : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  bytes_at rsegs m S bs ->
  Z.of_nat (length bs) = L ->
  (length bs <= length junk)%nat ->
  stk rsegs m (q - 2296) q ->
  mem_inv rsegs m ->
  (0x10007fff8000 + 2296 <= q <= 0x7fffffffff00)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
  (Fp + 148 <= q - 2296 \/ q <= Fp)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= q - 2296 \/ q <= B)%Z ->
  (S + L <= q - 2296 \/ q <= S)%Z ->
  (S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
  (S + L <= Fp \/ Fp + 148 <= S)%Z ->

  aenv m ->
  shk rsegs m S L -> app S L ->
  zsh m (B + Z.of_nat (length content)) (B + Z.of_nat (length content) + L) ->
  (0x10007fff8000 <= B /\ B + Z.of_nat (length content) + Z.of_nat (length junk) <= 0x7fffffffff00)%Z ->
  (0x10007fff8000 <= Fp /\ Fp + 148 <= 0x7fffffffff00)%Z ->
  (L <= 2 ^ 40)%Z ->
  evt rsegs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk S bs m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x149d68) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros WF SRC LEN LE ST MI Hq HS HSL HFp SEP1 SEP2 SEP3 SEP4 SEP5 AE ZS AS ZD HBh HFh LB40. pose proof (aenv_rt _ AE) as RTG. pose proof (aenv_mc _ AE) as MCI.
  assert (HF : (Fp + 148 <= 2^64)%Z).
  { destruct WF as (FC & _). pose proof (rw_cells_bound _ _ _ _ FC) as BF. unfold FILE_cells in BF. cbn [cells_size csize Nat.add length] in BF.
    lia. }
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (El : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  assert (ZS' : shk rsegs m S (Z.of_nat (length bs))) by (rewrite LEN; exact ZS).
  assert (AS' : app S (Z.of_nat (length bs))) by (rewrite LEN; exact AS).
  assert (ZD' : zsh m (B + Z.of_nat (length content)) (B + Z.of_nat (length content) + Z.of_nat (length bs))) by (rewrite LEN; exact ZD).
  assert (LB' : (Z.of_nat (length bs) <= 2 ^ 40)%Z) by lia.
  { eapply (fwritex_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp)); rewrite ?Eq, ?Es, ?El, ?Ef; eauto; lia. }
  intros ms' P. unfold fwritex_post in P. rewrite !Eq, !Es, !Ef in P. exact P.
Qed.
