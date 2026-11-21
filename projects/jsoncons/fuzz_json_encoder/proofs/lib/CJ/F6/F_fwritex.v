(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed fwritex_call, fwritex_spec, memcpy_callZ and 3 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import F_memcpy.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Datatypes; @option]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_memcpy; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @wfile]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Logic; @conj]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @not]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @wview]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @iff_Transitive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf_app]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @Morphisms; @respectful]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @wr_at_app]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_length]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Numbers; @BinNums; @N]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @ZMicromega; @SplitProof]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @swrap32_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_memcpy; @memcpy_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @memcpy_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_memcpy; @memcpy_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @FILE_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Corelib; @Init; @Peano; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @fwritex_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_split_CB]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @sum_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @mk_CB_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @rw_cells_app]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @memcpy_callZ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@Stdlib; @Lists; @List; @firstn_all2]; [@Stdlib; @Lists; @List; @length_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Stdlib; @Lists; @List; @length_app]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @sx32_neg]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @fwritex_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @F_fwritex; @fwritex_spec]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition fwritex_entry := 0xaf8a4%Z.

(* [comment removed for export] *)
Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
  [CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

(* [comment removed for export] *)
Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
    (B : Z) (content junk : list byte) : Prop :=
  rw_cells rsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
                                          (B + Z.of_nat (length content)) j2 lbfw)
  /\ rw_cells rsegs m B [CB (length content) content; CB (length junk) junk]
  /\ Z.land (bv_unsigned fl0) 32 = 0%Z                       (* [comment removed for export] *)
  /\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z        (* [comment removed for export] *)
  /\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z   (* [comment removed for export] *)
  /\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 29 "S?0|600;!1,10!1+01|21;|500;|30;!1+0!1,15!1+46%~R2!1+56!2'>6#B!1'=9!2+E+3+3!2'H1#\!2'G<!1,I0!2'J#F!1'=!2'>6#E$ra;R2$sp;R2$gp;R2$tp;R2$s0;R2$s1;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$F;R!2'2!1,132$fc;R!1+0!1,14$Fp;R+3$fl0;R6$j1;R7$j2;R7$lbfw;R2$B;R+3$content;R7$junk;R7$S;R+3$bs;R7$m;R8$ms';R+6!2+72$t0;R2!2+72$t1;R2!2+72$t2;R2!2+72$a1;R2!2+72$a2;R2!2+72$a3;R2!2+72$a4;R2!2+72$a5;R2!2+72$a6;R2!2+72$a7;R2!2+72$t3;R2!2+72$t4;R2!2+72$t5;R2!2+72$t6;R2!2+78$m';R8!2+8!3+9+6#@!7':!O';#^0#\#[#Z#?#>#=#Y#X!2'<1:#<#;#:#9#8#7#6#W#V#U#T#S#R#Q#P#O#N#5#4#3#2#M!1'?#^0#L!1,@2#1!1'A'B!2+8!3'C!3,D;!4,F+3+3=<!3,D;!4,F+3+3>!2'J>:!3,D;!4,F+3+3!2'J#K!1,I|508;!2'J#K!1,I|510;!1,K;#A#1!2+8!3'L'B#A#1!2+8!2'M'B#1!2+8!4'N'B#1=<!2+8!9'O#1#K#J#I#H#G#F!3'P6#E#B!3'Q69#D!4'R'B#1#C#B").

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : Z) (a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at rsegs m' (bv_unsigned a1) src.
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
        F (Z_to_bv 64 0xba65c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST HD SEP MI.
  assert (E : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D)); rewrite ?E; eauto. }
  intros ms' P. unfold memcpy_post in P. rewrite !E in P. exact P.
Qed.

(* [comment removed for export] *)
Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
  bytes_at rsegs m (bv_unsigned a0) bs ->
  Z.of_nat (length bs) = bv_unsigned a1 ->
  (length bs <= length junk)%nat ->
  stk rsegs m (bv_unsigned sp - 64) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  (64 <= bv_unsigned sp)%Z ->
  (bv_unsigned a2 + 148 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= B)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
   \/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->
  evt rsegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) SRC LEN LE ST MI SPLO SEP1 SEP2 SEP3 SEP4 SEP5.
  pose_word_ranges.
  set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (S := bv_unsigned a0) in *.
  set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
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
  zstep. call memcpy_callZ.
  1:{ exact SRC. }
  1:{ unfold lb in LEN. rewrite <- LEN, Nat2Z.id. reflexivity. }
  1:{ rewrite <- LEN, Nat2Z.id. exact BUFb. }
  1:{ lia. } 1:{ lia. } 1:{ assumption. }
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

(* [comment removed for export] *)
Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
    (S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 64, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 64) q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
    /\ bytes_at rsegs m' S bs.

Lemma fwritex_call : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  bytes_at rsegs m S bs ->
  Z.of_nat (length bs) = L ->
  (length bs <= length junk)%nat ->
  stk rsegs m (q - 64) q ->
  mem_inv rsegs m ->
  (64 <= q < 2^64)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
  (Fp + 148 <= q - 64 \/ q <= Fp)%Z ->
  (B + Z.of_nat (length content) + Z.of_nat (length junk) <= q - 64 \/ q <= B)%Z ->
  (S + L <= q - 64 \/ q <= S)%Z ->
  (S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
  (S + L <= Fp \/ Fp + 148 <= S)%Z ->
  evt rsegs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk S bs m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf8a4) fc None m (seg_rom rsegs)).
Proof.
  intros until bs. intros WF SRC LEN LE ST MI Hq HS HSL HFp SEP1 SEP2 SEP3 SEP4 SEP5.
  assert (HF : (Fp + 148 <= 2^64)%Z).
  { destruct WF as (FC & _). pose proof (rw_cells_bound _ _ _ _ FC) as BF. unfold FILE_cells in BF. cbn [cells_size csize Nat.add length] in BF.
    lia. }
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (El : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (fwritex_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp)); rewrite ?Eq, ?Es, ?El, ?Ef; eauto; lia. }
  intros ms' P. unfold fwritex_post in P. rewrite !Eq, !Es, !Ef in P. exact P.
Qed.
