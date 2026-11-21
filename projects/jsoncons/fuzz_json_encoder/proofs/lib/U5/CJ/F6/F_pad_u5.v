(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed memset_callZ, pad_call, pad_model and 2 more; added mk_wfile; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/U/CJ/F10/F_pad_u.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 31-34, 53-63, 98-199, 233-239. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memcpy_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fwritex_u5.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memcpy_u5; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @got_ssp]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @ssp_guard]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Datatypes; @orb]; [@Corelib; @Init; @Datatypes; @negb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @LEFT_ADJ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @ZERO_PAD]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Datatypes; @prod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @pad_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @PAD_FUEL]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @out]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Prelim; @zrepeat]; [@Corelib; @Init; @Datatypes; @None]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @Lists; @List; @app_nil_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec0]; [@Corelib; @Init; @Datatypes; @reflect]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @pad_loop_body]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @not]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @pad]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @pad_n]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memset_u5; @memset_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @memset_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memset_u5; @memset_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memset_u5; @rsegs]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@Corelib; @Lists; @ListDef; @repeat]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @wfile]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @ssp_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @pad_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @FILE_cells]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @NOT]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @signed_of_Z]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @Lists; @List; @skipn_0]; [@Stdlib; @ZArith; @Znat; @Z2Nat; @inj_0]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @sext32]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_split_CB]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @sum_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @mk_CB_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @rw_cells_app]; [@Stdlib; @ZArith; @Znat; @Z2Nat; @id]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @memset_callZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @rw_cells_bytes_at']; [@Stdlib; @Lists; @List; @repeat_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @fwritex_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @fwritex_call]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_bv]; [@Corelib; @Init; @Datatypes; @Lt]; [@Corelib; @Init; @Datatypes; @Gt]; [@Stdlib; @NArith; @BinNat; @N; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @sext32_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @Z_to_bv_swrap32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @pad_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @pad_spec]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition pad_entry := 0xb4850%Z.

(* [comment removed for export] *)
Definition got_ssp := 0xca220%Z.
Definition ssp_guard := 0xfd280%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!1,1|600;!1+00|30;!1,<+8$m;R%~R1!1+2!1+0!1,12$canary;R1!2+3!4'4'5#2'6!3,7+8!1,9!2':0';3!4'4'5#2';!3,7+8!1,9#13").

(* [comment removed for export] *)
Definition pad_n (w l fl : Z) : Z :=
  if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
  pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
  intros o c w l fl H. unfold pad, pad_n.
  destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
  change PAD_FUEL with (S 63). cbn [pad_loop].
  destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
  rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
  mem_inv rsegs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  evt rsegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbe5c8) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST MI Hq HD HC HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memset_spec ra (Z_to_bv 64 q)); rewrite ?Ed, ?En; eauto. }
  intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 30 "S>0!1,1|600;!1+00|21;|500;|30;!1,14!1+05!1+=6%~R1!1+26!2+N+>+>!2'^Y0#^1!2'@:!1,A|870;!2'_:#H!1'_B!2'_G6#G!1'^N#C$ra;R1$sp;R1$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R!2'^L!1,121$fc;R!1+0!1,13$Fp;R+>$fl0;R6$j1;R7$j2;R7$lbfw;R1$B;R+>$content;R7$junk;R7$canary;R1$C;R+>$n;R+>$m;R8$ms';R+_5!2+_71$t0;R1!2+_71$t1;R1!2+_71$t2;R1!2+_71$a0;R1!2+_71$a1;R1!2+_71$a2;R1!2+_71$a3;R1!2+_71$a4;R1!2+_71$a5;R1!2+_71$a6;R1!2+_71$a7;R1!2+_71$t3;R1!2+_71$t4;R1!2+_71$t5;R1!2+_71$t6;R1!2+_78$m';R8!2+3!3+L+_5#A!7'_0!O'_1#^2#^1#^0#\#@#?#>#[#Z#=#<#;#:#9#8#7#6#Y#X#W#V#U#T#S#R#Q#P#5#4#3#2#O!1'_8#^2#N!1,T1#1!1'_2'5!2+3!3'_9!3,79!4,Q+>+>;:!3,79!4,Q+>+><!2'_:<#C!3,79!4,Q+>+>!2'_:#M!1,A|508;!2'_:#M!1,A|510;!1,<9#B#1!2+3!3'_;'5#B#1!2+3!2'^O'5#1!2+3!4'_H'5#1;:!2+3!9'_I#1#M#L#K#J#I#H!3'U6#G!3'_<6!2':5#D=!3'_J6=#F!2'_K#1#E").

(* [comment removed for export] *)
Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Lemma pad_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk rsegs m (bv_unsigned sp - 368) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
  evt rsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4850) fc None m (seg_rom rsegs)).
Proof.
  intros until canary. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB.
  pose proof WF as WF0. destruct WF as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb).
  pose_word_ranges.
  set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 304%nat ST.
  do 6 zstep. zstep. zstep. zstep. zstep. zstep.

  assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
    n = pad_n W L FL ->
    mem_inv rsegs m1 ->
    rw_cells rsegs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m1 (bv_unsigned sp - 368) (bv_unsigned sp + -304) ->
    munch [(bv_unsigned sp - 368, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
    wmono rsegs m m1 ->
    wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
    rw_cells rsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m1 ssp_guard [C8 canary] ->
    evt rsegs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1036928) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xb48f8) fc None m1 (seg_rom rsegs))).
  { intros until pad256. intros Hn MI1 FR1 ST1 MU1 WM1 WF1 GOT1 SSP1. unfold got_ssp, ssp_guard in GOT1, SSP1.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 6 zstep. zstep. release_frame FR1 ST1 (bv_unsigned sp).
    apply evt_done. unfold pad_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [ ms_eq | ].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [rewrite <- Hn; exact WF1 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT1 | exact SSP1]]. }

  Ltac mk_wfile FC BUF FLG LBF := split; [exact FC|]; split; [exact BUF|]; split; [exact FLG|]; split; [exact LBF|]; split; [lia|]; split; lia.
  assert (PN0 : (W <= L \/ Z.land FL 73728 <> 0)%Z -> pad_n W L FL = 0%Z).
  { intros HH. unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
  zstep. if_cases Kw; zify_cond Kw; rewrite !signed_of_Z in Kw by lia.
  -
    eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
    rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
  - zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    +
      eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
      rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
    + assert (PN : pad_n W L FL = (W - L)%Z).
      { unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
        destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
      rewrite PN in *. set (N := (W - L)%Z) in *.
      zstep. rewrite Z_to_bv_swrap32, (sext32_small (W - L)) by lia. fold N.
      zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ exfalso. revert Kn. rewrite ?unsigned_lit by lia. lia. }

      apply (rw_cells_split_CB rsegs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
      cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
      cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
      zstep. zstep. call memset_callZ.
      1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      rewrite (Z.mod_small C 256) in * by lia.
      match goal with MSC : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename MSC into FRa end.
      zstep. if_cases Kn2; zify_cond Kn2.
      2:{ exfalso. revert Kn2. rewrite ?unsigned_lit by lia. lia. }
      zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      { exfalso. exact (Ke FLG). }
      zstep. zstep. zstep. zstep.
      pose proof (rw_cells_bytes_at' _ _ _ _ FRa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.

      set (bsP := repeat (Z_to_bv 8 C) (Z.to_nat N)) in *.
      assert (LbsP : length bsP = Z.to_nat N) by (subst bsP; apply repeat_length).
      set (nc := length content) in *. set (nj := length junk) in *.

      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_call;
          [ mk_wfile FC BUF FLG LBF
          | exact SRC
          | rewrite LbsP, Z2Nat.id by lia; reflexivity
          | rewrite LbsP; lia
          | replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z by lia; exact ST
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -304 - 64)%Z _ |- _ =>
        replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z in X by lia end.
      match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
      match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FRb with rw_cells _ _ _ (?c2 :: ?rest) =>
        assert (FR : rw_cells rsegs mm (bv_unsigned sp + -304) ([] ++ [CB (Z.to_nat N) bsP; c2] ++ rest));
        [ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [ exact FRa' |];
          cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact FRb
        | apply rw_cells_merge in FR; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FR;
          rewrite app_nil_r in FR; replace (Z.to_nat N + (256 - Z.to_nat N + 0))%nat with 256%nat in FR by lia ]
      end end.
      unfold bsP in *. eapply EXIT; [ reflexivity | hyp | exact FR | hyp | hyp | hyp | hyp | unfold got_ssp, ssp_guard; hyp | unfold ssp_guard; hyp ].
Qed.

(* [comment removed for export] *)
Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - 368, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - 368) q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Lemma pad_call : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk rsegs m (q - 368) q ->
  mem_inv rsegs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  evt rsegs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4850) fc None m (seg_rom rsegs)).
Proof.
  intros until canary. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB.
  unfold ssp_guard in GLO.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; unfold ssp_guard; lia. }
  intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.
