(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed memcpy_callv, sn_write_spec; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/U/CJ/F10/F_sn_write_u.v, lines 63-68, 99-166. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memcpy_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fwritex_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_lib_u5.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import StoreFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @Lists; @List; @length_map]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @zb]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memset_u5; @rsegs]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_wf]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Numbers; @BinNums; @Z0]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memcpy_u5; @memcpy_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @memcpy_postv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memcpy_u5; @memcpy_spec]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memcpy_u5; @rsegs]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Prelim; @zlength]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Datatypes; @S]; [@Corelib; @Init; @Peano; @lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @sn_write_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @zb_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @Tauto; @X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @bytes_at_write_other_n]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @rw_cells_frame_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @munch_write_n]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @stk_write_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @rw_CB_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_of_rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @rw_cells_of_u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @u8arr_frame_n]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @upd_firstn_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @le1_zero]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_split_CB]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @sum_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @mk_CB_cells]; [@Corelib; @Init; @Logic; @proj1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @rw_cells_app]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_sn_write_u5; @memcpy_callv]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @Tauto; @NOT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@Stdlib; @Lists; @List; @app_nil_r]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Stdlib; @Lists; @List; @length_skipn]; [@Stdlib; @Lists; @List; @length_firstn]; [@Stdlib; @Lists; @List; @firstn_0]; [@Stdlib; @Lists; @List; @app_nil_l]; [@Stdlib; @Lists; @List; @skipn_firstn_comm]; [@Stdlib; @Lists; @List; @skipn_skipn]; [@Stdlib; @Lists; @List; @firstn_all2]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := F_memset_u5.rsegs.
Notation mem := (word -> option byte).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1,4|30;!1+30$l;R!1+0+1vd!4'2+11$z;R+1!2'50#1#1!3+6+7!2'81!1'9#1!2'8+1#1").
Qed.
Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90|30;!1+3!1,40!1,@+>!3,=+>!2,?#3#22!4'B'<#5#43!3,=+>!2,?#6#52!1'F5!1'I!2,?#9#8!1'F2$m;R%~R!1+3!1,4|600;!1+:1$A;R+1$n;R+7$bs;R!1+01$H0;R!4';'<#4#3!3,=+>!2,?#2#12!5'A4!4'C'<#5#4!1'D!1'E3!3+6+7!2'81#2#3$~R4$~R!4'C'<#6#5!1'D!1'E!3,=+>!2,?#4#32!2$H0;R!4'B'<#7#6!3,=+>!2,?#5#42!5'A6!4'G'<#8#7!1'H5%~R!4'C'<#8#7!1'D!1'E!3,=+>!2,?#6#52!3+6+7!2'81#6#7$~R6$~R!4'G'<#9#8!1'H!3,=+>!2,?#7#62!2$H0;R!1'F!3,=+>!2,?#8#72!5'A78%~R!4'G'<#;#:!1'H!3,=+>!2,?#9#82%~R!4'C'<#<#;!1'D!1'E!3,=+>!2,?#:#92!3+6+7!2'81#:#;$~R7$~R8!2$H;R!1'I!2,?#;#:$_H;R8$_H0;R!4'G'<#?#>!1'H!3,=+>!2,?#=#<2$_H1;R!4'C'<#@#?!1'D!1'E!3,=+>!2,?#>#=2#4#2#1#1#2#1#1#2#1#1").
Qed.
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1,4|30;!1+30!2,J!1+01!3,=1!2'50,K!1,@1").
Qed.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at rsegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at rsegs m Src src -> length src = Z.to_nat N -> rw_cells rsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^64)%Z -> (0 <= Src < 2^64)%Z -> (0 <= Dst < 2^64)%Z -> mem_inv rsegs m ->
  evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbe048) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in P. exact P.
Qed.



Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte) (m : mem) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 28 "SD0|600;!1,40!1+31|21;|500;|30;!1,45!1+36%~R2!1+:7!2+_1+1+1!2'^O1#[!1,T0!2'_4:;|40;!2'P#J!1,T|508;!2'P#J!1,T|518;!2'_7+1#D!1,@+>!1'9#D!3,=+>!1,_6!2'51#EA$ra;R2$sp;R2$gp;R2$tp;R2$s0;R2$s1;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$F;R!2'L!1,432$fc;R!1+3!1,44$Fp;R+1$CK;R+1$D;R+1$n;R+1$B;R+1$bufp;R+1$o;R!1+0+1$dn;R+7$junk;R!1+07$m;R8$ms';R+^Y!2+^[2$t0;R2!2+^[2$t1;R2!2+^[2$t2;R2!2+^[2$a1;R2!2+^[2$a2;R2!2+^[2$a3;R2!2+^[2$a4;R2!2+^[2$a5;R2!2+^[2$a6;R2!2+^[2$a7;R2!2+^[2$t3;R2!2+^[2$t4;R2!2+^[2$t5;R2!2+^[2$t6;R2!2+^[8$m';R8!2+Q!3+6+^Y#@!7'^S!O'^T#\#[#Z#Y#?#>#=#X#W!2'51,K#<#;#:#9#8#7#6#V#U#T#S#R#Q#P#O#N#M#5#4#3#2#L!1'^\#\#K!1,^H2#1!1'^U'<!2+Q!3'_0!3,=9!4,_2+1+1<:!3,=9!4,_2+1+1#I!2'P#I!1,T=!3,=9!4,_2+1+1#H!2'P#H!1'D#C!3,=9!4,_2+1+1>!2'P#J!1,T|510;!3,=9!4,_2+1+1?!2'P#J;!1,@9#A#1!2+Q!3'_3'<#A#1!2+Q!2'U'<#1!2+Q!4'_5'<#1<:!2+Q!4';'<#1#I!3,=+>!1,_6!2'51!2'P#H@!3,=+>!1,_6!2'51!2'_4#G@A!2+Q!4';'<#1#H!3,=+>!2,?#C!3'_87B!3,=7!2'56,K!3'_97!1,_:!2'8+1#D#BA!2+Q!4';'<#1>C!2+Q!4';'<#1?C!4'G'<#1#FB").

Lemma sn_write_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Fp CK D n B bufp : Z) (o : list Z) (dn : nat) (junk : list byte),
  a0 = Z_to_bv 64 Fp -> a2 = Z_to_bv 64 0 ->
  rw_cells rsegs m (Fp + 40) [C8 (Z_to_bv 64 (B + zlength o))] ->
  rw_cells rsegs m (Fp + 56) [C8 (Z_to_bv 64 B)] ->
  rw_cells rsegs m (Fp + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells rsegs m (Fp + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells rsegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
  bytes_at rsegs m B (zb o) ->
  rw_cells rsegs m D [CB dn junk] -> (length o < dn)%nat -> (zlength o <= n < 2^63)%Z -> (0 <= bufp < 2^64)%Z -> (B + zlength o < 2^63)%Z ->
  stk rsegs m (bv_unsigned sp - 64) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z -> mem_inv rsegs m ->

  (B + zlength o <= D \/ D + Z.of_nat dn <= B)%Z ->
  (CK + 16 <= D \/ D + Z.of_nat dn <= CK)%Z ->
  (Fp + 160 <= D \/ D + Z.of_nat dn <= Fp + 40)%Z ->
  (D + Z.of_nat dn <= bv_unsigned sp - 64 \/ bv_unsigned sp <= D)%Z ->
  (bv_unsigned sp <= CK)%Z -> (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
  (CK + 16 <= Fp + 40 \/ Fp + 160 <= CK)%Z ->
  (B + zlength o <= CK \/ CK + 16 <= B)%Z -> (B + zlength o <= Fp + 40 \/ Fp + 160 <= B)%Z ->
  evt rsegs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp CK D n B bufp o dn junk m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb80b8) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros -> -> WPOS WBASE BUF COOKIE CKC SRC DST ROOM Hn Hbufp BHI ST SPLO MI D1 D2 D3 D4 S1 S2 S3 S4 S5 S6.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_bound _ _ _ _ CKC) as CB_. cbn [cells_size csize Nat.add] in CB_.
  pose proof (rw_cells_bound _ _ _ _ COOKIE) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BB. pose proof (zb_length o) as LZ. rewrite LZ in BB. unfold zlength in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (CK, CK + 16); (D, D + Z.of_nat dn); (Fp + 40, Fp + 48); (Fp + 56, Fp + 64)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat ST.
  do 15 zs.
  zs. replace (B + Z.of_nat (length o) - B)%Z with (Z.of_nat (length o)) by lia.
  zs. zs. brf K1; [exfalso; lia|]. zs. zs. zs. brf K2.
  -
    assert (O0 : length o = 0%nat) by lia. destruct o as [|c o']; [|cbn in O0; lia]. cbn [length Z.of_nat] in *.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
    pose proof (u8arr_store_ok rsegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write rsegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { cbn [zlength length Z.of_nat]. rewrite Z.add_0_r, Z.sub_0_r. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
    split. { cbn [zb map app length skipn]. rewrite upd_firstn_skipn in DST by (rewrite LJ; lia). cbn [firstn app] in DST. exact DST. }
    split; [assumption|]. split; [assumption|]. assumption.
  -
    pose proof (rw_CB_length _ _ _ _ DST) as LJ.
    apply (rw_cells_split_CB rsegs _ _ [] dn _ [] [length o; dn - length o]%nat) in DST; [ | cbn; lia ].
    cbn [mk_CB_cells app] in DST.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb]. cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
    zs. zs.
    eapply evt_cut.
    { eapply memcpy_callv with (src := zb o) (junk := firstn (length o) junk);
        [ exact SRC | rewrite LZ; lia | rewrite Nat2Z.id; exact DSTa | lia | lia | lia | lia | exact MI ]. }
    cbv beta. intros ms' P. unfold memcpy_postv in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & DSTa' & SRC').
    lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
    replace (ret_pc (Z_to_bv 64 753940)) with (Z_to_bv 64 753940) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    zs. zs. zs. zs. zs. zs.
    zs. brf K3; [exfalso; lia|]. zs. zs. if_lit.
    pose proof (rw_CB_length _ _ _ _ DSTb) as LJb.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DSTb) as DA. clear DSTb.
    pose proof (u8arr_store_ok rsegs _ _ _ 0%Z (Z_to_bv 64 (D + Z.of_nat (length o))) DA ltac:(rewrite LJb; lia) ltac:(f_equal; lia)) as SOK.
    zs. rewrite le1_zero. replace (Z_to_bv 64 (D + Z.of_nat (length o))) with (wa (D + Z.of_nat (length o) + 0)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write rsegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJb; lia)) as DA2. clear DA. store_done.
    pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DSTb. rewrite upd_length, LJb in DSTb.
    zs. zs. zs. zs.
    do 9 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold sn_write_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; rewrite ?Z.add_0_r; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split. { unfold zlength. match goal with H : rw_cells _ _ CK _ |- _ => exact H end. }
    split.
    { match goal with Ha : rw_cells _ ?mm D [CB _ ?l1], Hb : rw_cells _ ?mm (D + _)%Z [CB _ ?l2] |- _ =>
        assert (J : rw_cells rsegs mm D ([] ++ [CB (length o) l1; CB (dn - length o) l2] ++ []));
        [ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [rewrite Nat2Z.id in Ha; exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact Hb
        | apply rw_cells_merge in J; cbn [cells_size cells_bytes csize cbytes app] in J; rewrite app_nil_r in J ] end.
      replace (length o + (dn - length o + 0))%nat with dn in J by lia.
      rewrite upd_firstn_skipn in J by (rewrite length_firstn, length_skipn, LJ; lia). change (Z.to_nat 0) with 0%nat in J. rewrite firstn_O, app_nil_l in J.
      rewrite skipn_firstn_comm, skipn_skipn in J. replace (1 + length o)%nat with (S (length o)) in J by lia.
      rewrite firstn_all2 in J by (rewrite length_skipn, LJ; lia). exact J. }
    split; [assumption|]. split; [assumption|]. assumption.
Qed.
