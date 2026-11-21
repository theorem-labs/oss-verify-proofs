(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed land_m4096, lor_shl5, renframe_fold_walk and 4 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_malloc_free_u5 F_malloc_fast_u5 F_malloc_enframe_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import RMallocRep_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Numbers; @BinNums; @Z]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @F_syscalls_u5; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_1; @renframe_tail_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @eq_sym]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_pow2_bits_low]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_0]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_above_log2]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_le_trans]; [@Stdlib; @ZArith; @BinInt; @Z; @log2]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @log2_lt_pow2]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @add_nocarry_lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor_lor]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @ren3_post]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @wz]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@Corelib; @Init; @Datatypes; @prod]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@Corelib; @Init; @Datatypes; @pair]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_store_ok]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_same]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le2]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_2']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le2]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_read]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @renframe_tail_mem]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @le1_wz]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @zxb_b8]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @signed_wz_small]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @lor_shl5]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SysStep; @swrap32_small]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @renframe_off_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @renframe_tail_walk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_free_u5; @wr_at_sub]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slliw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_slliw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @le1_neg32]; [@Stdlib; @ZArith; @Zdiv; @Z_mod_plus_full]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @fold_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @fold_off_le_slack]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @smear]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @fold_off_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @renframe_off_walk]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_shiftr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @Z_shiftr_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @Z_lor_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @land_le_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltu]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @fold_assert_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addw]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @swrap32_add_2p64]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltu_b2z]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_comm]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_low]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec_high]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @size_class]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_enframe_u5; @mword_sc]; [@Stdlib; @micromega; @Tauto; @EQ]; [@Stdlib; @micromega; @Tauto; @isBool]; [@Stdlib; @micromega; @Tauto; @FF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @land_m4096]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_free_u5; @sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @mod_mod_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_free_u5; @sxv_mod32]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @Gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @size_class_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_free_u5; @sxv_range]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @F_malloc_free_u5; @frozen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RF_enframe_u5; @CEIL_WRAP_2; @renframe_fold_walk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zx16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_le2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Agent; @MallocRep_u5; @zx16_wz]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RMallocRep_u5; @rsize_classes_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @Pm6; @RMallocRep_u5; @RSIZE_CLASSES]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]].

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.



(* [comment removed for export] *)
Definition renframe_tail_mem (m : word -> option byte) (P E n k q : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P - 3)) [b8 k] in
  let m2 := write_to_mem m1 (wa (P - 2)) (le2 (wz q)) in
  let r := E - P - n in
  let m3 := if r =? 0 then m2 else write_to_mem m2 (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition ren3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pw : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (P E n k q : Z) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 25 "S40!1+0!1,1|600;|500;|30;%~R0!1+3!1+0!1,12$ra;R0$sp;R0$gp;R0$tp;R0$s0;R0$s1;R0$s2;R0$s3;R0$s4;R0$s5;R0$s6;R0$s7;R0$s8;R0$s9;R0$s10;R0$s11;R0$pw;R0$F;R!2'2!1,1|21;0$fc;R!1+0!1,11$m;R3$P;R+4$E;R+4$n;R+4$k;R+4$q;R+4$ms';R+5!2+60$t0;R0!2+60$t1;R0!2+60$t2;R0!2+60$a1;R0!2+60$a2;R0!2+60$a3;R0!2+60$a4;R0!2+60$a5;R0!2+60$a6;R0!2+60$a7;R0!2+60$t3;R0!2+60$t4;R0!2+60$t5;R0!2+60$t6;R0!2+63$m';R3!2+7!3+8+5#@!7'9!O':#Y#X#W#V#?#>#=#U#T#I#<#;#:#9#8#7#6#S#R#Q#P#O#N#M#L#K#J#5#4#3#2#H!1';#Y#G!1,<0#1!1'='>!2+7!3+83#1!6'?#F#E#D#C#B#A!2'@'>#1").

Lemma lor_shl5 r k : 0 <= k < 32 -> 0 <= r -> Z.lor (r * 2 ^ 5) k = Z.land k 31 + Z.shiftl r 5.
Proof.
  intros Hk Hr. replace (Z.land k 31) with k by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (D : Z.land (r * 2 ^ 5) k = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 5).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit k i) with false; [apply andb_false_r|]. symmetry.
      destruct (Z.eq_dec k 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- (Z.add_nocarry_lxor _ _ D). lia.
Qed.
End CEIL_WRAP_1.


Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
(* [comment removed for export] *)
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma renframe_tail_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw : word) F fc m
    (P0 P E B n k stride : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> E = P0 + stride - 4 ->
  mem_inv rsegs m ->
  wr_at rsegs m (P - 3) (E - P + 3) ->
  E + 1 <= 2^64 -> B + 16 <= P -> P0 <= P -> P + n <= E -> E - P - n < 2^31 -> P - B < 2^31 -> 16 <= P0 -> 0 <= B -> 0 <= n -> 0 <= k < 32 ->
  0 <= stride ->
  evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) F fc m P E n k ((P - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (Z_to_bv 64 P) (Z_to_bv 64 stride) p0w (wz B) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb1258) fc None m (seg_rom rsegs)).
Proof.
  intros until stride. intros HP0 HN HE MI WR ETOP BP P0P PNE EP PB P16 B0 N0 HK S0.
  pose proof (bv_unsigned_in_range _ p0w) as PWR. change (bv_modulus 64) with (2^64) in PWR.
  set (r := E - P - n).
  assert (K31 : Z.land k 31 = k) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).

  step.

  step. rewrite (unsigned_lit P), (wz_unsigned B), (swrap32_small (P - B)) by lia.

  step. rewrite HN.

  step. rewrite HP0. replace (P0 + stride + -4) with E by lia.

  step. step. rewrite (unsigned_lit (P - B + -16)), Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16. replace (P - B + -16) with (P - B - 16) by lia.

  step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.

  sok 0 1%nat (P + -3).
  step. rewrite (le1_wz k) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 k] |- _ =>
    pose proof (bytes_at_write_same rsegs mp a [b8 k] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P - 3) in BK by lia end.

  sok 1 2%nat (P + -2).
  step. change (le2 (Z_to_bv 64 ((P - B - 16) / 16))) with (le2 (wz ((P - B - 16) / 16))). sdk.

  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step.

    read_k. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned k), ?K31 by lia. step. step. rewrite ?(unsigned_lit 0), ?(unsigned_lit k) by lia.
    rewrite Z.lor_0_l.
    sok 0 1%nat (P + -3).
    step. change (le1 (Z_to_bv 64 k)) with (le1 (wz k)). rewrite (le1_wz k) by lia. sdk.
    step. step.
    apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
    split; [|assumption].
    unfold renframe_tail_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    rewrite K31. change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r.
    repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  -
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    +
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. rewrite (unsigned_lit r), Z.shiftl_mul_pow2 by lia.
      step. rewrite (unsigned_lit (r * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 r k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (P0 + stride + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (P0 + stride + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      read_k. step. clear RK. rewrite ?zxb_b8 by lia.
      step. rewrite ?(wz_unsigned k), ?K31 by lia.
      step. step. rewrite ?(unsigned_lit 5), (unsigned_lit k) by lia. change (5 ≪ 5) with (5 * 2 ^ 5). rewrite (lor_shl5 5 k) by lia.
      sok 0 1%nat (P + -3).
      step. rewrite (le1_wz (Z.land k 31 + Z.shiftl 5 5)) by (rewrite K31; change (Z.shiftl 5 5) with 160; lia). sdk.
      step. step.
      apply evt_done. unfold ren3_post. do 15 eexists. split; [reflexivity|].
      split; [|assumption].
      unfold renframe_tail_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
Definition renframe_off_mem (m : word -> option byte) (P0 off : Z) : word -> option byte :=
  if off =? 0 then m
  else write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off)))
                    (wa (P0 + 16 * off - 4)) [b8 0].

(* [comment removed for export] *)
Lemma renframe_off_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off avail freed mword : Z),
  bv_unsigned p0w = P0 -> bv_unsigned nw = n ->
  mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at rsegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 -> P0 + 16 * off - B < 2^31 -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off -> 16 * off <= stride - 4 - n ->
  evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb1234) fc None m (seg_rom rsegs)).
Proof.
  intros until mword. intros HP HN MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OFF0 OFFS.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.

  step. step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit off) in KO by lia.
  -
    subst off. unfold renframe_off_mem. rewrite Z.eqb_refl.
    replace (P0 + 16 * 0) with P0 by lia.
    replace p0w with (Z_to_bv 64 P0) by (rewrite <- HP; apply Z_to_bv_bv_unsigned).
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
    + apply unsigned_lit. lia.
    + eapply wr_at_sub; [exact WR | lia | lia].
  -
    step.
    step. rewrite (unsigned_lit off), Z.shiftl_mul_pow2, (swrap32_small (off * 2 ^ 4)) by lia.
    step. rewrite HP.
    pose proof (wr_at_store_ok rsegs m _ _ 1 1 WR ltac:(lia) ltac:(lia)) as SO1.
    replace (P0 - 4 + 1) with (bv_unsigned p0w + -3) in SO1 by lia.
    change (wa (bv_unsigned p0w + -3)) with (Z_to_bv 64 (bv_unsigned p0w + -3)) in SO1.
    step. rewrite le1_neg32. sdk.
    lazymatch goal with W : wr_at rsegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok rsegs mc _ _ 2 2 W ltac:(lia) ltac:(lia)) as SO2;
      replace (P0 - 4 + 2) with (bv_unsigned p0w + -2) in SO2 by lia;
      change (wa (bv_unsigned p0w + -2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in SO2 end.
    step. change (le2 (Z_to_bv 64 off)) with (le2 (wz off)). sdk.
    lazymatch goal with W : wr_at rsegs ?mc (P0 - 4) _ |- _ =>
      pose proof (wr_at_store_ok rsegs mc _ _ (16 * off) 1 W ltac:(lia) ltac:(lia)) as SO3;
      replace (P0 - 4 + 16 * off) with (P0 + off * 2 ^ 4 + -4) in SO3 by lia;
      change (wa (P0 + off * 2 ^ 4 + -4)) with (Z_to_bv 64 (P0 + off * 2 ^ 4 + -4)) in SO3 end.
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    step.
    replace (P0 + off * 2 ^ 4) with (P0 + 16 * off) by lia.
    unfold renframe_off_mem. replace (off =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      replace (write_to_mem (write_to_mem (write_to_mem m (wa (P0 - 3)) [b8 224]) (wa (P0 - 2)) (le2 (wz off))) (wa (P0 + 16 * off - 4)) [b8 0])
        with mc end.
    2:{ repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
        repeat (f_equal; try (unfold wa; f_equal; lia)). }
    eapply renframe_tail_walk with (P0 := P0) (E := P0 + stride - 4); try eassumption; try lia.
    eapply wr_at_sub; [exact WR | lia | lia].
Qed.

Lemma swrap32_add_2p64 d : -2^31 <= d < 2^31 -> bv_swrap 32 (18446744073709551616 + d) = d.
Proof.
  intros Hd. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  replace (18446744073709551616 + d + 2147483648) with ((d + 2147483648) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma renframe_fold_walk : forall (ra sp gp tp t2 s0 s1 gw a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0w nw prev next : word) F fc m
    (P0 B stride n k off0 avail freed mword T0 : Z),
  let slack := (stride - 4 - n) / 16 in
  let off := fold_off off0 slack in
  bv_unsigned p0w = P0 -> bv_unsigned nw = n -> T0 = stride - 4 - n ->
  mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at rsegs m (P0 - 4) stride ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  B + 16 <= P0 -> 0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 16 <= P0 -> 0 <= k < 32 ->
  0 <= off0 < 256 ->
  evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp (Z_to_bv 64 T0) (Z_to_bv 64 slack) t2 s0 s1
               gw (wz k) nw a3 (Z_to_bv 64 stride) p0w (wz B) (Z_to_bv 64 off0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb11f8) fc None m (seg_rom rsegs)).
Proof.
  intros until T0. intros slack off HP HN HT0 MI MM WR PTOP SEPG BP B0 N0 NS SS PBS P16 HK OF.
  assert (SL : 0 <= slack <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  pose proof (fold_off_le_slack off0 slack OF ltac:(lia)) as FO. fold off in FO.
  assert (S16 : 16 * slack <= stride - 4 - n) by (subst slack; Z.div_mod_to_equations; lia).

  step. if_cases K1; zify_cond K1; rewrite ?(unsigned_lit slack), ?(unsigned_lit off0) in K1 by lia.
  -
    assert (EO : off = off0) by (subst off; rewrite fold_off_eq; replace (slack <? off0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
  -
    step. rewrite (unsigned_lit T0), HT0 by lia.
    replace ((stride - 4 - n) ≫ 5) with (slack ≫ 1) by (subst slack; rewrite <- (Z.shiftr_div_pow2 _ 4), Z.shiftr_shiftr by lia; reflexivity).
    pose proof (Z_shiftr_range slack 1 ltac:(lia) ltac:(lia)) as R1.

    step. rewrite (unsigned_lit (slack ≫ 1)), (unsigned_lit slack) by lia.
    set (m1 := Z.lor slack (slack ≫ 1)).
    pose proof (Z_lor_range slack (slack ≫ 1) ltac:(lia) R1) as RM1. fold m1 in RM1.

    step. rewrite (unsigned_lit m1) by lia. pose proof (Z_shiftr_range m1 2 RM1 ltac:(lia)) as R2.
    step. rewrite (unsigned_lit m1), (unsigned_lit (m1 ≫ 2)) by lia. rewrite (Z.lor_comm (m1 ≫ 2) m1).
    set (m2 := Z.lor m1 (m1 ≫ 2)). pose proof (Z_lor_range m1 (m1 ≫ 2) RM1 R2) as RM2. fold m2 in RM2.

    step. rewrite (unsigned_lit m2) by lia. pose proof (Z_shiftr_range m2 4 RM2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit m2), (unsigned_lit (m2 ≫ 4)) by lia. rewrite (Z.lor_comm (m2 ≫ 4) m2).
    set (m3 := Z.lor m2 (m2 ≫ 4)). pose proof (Z_lor_range m2 (m2 ≫ 4) RM2 R3) as RM3. fold m3 in RM3.
    assert (SM : m3 = smear slack) by reflexivity.

    step. rewrite (unsigned_lit off0), (unsigned_lit m3) by lia.
    set (x := Z.land off0 m3).
    assert (RX : 0 <= x <= off0) by (subst x; split; [apply Z.land_nonneg; lia | apply land_le_l; lia]).

    step. rewrite v_sltu_b2z, (unsigned_lit slack), (unsigned_lit x) by lia.

    step. rewrite (unsigned_lit slack) by lia.
    destruct (Z.ltb_spec slack x) as [LT|GE]; cbn [Z.b2z].
    + pose proof (fold_assert_ok off0 slack OF ltac:(lia) ltac:(rewrite <- SM; exact LT)) as FA. rewrite <- SM in FA. fold x in FA.
      step. step. rewrite (zb_lxor_ones slack) by lia. rewrite (unsigned_lit (18446744073709551615 - slack)) by lia.
      change 18446744073709551615 with (Z.ones 64) at 1. rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by lia.
      rewrite (Z.mod_small (18446744073709551615 - slack)) by lia.
      step. rewrite (unsigned_lit (18446744073709551615 - slack)), (unsigned_lit x) by lia.
      replace (18446744073709551615 - slack + x) with (18446744073709551616 + (x - (slack + 1))) by lia.
      rewrite swrap32_add_2p64 by lia.

      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit (x - (slack + 1))) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x - (slack + 1)).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
    + step. step. change (Z.land 0 _) with 0.
      step. rewrite (unsigned_lit x), Z.add_0_l, (swrap32_small x) by lia.
      step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit slack), ?(unsigned_lit x) in K2 by lia; [|exfalso; lia].
      assert (EO : off = x).
      { subst off. rewrite fold_off_eq. replace (slack <? off0) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta.
        rewrite <- SM. fold x. replace (slack <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EO. eapply renframe_off_walk; try eassumption; try lia; try (apply PBS; lia).
Qed.

Lemma land_m4096 a : 0 <= a < 2^64 -> Z.land a 18446744073709547520 = a - a mod 4096.
Proof.
  intros Ha.
  replace (a - a mod 4096) with (Z.shiftl (Z.shiftr a 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
  change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones by lia.
  destruct (Z.lt_ge_cases i 12).
  - rewrite Z.shiftl_spec_low by lia. replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb]. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia).
    replace (i <? 12) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.lt_ge_cases i 64).
    + replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn. rewrite andb_true_r. reflexivity.
    + replace (Z.testbit a i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia|lia].
Qed.

(* [comment removed for export] *)
Lemma renframe_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw nw prev next : word) F fc m
    (B stride n k ctr avail freed last_idx freeable sc maplen vb3 v16 : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let P0 := B + 16 + stride * k in
  let slack := (stride - 4 - n) / 16 in
  let off0 := (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255) in
  let off := fold_off off0 slack in
  bv_unsigned nw = n ->
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
  ((last_idx =? 0) && negb (maplen =? 0) = false -> sc < 48) ->
  mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned gw) [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  wr_at rsegs m (P0 - 4) stride ->
  ov_read_bytes rsegs m (wa (P0 - 3)) 1 = Some [b8 vb3] ->
  ov_read_bytes rsegs m (wa (P0 - 2)) 2 = Some (le2 (wz v16)) ->
  ov_read_bytes rsegs m (wa (P0 - 4)) 1 = Some [b8 0] ->
  P0 + stride <= 2^64 -> (P0 + stride <= bv_unsigned gw \/ bv_unsigned gw + 40 <= P0 - 4) ->
  0 <= B -> 0 <= n -> n + 4 <= stride -> stride - 4 - n < 2^31 ->
  (forall off', 0 <= off' -> 16 * off' + n + 4 <= stride -> P0 + 16 * off' - B < 2^31) -> 0 <= k < 32 ->
  0 <= ctr < 2^32 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  0 <= vb3 < 256 -> 0 <= v16 < 65536 ->
  evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb117c) fc None m (seg_rom rsegs)).
Proof.
  intros until v16. intros mword P0 slack off0 off HN HS SC48 MI MM WR R3 R2 R4 PTOP SEPG B0 N0 NS SS PBS HK CT LI FB SC ML VB V16.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (MW5 : Z.land (Z.shiftr mword 5) 126 = 2 * sc) by (subst mword; apply mword_sc; lia).
  assert (MW12 : Z.land mword 18446744073709547520 = 4096 * maplen).
  { rewrite land_m4096 by lia. subst mword. Z.div_mod_to_equations. lia. }
  assert (MZ : Z.shiftr mword 12 = maplen).
  { rewrite Z.shiftr_div_pow2 by lia. subst mword. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  assert (L255 : Z.land (sxv ctr) 255 = Z.land ctr 255).
  { change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
    rewrite <- (mod_mod_pow2 (sxv ctr) 8 32), sxv_mod32, (mod_mod_pow2 ctr 8 32) by lia. reflexivity. }
  assert (OF0 : 0 <= off0 < 256).
  { subst off0. destruct (vb3 =? 0); (split; [apply Z.land_nonneg; lia|]);
      change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia. }
  assert (SK0 : 0 <= stride * k) by (apply Z.mul_nonneg_nonneg; lia).
  assert (ST16 : 16 <= stride /\ B + 16 <= P0).
  { split; [| subst P0; lia]. rewrite HS. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
    - apply andb_prop in E. destruct E as [_ E2]. destruct (Z.eqb_spec maplen 0); [discriminate|]. lia.
    - pose proof (size_class_range sc ltac:(specialize (SC48 eq_refl); lia)). lia. }
  destruct ST16 as [ST16 BP0].

  step. step. rewrite (wz_unsigned mword), MZ by lia.

  assert (JOIN : forall a5',
    evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (Z_to_bv 64 stride) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb11bc) fc None m (seg_rom rsegs))).
  { intros a5'.
    pose proof (sxv_range ctr) as RC.
    assert (Eoff0 : off0 = (if vb3 =? 0 then Z.land ctr 255 else Z.land (v16 + 1) 255)) by reflexivity.
    assert (EP0 : P0 = B + 16 + stride * k) by reflexivity.
    assert (Eoff : off = fold_off off0 slack) by reflexivity.
    assert (Esl : slack = (stride - 4 - n) / 16) by reflexivity.
    clearbody off slack off0 P0 mword. clear MW1 MW5 MW12 MZ HS SC48.

    step. step. step. rewrite ?(wz_unsigned k), ?(wz_unsigned B), ?(unsigned_lit stride) by lia.

    replace (wa (P0 - 3)) with (Z_to_bv 64 (B + stride * k + 13)) in R3 by (unfold wa; f_equal; lia).
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    step. rewrite ?zxb_b8 by lia. clear R3.

    step. rewrite HN. step. step. replace (B + stride * k + 16) with P0 by lia.
    set (p0w := Z_to_bv 64 P0). assert (HP0 : bv_unsigned p0w = P0) by (subst p0w; apply unsigned_lit; lia). clearbody p0w.
    replace (wa (P0 - 2)) with (Z_to_bv 64 (bv_unsigned p0w + -2)) in R2 by (unfold wa; f_equal; lia).
    replace (wa (P0 - 4)) with (Z_to_bv 64 (bv_unsigned p0w + -4)) in R4 by (unfold wa; f_equal; lia).

    step. if_cases KB; zify_cond KB; rewrite ?(wz_unsigned vb3), ?(unsigned_lit vb3) in KB by lia.
    -
      clear R2. unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(wz_unsigned (sxv ctr)), ?L255 by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land ctr 255) with off0 by (rewrite Eoff0, KB; reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS].
    -
      unfold frozen in R2.
      step. rewrite ?zx16_wz by lia. clear R2. step. rewrite (wz_unsigned v16) by lia.
      unfold frozen in R4. step. rewrite ?zxb_b8 by lia. clear R4.
      step. rewrite (unsigned_lit (stride + - n + -4)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      replace ((stride + - n + -4) / 16) with ((stride - 4 - n) / 16) by (f_equal; lia).
      step. rewrite ?(unsigned_lit (v16 + 1)) by lia.
      step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?(wz_unsigned 0), ?(unsigned_lit 0) in K4 by lia. lia. }
      replace (Z.land (v16 + 1) 255) with off0 by (rewrite Eoff0; replace (vb3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Eoff, Esl. eapply renframe_fold_walk.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [_; _; _; _; _; _] => exact MM
           | |- mem_inv _ _ => exact MI
           | |- wr_at _ _ _ _ => exact WR
           | |- _ => idtac end.
      all: first [lia | exact PBS]. }

  assert (JOIN2 : forall a5', stride = 16 * size_class sc -> sc < 48 ->
    evt rsegs (ren3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (P0 + 16 * off)) F fc
               (renframe_off_mem m P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1
               gw (wz k) nw (wz (sxv ctr)) (wz mword) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb11a0) fc None m (seg_rom rsegs))).
  { intros a5' HS16 SC'.
    lazymatch type of R2 with ?T => change T with (frozen T) in R2 end.
    lazymatch type of R3 with ?T => change T with (frozen T) in R3 end.
    lazymatch type of R4 with ?T => change T with (frozen T) in R4 end.
    pose proof (Z_shiftr_range mword 5 MWR ltac:(lia)) as R5.
    pose proof (size_class_range sc ltac:(lia)) as SZ.

    step. rewrite (wz_unsigned mword) by lia. step. step. rewrite (unsigned_lit (mword ≫ 5)), MW5 by lia.
    step. step. rewrite ?(unsigned_lit (2 * sc)) by lia.
    pose proof (rsize_classes_read m sc MI ltac:(lia)) as RS. unfold RSIZE_CLASSES in RS.

    step. rewrite ?zx16_wz by lia.
    step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia.
    replace (size_class sc * 2 ^ 4) with stride by lia.
    apply JOIN. }

  step. if_cases KM; zify_cond KM; rewrite ?(unsigned_lit maplen) in KM by lia.
  -
    apply JOIN2; [| apply SC48]; rewrite ?HS; replace (maplen =? 0) with true by (symmetry; apply Z.eqb_eq; lia); rewrite ?andb_false_r; cbn [negb andb]; try reflexivity.
    all: destruct (last_idx =? 0); reflexivity.
  -
    step. rewrite (wz_unsigned mword), MW1 by lia.
    step. if_cases KL; zify_cond KL; rewrite ?(unsigned_lit last_idx) in KL by lia.
    +
      apply JOIN2; [| apply SC48]; rewrite ?HS; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity.
    +
      step. step. rewrite (wz_unsigned mword) by lia. rewrite MW12.
      step. replace (4096 * maplen + -16) with stride.
      2:{ rewrite HS. replace (last_idx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
          replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia. }
      step. apply JOIN.
Qed.
End CEIL_WRAP_2.

