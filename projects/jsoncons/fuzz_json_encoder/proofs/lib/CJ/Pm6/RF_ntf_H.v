(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed meta_word_mod32, meta_word_sc52, rmaskw_range and 5 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F F_ntf_H MallocKit_A3 MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @bv]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @rentry_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_A; @rntf_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @mw_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_range]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_word]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freeable]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_sizeclass]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_maplen]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @div_small]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @ZArith; @BinInt; @Z; @div_add]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @lor_sxv_zero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_meta_rec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @eh_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @eh_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @lor_range64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rmid_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @ntf_cond]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @rentry_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSSP_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rmaskw_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rmaskw_zero]; [@Corelib; @Init; @Logic; @iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmeta_slot_bounds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @eh_slot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @unsigned_lit_land]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @RAT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @active]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @bit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mask_upto]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @okay_to_free]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @entry_hyps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_slot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @bounces]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @usage]; [@Corelib; @Init; @Datatypes; @andb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @ntf_cond_unfold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_C; @rconc_meta_inj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_meta_chunk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @oconc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Logic; @I]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_active_read]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_lt4096]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @micromega; @Tauto; @IFF]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rntf_fge]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_stride]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @UNIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @size_class]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @is_bouncing]; [@Corelib; @Init; @Logic; @eq_sym]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@Stdlib; @micromega; @Tauto; @EQ]; [@Stdlib; @micromega; @Tauto; @isBool]; [@Stdlib; @micromega; @Tauto; @FF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_H; @okf_unfold]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @size_class_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSIZE_CLASSES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rsize_classes_read]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@Stdlib; @micromega; @Tauto; @TT]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zx16]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_le2]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @aptr_eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @optr_eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @sc_in_seq_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_ntf_F; @seq_range_test]; [@Corelib; @Init; @Logic; @proj2]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_bounces_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_usage_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rntf_notall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zxb_b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zx16_wz]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @meta_word_sc2]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @meta_word_pg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @land_pgmask]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_maplen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RMLOCK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RNEED_LOCKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RPAGE_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RGOT_SSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @canary_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Corelib; @Init; @Logic; @ex_ind]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_transport_high]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @W_high]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sllw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_sllw]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addw]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @free_all_test]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @ENTRY; @rntf_okchk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @addiw_m1_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @meta_word_mod32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sllw2_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @addw_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_H; @CEIL_WRAP_1; @meta_word_sc52]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_freeable]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_comm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @sllw1_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sx32_wz_sxv]].

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!1,2|600;!1+30$pc;R+0$R;R!2'1!1,2|21;1$ms';R+4!3+5+4#1!7'6#2/F;!2'70#3/fc;!1,81/m1;!1'9':").

Definition rentry_cases (ms' : machine_state) : Prop :=
  (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0xac8ec (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
     RAT 0xac6d0 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = None /\
   exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xac794 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xac728 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
     RAT 0xac6a4 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 23 "S;0!1,2|600;!1+30|500;|30;!1+3!1,23%~R1!1+=4!1+?4!2+D+0+0!2'G0#I|620;!2'M8!1,N9$ra;R1$sp;R1$gp;R1$tp;R1$s0;R1$s1;R1$s2;R1$s3;R1$s4;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$F;R!2'1!1,2|21;1$fc;R!1+3!1,22$st;R+;$g;R'<$i;R+0$lo;R+0$m;R5$ms';R+4!2+>5$m1;R5!2+>6$junk;R6!2+@!E'A#J#I#H#G#F#C#B#A#@#?#>#=#<#;#:#9#8#7#6#2#3!2+@!3'B!3,C7!4,E+0+0!2'F8!1,H98!1,I7#4#2!2+@!3'J':#4#2!2+@!2'K':#2!2+@!4'L':#2#5:!2+@!4'O':#2:!7'P/RUNp;#1#C#D#E#F#J!3'Q/RUNp;#8#2").

(* [comment removed for export] *)
Lemma meta_word_sc52 mr : mw_ok mr ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
  intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
  rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
  intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

(* [comment removed for export] *)
Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
  munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
  /\ stk rsegs m1 lo (bv_unsigned sp + -96) /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

Ltac rpost_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


(* [comment removed for export] *)
Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> ntf_cond st g i = false ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xac6c8) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). pose_ceil. pose_ceil.
  st1. rewrite ?(unsigned_lit (conc st g)) by lia.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
  -
    rpost_common MU WM MI ST FR MR m1 junk.
    left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
    do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  -
    assert (M0 : mask = 0) by (apply MZ; lia).
    rpost_common MU WM MI ST FR MR m1 junk.
    right; left. split; [exact HC|]. split; [exact M0|].
    do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xac680) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  (pose_ceil; unfold RCTX in *).
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
  assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
  { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
    split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
  rmeta_chunk MR MSL CH.

  st1. clear CH.
  destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
  - destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
    specialize (G50 HC ltac:(congruence)).

    st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }

    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
    replace (wa (1022512 + 80 + 8 * sc)) with (Z_to_bv 64 (1022512 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.

    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    + pose proof (NINJ ltac:(lia)) as ->.
      rpost_common MU WM MI ST FR MR m1 junk.
      do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
      do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
    + assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
      rpost_common MU WM MI ST FR MR m1 junk.
      do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
      do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
  - st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
    rpost_common MU WM MI ST FR MR m1 junk.
    do 2 right; left. split; [exact HC|]. split; [exact NX|].
    do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
  rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
  evt rsegs POST
    (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xac5d0) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
  pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
  pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose_ceil.
  assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
  assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).

  st1. st1. st1.
  st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
  {
    eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
    rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  assert (SC48 : sc < 48) by lia. clear K2.
  assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
  specialize (USG SC48).
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  assert (RS' : ov_read_bytes rsegs m1 (Z_to_bv 64 (123112 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (123112 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
    apply rsize_classes_read; [assumption| lia]. }

  st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.

  assert (K690 : forall (t0' : word),
    m_maplen mr <> 0 ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 123112) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 1022512) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac624) fc None m1 (seg_rom rsegs))).
  { intros t0' MLNZ.
    assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
    assert (GSR : 0 < get_stride mr < 2^64).
    { unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }

    st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
    replace (123112 + sc * 2) with (123112 + 2 * sc) by lia.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

    st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    { eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
    assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
    assert (OKF : okay_to_free st g =
              if negb (optr_eqb (m_next mr) (Some g)) then true
              else if negb (is_bouncing sc st) then true
              else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
    { rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }

    rmeta_chunk MR MSL CH.
    st1. clear CH.
    assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
    { intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _). pose_ceil.
      split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
    destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
    2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
        eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
    destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
    st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
    { assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
      cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
    pose proof (NINJ ltac:(lia)) as Enx. subst nx.
    rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.

    st1. rewrite ?(unsigned_lit sc) by lia. st1.
    st1. if_cases K7; zify_cond K7.
    { assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
      unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    assert (SR : sc_in_seq_range sc = true).
    { destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
    assert (SR' : 7 <= sc < 39).
    { unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
    unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.

    st1.
    pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
    pose proof (BND (sc - 7)) as BR.
    replace (Z_to_bv 64 (1022512 + 880 + (sc - 7))) with (Z_to_bv 64 (1022512 + (sc + -7) + 880)) in RDB by (f_equal; lia).
    st1. clear RDB. st1.
    st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
    { replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
    replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.

    st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
    pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
    replace (wa (1022512 + 464 + 8 * sc)) with (Z_to_bv 64 (1022512 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
    st1. clear RDU.
    st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.

    st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
    { replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
    replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.

    st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
    - replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
      assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
      eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
    - replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
      eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }

  assert (K678 :
    (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs POST
      (MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 123112) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 1022512) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac60c) fc None m1 (seg_rom rsegs))).
  { intros COND.
    assert (STR : get_stride mr = 16 * size_class sc).
    { unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).

    st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
    st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.

    st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
    - eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
      rewrite okf_unfold, FRZ, NB48. cbn [orb].
      replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
    - replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
      apply K690. lia. }

  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  { apply K678. left. lia. }

  st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
  { apply K678. right. lia. }

  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
  st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
  replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
  2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
  apply K690. lia.
Qed.

(* [comment removed for export] *)
Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rmrep st m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xac56c) fc None m (seg_rom rsegs)).
Proof.
  intros until t6. intros MR ST.
  pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
  pose proof MW as (LI & FB & SCR & ML).
  pose proof (meta_word_range _ MW) as MWR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _). pose_ceil.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof rmaskw_range as MWR'.
  pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & _) & _).
  (pose_ceil; unfold RGOT_SSP, RSSP_GUARD in *). unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

  st1. carve_frame 96%nat ST. st1. st1. st1. st1. st1.

  st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  clear MR G4 G5.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
  rmeta_chunk MR1 MSL CH.

  st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
  st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
  st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
  st1. rewrite (meta_word_freeable _ MW).
  st1. rewrite (meta_word_sc52 _ MW).
  clear CH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.

  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }

  st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
  rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
  st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
  st1. rewrite addiw_m1_word.

  pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
  st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
  - assert (HC : ntf_cond st g i = false).
    { rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
      apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
    eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
  -
    apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
    eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed.
End ENTRY.
End CEIL_WRAP_1.

