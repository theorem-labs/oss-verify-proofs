(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed act_mask_le4, land_mod_pow2, rntf_deq and 2 more. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_C F_ntf_E MallocKit_A3.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_slot]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_meta_rec]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_E; @CEIL_WRAP_1; @rat9c_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocModel_B; @deq_mid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @LActive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @conc]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_length]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Logic; @eq_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@Corelib; @Init; @Datatypes; @true]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_head_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @actives]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @usages]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @unmap_seqs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @bouncess]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_tail_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr_store_ok]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @actives_length]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_set_active]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_active]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @PER_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Corelib; @Classes; @Morphisms; @trans_co_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @upd_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_set_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_set_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @optr_eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocTree; @rpres_except]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rpres_except_of_munch_cov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp_stack]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp_ctx]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @ivs_covered]; [@Corelib; @Init; @Logic; @not]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @active]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmeta_slot_bounds]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_meta_chunk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @oconc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_word]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_put_meta_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_congr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @meta_slot_put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @meta_cells_put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @conc_put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @get_meta_rec_put_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_active_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @upd_meta_put]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @aptr_eqb_neq]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp_meta]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_C; @rconc_meta_inj]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @le4_congr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @land_range64]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @land_upper]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @mod64_mod32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_mod32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_E; @CEIL_WRAP_1; @land_mod_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocModel_B; @clr_links]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ghdr]; [@stdpp; @base; @lookup]; [@stdpp; @gmap; @gmap]; [@stdpp; @decidable; @prod_eq_dec]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @numbers; @N; @eq_dec]; [@stdpp; @numbers; @Z; @eq_dec]; [@stdpp; @countable; @prod_countable]; [@stdpp; @countable; @N_countable]; [@stdpp; @countable; @Z_countable]; [@stdpp; @gmap; @gmap_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @g_active_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_E; @CEIL_WRAP_1; @rat00_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocModel_B; @pd_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocModel_B; @act_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocModel_B; @act_of]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @munch_grow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @ivl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_group_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @g_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sllw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_sllw]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_subw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_subw]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @amo_aligned_intro]; [@Stdlib; @micromega; @Tauto; @NOT]; [@LinuxProcessSemantics; @Riscv; @Sem; @amo_aligned]; [@LinuxProcessSemantics; @Riscv; @Instr; @AW]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lr]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@LinuxProcessSemantics; @Riscv; @Sem; @eff]; [@Corelib; @Numbers; @BinNums; @positive]; [@LinuxProcessSemantics; @Riscv; @Sem; @EFault]; [@LinuxProcessSemantics; @Riscv; @Sem; @ELoad]; [@LinuxProcessSemantics; @Riscv; @Sem; @is_x0]; [@LinuxProcessSemantics; @Riscv; @Sem; @EDone]; [@Corelib; @Init; @Logic; @proj2]; [@LinuxProcessSemantics; @Riscv; @Instr; @Sc]; [@LinuxProcessSemantics; @Riscv; @Sem; @EStore]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mask_upto]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @group_active_idx]; [@stdpp; @option; @from_option]; [@Corelib; @Init; @Datatypes; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @land_neg_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @ldiff_le]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_set_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_set_freed]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @le4_sxv]; [@Stdlib; @micromega; @Tauto; @IFF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_ntf_E; @CEIL_WRAP_1; @act_mask_le4]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @swrap32_mod32]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @sextw_sxv0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sx32_wz_sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_fast; @sxv_land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @negw_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sllw2_word]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists a3 a4 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xac730) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_deqself : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g : aptr) (sc lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some g ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac728) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  st1.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (1022512 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (1022512 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.

(* [comment removed for export] *)
Lemma rntf_deq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) st (g nx pv : aptr) (sc lo : Z),
  rmrep st m -> mem_inv rsegs m -> meta_slot st g -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
  (active st sc = None \/ exists q, active st sc = Some q /\ meta_slot st q) ->
  a2 = pw st (active st sc) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat9c_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
               (deq_mid (LActive sc) g st) g sc fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac6a4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose_ceil.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose_ceil. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB. pose_ceil.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (1022512, 1022512 + 928)]%Z m) as MU.

  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.

  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.

  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (1022512 + 80 + 8 * sc)) with (Z_to_bv 64 (1022512 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }

  st1. if_cases K; zify_cond K.
  -
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  -
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. pose_ceil. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    pose proof MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (Z_to_bv 64 (1022512 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (1022512 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. do 3 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.

(* [comment removed for export] *)
Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.

Lemma act_mask_le4 f y z : 0 <= f < 2^32 -> 1 <= y <= 2^32 -> z mod 2^32 = (y - 1) mod 2^32 ->
  le4 (Z_to_bv 64 (Z.land (sxv f) (bv_unsigned (Z_to_bv 64 z)))) = le4 (wz (Z.land f (y - 1))).
Proof.
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xac794) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells rsegs m' (bv_unsigned sp + -96) fr
    /\ rmrep st' m'.

(* [comment removed for export] *)
Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv rsegs m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac730) fc None m (seg_rom rsegs)).
Proof.
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB. pose_ceil.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  (pose_ceil; unfold RCTX in *).
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.

  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono rsegs m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).

  st1. if_cases K; zify_cond K.
  -
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  -
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].

    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (1022512 + 80 + 8 * sc)) with (Z_to_bv 64 (1022512 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.

    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + destruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. pose_ceil. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.

      st1.

      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }

      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.

      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.

      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

      st1. st1. st1.

      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    +
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. do 9 eexists. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
End CEIL_WRAP_1.

