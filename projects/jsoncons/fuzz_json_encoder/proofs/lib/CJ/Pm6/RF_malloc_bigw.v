(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv): changed le4_swrap_succ, le4_sxv_succ, lor_land_2048_4064 and 6 more. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import Malloc_fp F_malloc_bigw.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMalloc_fp RF_enframe RMallocKit_A2.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zeros]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mrd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @Lists; @List; @nth_error]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Lists; @ListDef; @repeat]; [@Stdlib; @Lists; @List; @repeat_length]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @AND]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@Stdlib; @Lists; @List; @nth_error_repeat]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Corelib; @Init; @Datatypes; @negb]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff_spec]; [@Stdlib; @Bool; @Bool; @orb_true_r]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @Bool; @Bool; @orb_false_r]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_spec]; [@Corelib; @Numbers; @BinNums; @N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @big_meta]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_pow2_bits_low]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_comm]; [@Corelib; @Init; @Logic; @eq_sym]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_above_log2]; [@Stdlib; @PArith; @BinPos; @Pos; @succ]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Numbers; @BinNums; @positive]; [@Stdlib; @ZArith; @BinInt; @Pos2Z; @inj_succ]; [@Stdlib; @ZArith; @BinInt; @Z; @log2]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_0]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @add_nocarry_lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor_lor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @big_ml]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @big_ml_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mkMeta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freeable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_sizeclass]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_maplen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_enframe; @land_m4096]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_malloc_bigw; @CEIL_WRAP_1; @lor_land_2048_4064]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @le4_congr]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @u32]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_mod]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_mod32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @mod_mod_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_range]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocTree; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RMLOCK]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Logic; @False_ind]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmunmap_entry]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_get_meta; @runlock_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_get_meta; @runlock_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Program; @Basics; @flip]; [@Corelib; @Program; @Basics; @impl]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @flip_Reflexive]; [@Corelib; @Classes; @RelationClasses; @impl_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mstate]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @ralloc_meta_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_seq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_malloc_bigw; @CEIL_WRAP_1; @rseq_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @step_seq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_head_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @actives]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @usages]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @unmap_seqs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @bouncess]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_tail_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RNEED_LOCKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RPAGE_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RGOT_SSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSSP_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @canary_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @brk_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @upd_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_seq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B3; @rmrep_set_seq]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @le1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@Corelib; @Init; @Logic; @ex_intro]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_unmap_seq_map]; [@stdpp; @base; @empty]; [@stdpp; @gmap; @gmap]; [@stdpp; @numbers; @Z; @eq_dec]; [@stdpp; @countable; @Z_countable]; [@stdpp; @gmap; @gmap_empty]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @step_seq_eq]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @rw_cells_of_u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @unmap_seqs_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr_of_rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_congr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_ctx_frameW]; [@stdpp; @numbers; @N; @eq_dec]; [@stdpp; @countable; @N_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @region]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_regions]; [@stdpp; @decidable; @prod_eq_dec]; [@stdpp; @countable; @prod_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_metas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @area]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ghdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_reserved]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @unmap_seqs_empty]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @brkstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_brk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zxb_b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mkRegion]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @RKGroup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @big_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ticks_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @ref_reserved]; [@stdpp; @base; @lookup]; [@stdpp; @gmap; @gmap_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @round_up_pg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ranges_free]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @lr_lo]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @rkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMalloc_fp; @rmeta_chunk_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_meta_rec]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @round_up_pg_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMalloc_fp; @rreserved_disjoint2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cellval]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cell_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @Known]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_of_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_malloc_bigw; @CEIL_WRAP_1; @rzeros_bytes_at]; [@stdpp; @option; @from_option]; [@Corelib; @Init; @Datatypes; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @shadow0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_A2; @cell_read_shadow0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @wr_at_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_mmap_counter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_secret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_init_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_free_meta_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_count]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_area_count]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_alloc_shift]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_area_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_area_tail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_prefix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @big_metaA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_put_meta_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_hdr_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @hdr_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_transport_unowned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rrepfoot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rarea_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rarea_lr_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rgroup_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @lr_lo_group]; [@Stdlib; @NArith; @BinNat; @N; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @cell_read_hdr_havoc_fresh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @Unknown]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @ivs_avoid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_A2; @rmrep_put_group_new]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @put_group]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@Stdlib; @ZArith; @BinInt; @Z; @land_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_enframe; @land_le_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_bigw; @meta_word_big_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_A2; @rmrep_set_mmap_counter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_mmap_counter]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @PER_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @Morphisms; @trans_co_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_malloc_bigw; @CEIL_WRAP_1; @le4_swrap_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sx32_wz_sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_malloc_bigw; @CEIL_WRAP_1; @rbig_word_eq]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
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


Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at rsegs m (x + o) [b8 0]) -> bytes_at rsegs m x (zeros k).
Proof.
  intros m x k X0 XK H. split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed.

(* [comment removed for export] *)
Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed.

Lemma rbig_word_eq rid n : 0 <= n < 2^48 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 2 "S_Y0!2'5,6#1|10;!1,:1|510;!1,:3!2'924!2+;0!2'<#15!1,:|;7e0;!1,:|513;!2'7!2'7#278!2'^N9!1,:|^B7ffffffffffff000;!1'_8!2'_9#4#3!1,:|<000;!2'_:9!2'_;9<!1,:|<013;!2'7#2>!2'7!2'7#378|500;!1,:A!1,:,\|600;!1,:D|51f;!1,:F!2'7!2'7,6!2'_=BC!2'_=EG!2'K24!2'<,62%~RJ%~R!2'5,64!2'<,65!2'5,62$Ha;RL$~R+L!3'M24#2%Ha;RL%~R+L!2'5,65!1,A+N!1+O+N!2,P+3#2!1+Q+3!1+S+3!2,[+3,\!2,Y+3>!3,^<+3TU!2,Y+37!3,^<+3!3,^<+3TW!2,Y+38!2'^2S,V!4'^3#1#3vv!2,^4+^5,^6!3+F+^5!2'^7#1#3,^6!3'^8+3,6#2!2'7#3>!2'7#4>!2'^N!2'_:[!2'_;[<7!2'7#5>!2'_;^1<!2'_:^1^2!2'7#6>!2'_;^4<!2'_:^4^5!3+F+3<,6!1'_@^7!2'_=<!2'_<^4<!2'<,6<!2'7#7>!2'_;^;<!2'<<,6!2'7#8>!2'_;^><!2'7#9>!2'_<^@<!2'7#:>!2'_;^B<!2'_<^B<!2'7#;>!3,?+N!2,_E!3,_F+3!3,_G+3!2,_H+3!1,_I,\!2,_J+3}1!2,_J+3,^H,_KO!4,^:+3!2,P+3#3#2!2,P+3#4!2,Y+3<!2,Y+3,6!6,_LS'T+U+U,V!7,WS'T+U+U,V!4,X+3^H,_>^I,^0!1,^1+U!2,[+31!3,^<+3^LU!3,_M+3^HT|11;!2,[+3^O%~R^7+_O!2'_=<#2!2'_=<!2'_<^1<|34;!1,:^T!2'<#4^U!2'5^U#4!2'^P7#7!2'92^U!2'_<^@^Y!2,Y+3^U!7,WS'T+U+U,V!4,X+3T,^E^[,^0!2#1#9#4!2'^P7#6!1'_W,\!1'_W_2!1'_W_3!1'_W_4!1'_W_5!1'_W_6!1'_W_7!1'_W_8!1'_W_9!1'_W_:!1,:_;!2'7CC!2'7_=C!2'7_>C!2'7_?C!2'7_@C!2'7_AC!2'7_BC!2'7_CC!2'7_DC!2'7_EC$x;R+3#1$x;R+3!2'7#1C!2,Y+3C!2'_:\!2'_;\<!2'`1_J7$z;R+3!3+F+3#1!2'7H^S!3,_M+3^H^P!2'_=<#4!1'`4#2!7,WS'T+U+U,V!4,X+3^I,ZT,^0!2,Y+32!7,^FS'T+U+U,V_P!7,WS'T+U+U,V!4,X+3T,^E!3,^=+3_Q!1,13,^0!2'^M=7!1,^1'`8!9,`7_T_T!2,^A!2+`9+_7+3!4,`:+_7+3#3,6,6,6,6CG_O!2'92E!7,WS'T+U+U,V!4,X+3^I,ZX,^0!2'5,69$rid;R+_7$n;R+3$Hn;R6!6'^9+3!2'^M:7$z;R+3!3+F+3#1;!6'^9+3=$z;R+3!3+F+3!2'^M#17;vdvd!6'^9+3!2'_<?<$z;R+3!3+F+3!2'^M!2'_:@!2'_;@<7!2'7H!2'_=<#1&H;R&__sat1;RIK&__sat0;RMN&__arith;R$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!7,WS'T+U+U,V!4,X+3V,_>X,^0YZ%__x1;R+3!3+F+3!2'7#1>!2'7!2'7#178!1#1#5!3+F+3?9!6'^@+3[$z;R+3!3+F+3!2'^M!2'_:#1!2'_;#1<7!2'7H!2'_=<!2'_<\<&D;R!3'^L^0,6$i;R+3$Hi;R0!6'^9+^5!2'^Q!2'^P^3#2!2'^P7#2$b;R+^5!3+F+^5#1!2'^P,6#3!6'^9+^5,^[$b;R+^5!3+F+^5!2'^Q!2'^P^6#3!2'^P7#3#1&H;R&H;R!2'_?^1<%~R^8!3+F+3^4!2'7^9^5&H0;R!2'_A^4<%~R^:!2+;!2'5,6^<!2'<^<<&H1;R!2'_B^;<%~R^=!2+;!2'<<^?!2'5^?,6&H2;R!2'_C^><%~R^7!3+F+3^A,6&H3;R!2'_D^@<%~R^7!3+F+3^C^B&q;R^D+3&r;R!2'_;^E<+3&__sat5;RIK&__sat4;RMN&__arith;R$__x3;R+3$__x2;R+3$__x1;R+3&__wit;R^FP&__varmap;R^GR&__ff;R!8,RS'T+U+U,V!8,RS'T+U+U,V^J^K!7,WS'T+U+U,V!4,X+3^M,_>!3,^<+3^N^P,^0^K!7,WS'T+U+U,V!4,X+3^N,_>!3,_N+3^M^P,^0YZ%__x3;R+3%__x2;R+3%__x1;R+3%~R%~R^Q!3+F+3[!2'7^R#4!3+F+3^R!2'_:[#4!4#1#4#?#5#:!3+F+3^S^3!6'^@+3^9$z;R+3!3+F+^5!2'^Q!2'^P#1#4!2'^P7#4,^[&o;R!2'_P#3^U!2+_Q!2'<#3^U!2'5^U#3!6'_R^V^W!3+F+^5!2'^Q!2'^P!2'_=<!2'_<!2'7#7><#4!2'^P7#4,^[$~R^V!1$H;R!2'<#5^U!6'^9+3!2'_=^A<$z;R+3!3+F+^5!2'^Q!2'^P#1#7^X,^[!6'^9+^5,^[$b;R+^5!3+F+^5!2'^Q#1^X,^[!2,^4+^5,^[!2'^P!2'_=^Z^Y#6!4'_S^Z^U#6&__sat1;RIK&__sat0;RMN&__arith;R$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!8,RS'T+U+U,V^\^K^\YZ%__x1;R+3%~R!2'<#1^U!2'<#2^U_0!2'_=<^A!2'_T<^A#1$~R^W!1$H;R!2'5^U#5&H0;R!4'_U+^5_1,^[!4'_V7#6&__sat1;RIK&__sat0;RMN&__arith;R&__wit;ROP&__varmap;R!1,^;+3R&__ff;R!7,WS'T+U+U,V!4,X+3^I,ZW,^0YZ!2'5,67#1vd!4'^I!2'<_<#6!2'<_F#6!<'^C+3+3'<_G'<$x;R+3$y;R+3!1'_X!2'<#2#1_<_F!<'_Y+_Z+3+3+3,:,:_G_G$x;R+_Z!2,^4+3!1,:#1_;_F!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_:_E!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_9_D!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_8_C!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_7_B!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_6_A!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_5_@!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_4_?!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_3_>!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[_2_=!<'_Y+_Z+_Z+3+3'_W,:,:_H'_[,\C!2,^4+3C#6#6!2,^4+3#6&__sat1;RIK&__sat0;RMN&__arith;R$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!8,RS'T+U+U,V!7,WS'T+U+U,V!4,X+3^[,ZT,^0^K!7,WS'T+U+U,V!4,X+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3!3,^<+3_I_I_I_I_I_I_I_I_I_I_I,^ET,^0YZ%__x1;R+3%~R!2'5^U#1!2'<_F#2_0!2'<!1'_\7#6!3+F+^5,^[_1!6'^@+^5,^[$b;R+^5!3+F+^5!2'^Q!2'^P!2'_=<!2'_<^E<#8#1,^[!1'_2!2'^P!2'_=<^D#7^X#1#1#1^6#1!2'^P,6#2!1'`0#2!2'^P!2'^N^37#2!3'_5^37#2!3+F+3^0,6!6'^@+3_K_L!6'^@+3!2'7_J7_L&H;R!2'_?\<%~R^8!3+F+3^1!2'7^S^2&H0;R!2'_A^1<%~R^:!2+;!2'5,6^5!2'<^5<&H1;R!2'_B^4<%~R^=!2+;!2'<<^<!2'5^<,6&H2;R!2'_C^;<%~R^7!3+F+3!2'_<^><,6&H3;R!2'_D^><%~R^7!3+F+3!2'_;^@<^@&q;R^A+3&r;R^C+3&__sat5;RIK&__sat4;RMN&__arith;R$__x3;R+3$__x2;R+3$__x1;R+3&__wit;R^FP&__varmap;R^GR&__ff;R!8,RS'T+U+U,V!8,RS'T+U+U,V^J^K!7,WS'T+U+U,V!4,X+3V,_>!3,^<+3_M^L,^0^K!7,WS'T+U+U,V!4,X+3!3,^<+3!3,_N+3V^LW,_>!3,^<+3!3,^<+3!3,^<+3^I!3,_M+3!2,Y+3B_I!3,_M+3!2,Y+3E!2,Y+3G_M,^0YZ%__x3;R+3%__x2;R+3%__x1;R+3%~R%~R^Q!3+F+3?!2'7_N#3!3+F+3!2'7!2'_:?#37!2'7H_N!4#1#5#4#>#:_K!3'`2_J7#1!2'^M_J7!3'`3_J7#1@#1_O!2'`5#2&__sat1;RIK&__sat0;RMN&__arith;R$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!8,RS'T+U+U,V_R^K_RYZ%__x1;R+3%~R6!2+;!2'5,6#2!2'<#25!2#1#5#4!3+F+3_S!2'7!2'7!2'7!1'`6_U!2'_=B!1'`;_U!2'_=E!1'`<_U!2'_=<!1'`=_U!3+F+3_S!1'_8!2'_9#3#2:!2'`>9&__sat3;RIK&__sat2;RMN&__sat1;R!2'K2E%~RJ%~R!2'5,6E!2'<,6_V&__sat0;R$Ha;RL$~R+L!3'M2E#2%Ha;RL%~R+L!2'5,6_V&__arith;R$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!8,RS'T+U+U,V_R^K!7,^FS'T+U+U,V_W!7,WS'T+U+U,V!4,X+3X,^E!3,^=+3_Q!1,1D,^0YZ%__x1;R+3%~R6!2+;_X!2'<9_V!2#1#7#6!2'^M!2'^N9!1,:|^B7ffffffffffff800;7!2'`?9&__sat1;RIK&__sat0;RMN&__arith;R$__p1;Rw$__x1;R+3&__wit;ROP&__varmap;RQR&__ff;R!8,RS'T+U+U,V!7,^FS'T+U+U,V_P!6,^ZS'T+U+U,V#4^K_WYZ%__p1;Rw%__x1;R+3%~R!2+;0#2_X!3#1!2'<#55#5#4").
Qed.

Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
  rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; Z.div_mod_to_equations; lia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma rbig_fail1_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xaccb4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Lemma rbig_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt rsegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom rsegs)
                        /\ stk rsegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xace80) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Lemma rbig_fail2a_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells rsegs m RMLOCK [C4 (wz 0)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0xace80) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xacda8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros LK. unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0xace74)) with (Z_to_bv 64 0xace74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed.

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 37 "S80!1,1|600;!1+00|21;|500;|30;%~R1!1+2!1+0!1,14!2'7!2'`B0#Y!1,_I|510;!2+`9+3+3$sp;R1$gp;R1$tp;R1$s5;R1$s6;R1$s7;R1$s8;R1$s9;R1$s10;R1$s11;R1$t0;R1$t1;R1$t2;R1$a2;R1$a3;R1$a4;R1$a5;R1$a6;R1$a7;R1$t3;R1$t4;R1$t5;R1$t6;R1$nw;R1$xw;R1$rav;R1$s0v;R1$s1v;R1$s2v;R1$s3v;R1$s4v;R1$F;R!2'`Q!1,121$fc;R!1+0!1,13$lo;R+3$st';R+c:$m;R'`R$n;R+3$ms';R+`Z!2+c;1$a0;R1!2+c;1$a1;R1!2+c;5$m';R5!2+;!3+F+`Z#4!7'`[!O'`\!2'`A0!1,:|C2cda8;!2'`A06#X#W#O#N#M#B!2'`A0'a2#3#2#L#K#J#I#H#G!2'`A0!1,_I,\!2'`A0!2'7#5!1,:|44;#A#V#U#T#S#R#Q#P#F#E#D#C#:!2'`A0'c<#9!1,^11#1!1'a1'>!2+;!3'c=!3,?7!4,`:+3+3!2'7'c>!1,:|9150;!2'7'c>!1,:|9170;!3,?7!4,`:+3+3!2'7'c>!1,:|9190;!2'7'c>!1,:|9191;!1,A7#6#1!2+;!3'c?'>#6#1!2+;!2'c@'>#1!2+;!4'`V'>#1#86!2+;!4'`S'>#16!3,?+`T!1,`U#;!3,?+`T!1,`U#<!3,?+`T!1,`U#=!3,?+`T!1,`U#>!3,?+`T!1,`U#?!3,?+`T!1,`U#@!1,A+`T!3'cA/RUNp;#7#1").

(* [comment removed for export] *)
Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo -> mem_inv rsegs m ->
  evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xaccb4) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  (pose_ceil; unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *). unfold ctx_tail_cells in C6.
  replace (1022512 + 912) with 1023424 in C6 by reflexivity. replace (1022512 + 848) with 1023360 in US by reflexivity.

  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.

  step. step. step. rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.

  step. rewrite ?zxb_b8 by lia. step.

  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells rsegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk rsegs mj lo (bv_unsigned sp + -48) -> mem_inv rsegs mj ->
    munch [(1022512 + 848, 1022512 + 880); (1022512 + 912, 1022512 + 913)]%Z m mj -> wmono rsegs m mj ->
    evt rsegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 1022504)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xacda0) fc None mj (seg_rom rsegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (1022512 + 912) with 1023424 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 1023424) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (1022512 + 912) [b8 ns] FRj STj MUj WMj SOK.

    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  -
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  -
    pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr rsegs m1 1023360 (zeros 32)).
    { apply (u8arr_of_rw_cells rsegs m1 1023360 32). apply (rw_cells_congr rsegs m1 1023360 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono rsegs m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (1022512 + 912) with 1023424 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.

    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX, FRc : rw_cells rsegs ?mX (bv_unsigned sp + -48) _, STc : stk rsegs ?mX _ _, MIc : mem_inv rsegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^48.
Hypothesis CLO : alloc_ceiling <= lo.

Lemma rbig_succ_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xacf40) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xacda8) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].

  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells rsegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; pose_ceil; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }

  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  (pose_ceil; unfold RCTX, RMLOCK in *).

  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.

  unfold ctx_head_cells in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix rsegs m _ [C8 (wz (c_secret (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

  step. step.

  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl rsegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells rsegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.

  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells rsegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.

  step. rewrite (sx32_wz_sxv c) by lia. step.

  lazymatch goal with H : rw_cells rsegs ?mX 1022512 _ |- _ =>
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 1022524) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (1022512 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.

  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed.
End SUCC.
End CEIL_WRAP_1.

