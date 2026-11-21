(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed ram_entry, rmemcpy_callZ3, rrw_cells_app_join and 2 more; added aux_br, aux_cur, aux_cur_25 and 4 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/CJ/Pm10/RF_am_E.v, lines 39-48, 55-62, 68-73, 79-223, 231, 246-345. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import F_memcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @length]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_memcpy; @memcpy_post]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_memcpy; @memcpy_spec]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_memcpy; @rsegs]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64s]; [@Stdlib; @Lists; @List; @nth_error]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64s_split]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Nat; @mul]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @mul]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_mul]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Lists; @List; @app_nil_r]; [@Stdlib; @Lists; @List; @firstn_0]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub_diag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Stdlib; @Lists; @List; @firstn_all2]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @Lists; @List; @firstn_app]; [@Stdlib; @Lists; @List; @app_nil_l]; [@Stdlib; @Lists; @List; @skipn_0]; [@Stdlib; @Lists; @List; @skipn_all2]; [@Stdlib; @Lists; @List; @skipn_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_ov_read]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_prefix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_app]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @wr_at_sub]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Corelib; @Init; @Logic; @not]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @wview]; [@Stdlib; @ZArith; @BinInt; @Z; @lt_ge_cases]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSSP_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RMLOCK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_A; @ram_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_am_E; @am_init_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocTree; @rauxv_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_init_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_secret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @secret_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_secret]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_E; @CEIL_WRAP_1; @ram_entry_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_head_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @actives]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @usages]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @unmap_seqs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @bouncess]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_tail_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RNEED_LOCKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RPAGE_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RGOT_SSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @canary_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RAUXV_CELL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocTree; @auxv_list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_mmap_counter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_free_meta_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_count]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_area_count]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_alloc_shift]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_area_head]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_meta_area_tail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_avail_meta_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_E; @CEIL_WRAP_1; @ru64s_read]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_E; @CEIL_WRAP_1; @rrw_cells_app_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_E; @CEIL_WRAP_1; @rmemcpy_callZ3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@Stdlib; @micromega; @Tauto; @NOT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_transport_high]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @W_high]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @upd_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_init_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_secret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_ctx_frameW]; [@stdpp; @gmap; @gmap]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @numbers; @N; @eq_dec]; [@stdpp; @countable; @N_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @region]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_regions]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@stdpp; @decidable; @prod_eq_dec]; [@stdpp; @numbers; @Z; @eq_dec]; [@stdpp; @countable; @prod_countable]; [@stdpp; @countable; @Z_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_metas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @area]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ghdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_reserved]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_ctx]; [@Corelib; @Init; @Logic; @or_intror]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_am_E; @CEIL_WRAP_1; @rrw_cells_app_join]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @sx32_wz]].

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at rsegs m S src -> length src = Z.to_nat n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xba65c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

(* musl's [get_random_secret] auxv walk, proved once for any pair list [L]:
   [for (i=0; auxv[i]; i+=2) if (auxv[i]==AT_RANDOM) memcpy(&secret, (char* )auxv[i+1]+8, 8);]
   The loop head is 0xac9c8 (s1 = 16 * pairs done, a0 = av, s4 = 25); the
   AT_RANDOM body is 0xac9ac (memcpy to the frame cell 0(sp)); the exit is 0xac9d8.
   [aux_cur pre b0] is the frame cell after the pairs [pre]: the secret once an
   AT_RANDOM pair was seen, else the initial bytes [b0]. *)
Definition aux_cur (pre : list (Z * Z)) (b0 : list byte) : list byte :=
  if existsb (fun p => fst p =? 25) pre then le8 (wz secret_val) else b0.

Lemma aux_cur_25 : forall pre v b0, aux_cur (pre ++ [(25, v)]) b0 = le8 (wz secret_val).
Proof.
  intros pre v b0. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(25, v)]) with true by reflexivity.
  rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma aux_cur_skip : forall pre k v b0, k <> 25 -> aux_cur (pre ++ [(k, v)]) b0 = aux_cur pre b0.
Proof.
  intros pre k v b0 Hk. unfold aux_cur. rewrite existsb_app.
  replace (existsb (fun p : Z * Z => fst p =? 25) [(k, v)]) with false
    by (symmetry; cbn [existsb fst]; rewrite Bool.orb_false_r; apply Z.eqb_neq; exact Hk).
  rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma aux_cur_last : forall L b0 r, last_assoc 25 L = Some r -> aux_cur L b0 = le8 (wz secret_val).
Proof.
  intros L b0 r H. apply last_assoc_In in H. unfold aux_cur.
  replace (existsb (fun p : Z * Z => fst p =? 25) L) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists (25, r). split; [exact H| reflexivity].
Qed.

Local Ltac aux_br :=
  lazymatch goal with |- context [bv_eqb ?x ?y] =>
    first [ replace (bv_eqb x y) with true
              by (symmetry; unfold bv_eqb; apply Z.eqb_eq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia)
          | replace (bv_eqb x y) with false
              by (symmetry; unfold bv_eqb; apply Z.eqb_neq; rewrite ?wz_unsigned, ?unsigned_lit by lia; lia) ]
  end;
  try change (negb true) with false; try change (negb false) with true; cbv iota.

Definition raux_post (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 1022128) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xac9d8) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 (aux_cur L b0)].

Lemma raux_walk : forall (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (av rnd : Z) (L : list (Z * Z)) (b0 : list byte) (m0 : word -> option byte),
  rw_cells rsegs m0 RAUXV_CELL [C8 (wz av)] ->
  bytes_at rsegs m0 av (u64s (map wz (flat_pairs L ++ [0; 0]))) ->
  bytes_at rsegs m0 (rnd + 8) (le8 (wz secret_val)) ->
  Forall (fun p => fst p <> 0) L -> Forall (fun p => fst p = 25 -> snd p = rnd) L ->
  Forall (fun p => 0 <= fst p < 2^64 /\ 0 <= snd p < 2^64) L ->
  RAUXV_CELL + 8 <= bv_unsigned sp + -64 -> bv_unsigned sp <= av -> av + 16 * (Z.of_nat (length L) + 1) <= 2^64 ->
  bv_unsigned sp <= rnd + 8 -> rnd + 16 <= 2^64 -> 64 <= bv_unsigned sp ->
  forall post pre (m : word -> option byte) (x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  L = pre ++ post -> bv_unsigned s1 = 16 * Z.of_nat (length pre) ->
  munch [(bv_unsigned sp + -64, bv_unsigned sp + -64 + 8)]%Z m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 8 (aux_cur pre b0)] ->
  evt rsegs (raux_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av L b0 m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 1022128) s1 (wz av) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 25) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac9c8) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 F fc av rnd L b0 m0 AVC AVL RND NZ R25 RNG HC HAV HAVH HR HRH HSP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAUXV_CELL in HC, AVC.
  assert (WZAV : bv_unsigned (wz av) = av) by (apply wz_unsigned; lia).
  induction post as [|[k v] post IH]; intros pre m x1 t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EL HS1 MU WM MI FR.
  - (* AT_NULL: leave the loop *)
    rewrite app_nil_r in EL. subst L.
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs pre ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz 0) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_end pre) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1. aux_br.
    st1. aux_br.
    apply evt_done. unfold raux_post. do 17 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact FR.
  - assert (IN : In (k, v) L) by (rewrite EL; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) NZ _ IN) as NZk.
    pose proof (proj1 (Forall_forall _ _) R25 _ IN) as R25k.
    pose proof (proj1 (Forall_forall _ _) RNG _ IN) as RNGk.
    cbn [fst snd] in NZk, R25k, RNGk.
    assert (LL : Z.of_nat (length L) = Z.of_nat (length pre) + 1 + Z.of_nat (length post))
      by (rewrite EL, length_app; cbn [length]; lia).
    assert (AVLm : bytes_at rsegs m av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    assert (AVCm : rw_cells rsegs m 0xf98b8 [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]]).
    assert (RNDm : bytes_at rsegs m (rnd + 8) (le8 (wz secret_val)))
      by (eapply bytes_at_transport; [exact RND| exact MU| cbn [disjoint_from]; split; [lia| exact I]]).
    st1.
    pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre)) (wz k) (wa (av + 8 * (2 * Z.of_nat (length pre))))
                  AVLm (flat_pairs_nth_key L pre k v post EL) ltac:(lia) eq_refl) as RD.
    st1. clear RD.
    st1.
    destruct (Z.eq_dec k 25) as [K25|K25].
    + (* AT_RANDOM: copy the 8 bytes at value+8 into the frame cell *)
      subst k. specialize (R25k eq_refl). subst v.
      aux_br.
      pose proof (ru64s_read m av _ (2 * Z.of_nat (length pre) + 1) (wz rnd) (wa (av + 8 * (2 * Z.of_nat (length pre) + 1)))
                    AVLm (flat_pairs_nth_val L pre 25 rnd post EL) ltac:(lia) eq_refl) as RD.
      st1. clear RD. st1. st1. st1. st1.
      call rmemcpy_callZ3.
      1:{ exact RNDm. } 1:{ reflexivity. } 1:{ exact FR. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      1:{ lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end. }
      lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (le8 (wz secret_val))] |- _ => rename H into DST end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mY _) =>
        assert (AVCy : rw_cells rsegs mY 0xf98b8 [C8 (wz av)])
          by (eapply rw_cells_transport; [exact AVC| exact MU| exact WM| cbn [disjoint_from cells_size csize]; split; [lia| exact I]])
      end.
      st1. st1.
      eapply (IH (pre ++ [(25, rnd)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end.
      * rewrite aux_cur_25. exact DST.
    + (* any other key: skip the pair *)
      aux_br.
      st1. aux_br.
      st1.
      eapply (IH (pre ++ [(k, v)])).
      * rewrite <- app_assoc. exact EL.
      * rewrite length_app. cbn [length]. first [rewrite unsigned_lit by lia; lia | rewrite wz_unsigned by lia; lia | lia].
      * exact MU.
      * exact WM.
      * exact MI.
      * rewrite (aux_cur_skip pre k v b0 K25). exact FR.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 21 "S=0|600;!1,10!1+01|21;|500;|30;!1+0!1,15%~R2!1+36!1+56!2'^O1#Y!2'C9!1,_L0!2+^\+4+4|40;$ra;R2$sp;R2$gp;R2$tp;R2$s0;R2$s1;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$F;R!2'2!1,132$fc;R!1+0!1,14$lo;R+4$st;R+`N$m;R7$ms';R+^U!2+^V2$x1;R2!2+^V2$t0;R2!2+^V2$t1;R2!2+^V2$t2;R2!2+^V2$s1x;R2!2+^V2$s4x;R2!2+^V2$a0;R2!2+^V2$a1;R2!2+^V2$a2;R2!2+^V2$a3;R2!2+^V2$a4;R2!2+^V2$a5;R2!2+^V2$a6;R2!2+^V2$a7;R2!2+^V2$t3;R2!2+^V2$t4;R2!2+^V2$t5;R2!2+^V2$t6;R2!2+^V7$m';R7!2+^V8$junk;R8!2+U!3+8+^U#E!7'^W!O'^X#D!2'^P1:#X#W#C#B#A!2'^P1!1,E|<000;#@#>#=#<#;#:#9#8#7!2'^P1'`O!2'^P1'`P#?#Q#P#O#N#M#L#K#6#5#4#3#J!2'^P1!1,E|C2c9f8;#I!1,^E2#2!1'^Z'7!2+U!3'^[!3,=;!4,_0+4+4!2'`M9!1,E09!3,=;!4,_0+4+4'`Q!2'C'`Q!1,E<!1,@;#F#2!2+U!3'_1'7#F#2!2+U!2'H'7#2!2+U!4'<'7#2:!8'`R/RUNp;#1#R#S#T#U#V#Z!2+U!4'`S'7#2#H:!3'`T/RUNp;!1'`U#G#2").

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv rsegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = secret_val -> 0 <= c_secret (ctx st) < 2^64 ->
  evt rsegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac944) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold ctx_head_cells in C1.
  (pose_ceil; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *). unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & L & rnd & AVC & AVL & RND & (AB & BAV & AVH & BR & RH & XR) & NZ & LA & R25 & RNG).
  pose proof (conj AVC (conj AVL RND)) as AUX0.
  unfold RAUXV_CELL in AVC.

  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.

  st1. st1. st1. st1. st1. st1.

  st1. rewrite sx32_wz by lia. st1. st1.

  st1.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; pose_ceil; lia. }

  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.

  st1. st1. st1. st1. st1. st1. st1. st1. st1.

  (* The auxv walk 0xac9c8..0xa7dbc, for any layout: [raux_walk]. *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge rsegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  destruct AUX0 as (AVC0 & AVL0 & RND0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (AVCx : rw_cells rsegs mX RAUXV_CELL [C8 (wz av)])
      by (eapply rw_cells_transport; [exact AVC0| exact MUh| exact WM| cbn [disjoint_from cells_size csize]; split; [unfold RAUXV_CELL; lia| exact I]]);
    assert (AVLx : bytes_at rsegs mX av (u64s (map wz (flat_pairs L ++ [0; 0]))))
      by (eapply bytes_at_transport; [exact AVL0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    assert (RNDx : bytes_at rsegs mX (rnd + 8) (le8 (wz secret_val)))
      by (eapply bytes_at_transport; [exact RND0| exact MUh| cbn [disjoint_from]; split; [lia| exact I]]);
    lazymatch type of FRm with rw_cells _ _ _ [CB _ ?bz] =>
      eapply evt_cut;
      [ eapply (raux_walk sp gp tp _ _ _ _ _ _ _ _ _ F fc av rnd L bz mX AVCx AVLx RNDx NZ R25 RNG
                  ltac:(unfold RAUXV_CELL; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L []);
        [ reflexivity | first [reflexivity | vm_compute; reflexivity] | apply munch_refl | apply wmono_refl | assumption | exact FRm ]
      | post_call rsegs mX ]
    end end.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) [CB _ (aux_cur _ _)] |- _ => rename H into DST end.
  rewrite (aux_cur_last L _ rnd LA) in DST.

  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz secret_val)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.

  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; pose_ceil; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.

  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret secret_val c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells rsegs ?mX 1022512 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.

  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
End CEIL_WRAP_1.

