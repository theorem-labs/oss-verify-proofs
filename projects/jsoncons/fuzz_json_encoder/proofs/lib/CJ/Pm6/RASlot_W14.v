(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed land224_m32, rtail_walk, sx32_congr and 3 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/CJ/Pm10/RASlot_W14.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, lines 25-27, 32-35, 41-44, 49-62, 106-181, 186-311. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W3 ASlot_W14.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @Z_to_bv_eqm]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_l]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_mod32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @mod_mod_pow2]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv_range]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zb_lxor_ones]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_assoc]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RASlot_W14; @CEIL_WRAP_1; @TAIL; @rtailW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmeta_slot_bounds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @ge]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RMLOCK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stFin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ticks_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMalloc_fp; @rregion_facts]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Numbers; @BinNums; @N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @round_up_pg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @conc_region']; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @AV_FR_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mask_upto]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_hdr_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @hdr_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_usage_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @usage]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@Corelib; @Init; @Datatypes; @prod]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @pair]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_head_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @actives]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @usages]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8arr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @unmap_seqs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @bouncess]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ctx_tail_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr_store_ok]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @usages_length]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B3; @rmrep_set_usage]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_usage]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @PER_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@Corelib; @Classes; @Morphisms; @trans_co_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @Tauto; @OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @meta_slot_same_areas]; [@stdpp; @gmap; @gmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@stdpp; @decidable; @prod_eq_dec]; [@stdpp; @numbers; @N; @eq_dec]; [@stdpp; @numbers; @Z; @eq_dec]; [@stdpp; @countable; @prod_countable]; [@stdpp; @countable; @N_countable]; [@stdpp; @countable; @Z_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @area]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_slot]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sllw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_sllw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_meta_chunk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_meta_rec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @oconc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mkMeta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freeable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_sizeclass]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_maplen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RASlot_W14; @CEIL_WRAP_1; @unsigned_mod32_pred_sxv]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xori]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RASlot_W14; @CEIL_WRAP_1; @unsigned_mod32_swrap_add_not]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_put_meta_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @recA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_congr]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @le4_congr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_A; @ticks_ok_upd_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_reserved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @ref_reserved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @region]; [@stdpp; @base; @lookup]; [@stdpp; @gmap; @gmap_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_regions]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ranges_free]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @lr_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @rkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @RKGroup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ghdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cellval]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cell_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @Known]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rwr_at_bytes_exist]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @wr_at_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @rw_cells_of_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C1]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMalloc_fp; @rmeta_chunk_facts]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_A; @byte_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @land_upper]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @hdr_byte_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmrep_transport_unowned]; [@Stdlib; @Lists; @List; @In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rrepfoot]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @lr_lo_group]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RNEED_LOCKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RPAGE_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RGOT_SSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSSP_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rarea_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rarea_lr_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rgroup_conc]; [@Stdlib; @NArith; @BinNat; @N; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Stdlib; @ZArith; @Znat; @N2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @N2Z; @is_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @cell_read_hdr_havoc_old]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @Unknown]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @ivs_avoid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_A2; @rmrep_put_group_new]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @Malloc_fp; @actives_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @put_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @get_meta_rec_put_same]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr_frame]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u64arr_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @active]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @Malloc_fp; @actives_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @recF]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @stE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_set_active]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @set_active]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @lor_small_shl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @lor_shl_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @land_pg_mask]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_A3; @le1_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RASlot_W14; @CEIL_WRAP_1; @land224_m32]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @ASlot_W14; @sllw2_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RASlot_W14; @CEIL_WRAP_1; @sx32_congr]].

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal.
Qed.

Lemma unsigned_mod32_add_not a b : 0 <= b < 2^64 ->
  (bv_unsigned (wz (sxv a)) + Z.lxor b 18446744073709551615) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  intros Hb. rewrite zb_lxor_ones by lia. rewrite (wz_unsigned (sxv a)) by (apply sxv_range).
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l.
  replace (a + (18446744073709551615 - b)) with ((a - 1 - b) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma unsigned_mod32_swrap_add_not a b :
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition rtailW : list (Z * Z) :=
  [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

(* [comment removed for export] *)
Lemma rtail_walk :
  forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
  rmrep stT mC -> mem_inv rsegs mC ->
  evt rsegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xad7ec) fc None m' (seg_rom rsegs)
      /\ munch rtailW mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
      /\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xad694) fc None mC (seg_rom rsegs)).
Proof.
  intros until mC. intros MR MI.
  pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold rtailW in MU.
  pose proof (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). pose_ceil. fold G in Gpos, GC, GI, G4.
  pose proof (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). pose_ceil.
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  pose proof (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.

  destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
  (pose_ceil; unfold RCTX, RMLOCK in *).

  pose proof (rmrep_usage_read (stA stT p) mC sc (wa (1022512 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage (stA stT p) sc) with (usage stT sc) in RDU.
  replace (wa (1022512 + 464 + 8 * sc)) with (Z_to_bv 64 (1022504 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.

  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.

  pose proof MRA as (_ & (_ & _ & USG & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (usages (stA stT p)) sc (wa (1022512 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (1022512 + 464 + 8 * sc)) with (Z_to_bv 64 (1022504 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
  rraw_store_finish0 (1022512 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
  assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.

  step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  rmeta_open G MUa WMa.

  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).

  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }

  step. step.
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
  assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.

  pose proof MRC as (WFC & _ & _ & _ & _ & SHC). pose proof WFC as (_ & _ & DJ & _ & WG).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| lia| lia]) ltac:(lia) ltac:(lia)) as (hb & LHB & HB) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  pose proof (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.

  step.

  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.

  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].

  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.

  lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
      [ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  {
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold RCTX in X1. lia.
    - unfold RMLOCK in X2. lia.
    - unfold RNEED_LOCKS in X3. lia.
    - unfold RPAGE_SIZE in X4. lia.
    - change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
      destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
      destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold RGOT_SSP in X5. lia.
    - unfold RSSP_GUARD in X6. lia. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
  assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.

  pose proof MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
  rmchunk MRD MSTD CH.
  change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  rmeta_open G MUc WMc.

  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.

  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.

  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.

  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read rsegs mX (1022512 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (1022512 + 80 + 8 * sc)) H
                  (actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (1022512 + 80 + 8 * sc)) with (Z_to_bv 64 (1022592 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.

  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.

  step. step. step.

  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tauto. }
  assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
  clear MRD TKD MSTD.

  clear CH3.
  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok rsegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (1022512 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (1022512 + 80 + 8 * sc)) with (Z_to_bv 64 (1022592 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (1022592 + 8 * sc + 0)) with (Z_to_bv 64 (1022592 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
  rraw_store_finish0 (1022512 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.

  step.
  apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
End TAIL.
End CEIL_WRAP_1.

