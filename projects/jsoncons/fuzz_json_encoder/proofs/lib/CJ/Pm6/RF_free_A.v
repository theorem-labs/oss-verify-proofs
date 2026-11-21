(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed meta_word_pg, meta_word_sc2, rfree_head and 3 more. *)
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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_free_A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Pm6 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @eq]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @mw_ok]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freeable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_sizeclass]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_maplen]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_word]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @div_small]; [@Stdlib; @ZArith; @BinInt; @Z; @div_add]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_mul_pow2]; [@Stdlib; @ZArith; @BinInt; @Z; @ldiff_ones_r]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @land_ldiff_distr]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @mstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aptr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @region]; [@Corelib; @Init; @Datatypes; @snd]; [@Corelib; @Numbers; @BinNums; @N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_meta_rec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @wr16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @aadd]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @wr8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @F_syscalls; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ticks_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocTree; @rpres_except]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@stdpp; @base; @lookup]; [@stdpp; @gmap; @gmap]; [@stdpp; @numbers; @N; @eq_dec]; [@stdpp; @countable; @N_countable]; [@stdpp; @gmap; @gmap_lookup]; [@Corelib; @Init; @Datatypes; @fst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_regions]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @rkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @RKGroup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @round_up_pg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @r_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_slot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cellval]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @cell_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @Known]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @b8]; [@Corelib; @Init; @Datatypes; @prod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ghdr]; [@stdpp; @decidable; @prod_eq_dec]; [@stdpp; @numbers; @Z; @eq_dec]; [@stdpp; @countable; @prod_countable]; [@stdpp; @countable; @Z_countable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_groups]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rregions_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_globals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_areas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_groups]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @rfhead_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_reserved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @ref_reserved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ranges_free]; [@Corelib; @Init; @Logic; @not]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @lr_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @area]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @s_areas]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rreserved_disjoint]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @Tauto; @X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @RunP; @alloc_ceiling_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rmeta_slot_bounds]; [@Stdlib; @ZArith; @BinInt; @Z; @ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @wz_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_read]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Datatypes; @length]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zxb]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_byte]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sllw]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_sllw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @sxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_store_ok]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le1]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_1']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_wr8]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @N2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @N2Z; @is_nonneg]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @le1_neg1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv_store]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at_write_other]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wr_at_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_write]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @ticks_ok_wr8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le2]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_2']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_wr16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le2]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addiw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @w_addiw]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rpres_except_of_munch_cov]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RCTX]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B; @ivs_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocTree; @rpres_except_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @F_malloc_free; @all_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_get_meta; @sllw1_word']; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zxb_b8]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @get_stride]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @UNIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @IB]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @optr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_avail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_freed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @conc_region']; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_meta_chunk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @meta_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_prev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @m_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_mul]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @m_mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @oconc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_srli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_srli]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @rfree_head3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le4]; [@Stdlib; @Lists; @List; @firstn_all2]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_le4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @zx32_wz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @g_meta]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @area_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @a_check]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @c_secret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @ctx]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @Malloc; @size_class]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rfree_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_shadow_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @length_le8]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rmrep_transport_high]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @W_high]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_get_meta; @rget_meta_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_get_meta; @rget_meta_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_maplen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocKit_B3; @meta_word_last_idx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @meta_word_sc2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @meta_word_pg]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocKit_B; @rfree_fp_stack]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RF_free_A; @CEIL_WRAP_1; @rfree_head2]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @RSIZE_CLASSES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Pm6; @RMallocRep; @rsize_classes_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @size_class_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zx16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_extract_le2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @zx16_wz]; [@Corelib; @Init; @Logic; @or_introl]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Agent; @MallocRep; @land_pgmask]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := (pose_ceil; unfold UNIT, IB in *); lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof.
  intros (LI & FB & SCR & ML).
  assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by reflexivity. rewrite E, land_ldiff_distr.
  rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
  rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
  replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
  rewrite Z.mod_add, Z.mod_small by lia.
  replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
  rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof.
  intros (LI & FB & SCR & ML). unfold meta_word.
  replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
    with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
  rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x6 x7 junk m',
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
                  (wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 0xf9390) x5 x6 x7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xac394) fc None m' (seg_rom rsegs)
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rmrep st1 m'.

(* [comment removed for export] *)
Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
  stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 ->
  r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  0 <= rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac344) fc None m0 (seg_rom rsegs)).
Proof.
  intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  (pose_ceil; unfold UNIT, IB in *).
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read rsegs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.

  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }

  st1. st1. st1. st1. st1. st1.
  rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).

  pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK3 : store_ok rsegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
      by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
  st1.
  pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
  cbn [aadd snd] in MR2. fold po in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
      by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
  store_done.
  pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
    assert (SOK2 : store_ok rsegs mX (wa (bv_unsigned a0 + -2)) 2 = true)
      by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok rsegs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
  st1.
  pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
  cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
      by (f_equal; unfold wa; f_equal; lia) end.
  store_done. clear MR2 TK2 HWr HWr2.

  st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
  replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
  st1.

  apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|exact I].
      intros x Hx. right. right. exists (fst p), r.
      assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
      destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [exact Hr|]); (split; [exact Hk|]); (split; [lia|]); assumption. }
  apply evt_done. unfold rfhead_post.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
  do 6 eexists.
  split; [reflexivity|].
  split; [eapply rpres_except_trans; [exact PE0| exact MU]|]. split; [exact WM0|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. exact MR3.
Qed.

(* [comment removed for export] *)
Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
    (m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base : aptr) (b3 lo8 hi r32 : Z),
  let po := snd p in
  let idx := Z.land b3 31 in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m0 -> mem_inv rsegs m0 -> ticks_ok st ->
  stk rsegs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells rsegs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono rsegs m m0 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  meta_slot st g -> m_mem mr = Some base -> fst base = fst p -> 0 <= snd base ->
  cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  0 <= b3 < 256 -> idx <= m_last_idx mr ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m0 (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m0 (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m0 (E - rsv) [b8 0] -> bytes_at rsegs m0 E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac2fc) fc None m0 (seg_rom rsegs)).
Proof.
  intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
         AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  (pose_ceil; unfold UNIT, IB in *).
  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.

  st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
  replace (conc st base + stride + stride * idx + 12) with E by (unfold E; lia).
  fold rsv0.

  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  -
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
  -
    destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read rsegs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (conc st base + stride + stride * idx + 8) in RD4 by (unfold E; lia).
    pose proof (bytes_at_read rsegs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (conc st base + stride + stride * idx + 7) in RD5 by (unfold E; lia).

    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

    st1.
    rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
    subst mr.
    eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
      [exact MR1| exact MI| exact TK| exact ST| pose_ceil; lia| lia| exact FR| exact PE0| exact WM0| exact Hr| exact Hk| exact HP| exact AL| lia| lia
      | exact MSL| exact HK3| exact HK2| exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| exact RB0r| exact RE0| exact HCLR].
Qed.

(* [comment removed for export] *)
Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo8 + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
  let stride := get_stride mr in
  let E := conc st base + UNIT + stride * idx + stride - IB in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  rmrep st m -> mem_inv rsegs m -> ticks_ok st ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
  bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
  16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
  0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->
  (* [comment removed for export] *)
  (m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
  UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at rsegs m (E - 4) (le4 (wz r32)) /\ bytes_at rsegs m (E - 5) [b8 0]) ->
  rsv <= E - (r_base r + po) -> bytes_at rsegs m (E - rsv) [b8 0] -> bytes_at rsegs m E [b8 0] ->
  (forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
  evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until r32. intros sh po off16 idx base mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
         AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl rsegs m) as WM.
  assert (IDX : 0 <= idx < 32).
  { unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (FB : fst base = fst p) by reflexivity.
  assert (HB : conc st base = r_base r + snd base) by (apply conc_region'; rewrite FB; exact Hr).
  assert (SB0 : 0 <= snd base) by (unfold base; cbn; unfold UNIT; lia).

  revert BIG RB0r RE0.
  (pose_ceil; unfold rfree_entry, UNIT, IB in *). intros BIG RB0r RE0.

  st1. if_cases K0; zify_cond K0. { exfalso. lia. }
  carve_frame 48%nat ST.
  st1. st1. st1. st1. st1. st1. st1.

  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; pose_ceil; lia) end.
  eapply evt_cut.
  { eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
    all: try eassumption. all: try lia. }
  intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
  replace (ret_pc (Z_to_bv 64 0xac2b4)) with (Z_to_bv 64 0xac2b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
    destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
  fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
  replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
  set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (MW : mw_ok mr) by (unfold mw_ok; lia).
  pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
  pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (K2 : forall a4v a5v a6v, evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0xac2b4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
                (Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac2fc) fc None mX (seg_rom rsegs))) end.
  { intros a4v a5v a6v.
    lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
    lazymatch type of MUs with munch ?W m ?mY =>
      assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
        by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [exact MUs| exact WM|];
            cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
    subst rsv rsv0 E stride mr.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base b3 lo8 hi r32) end;
      [exact MR1| assumption| exact TK| exact ST| ulia| ulia| exact FR| exact PE0| exact WM| exact Hr| exact Hk| exact HP| exact AL| ulia| ulia
      | exact MSL| exact Hmem| exact FB| exact SB0| exact HK3| exact HK2| exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
      | intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [exact X1|]; split; [exact X2|]; split;
          (eapply bytes_at_transport; [eassumption| exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
      | ulia
      | exact RB0r
      | exact RE0
      | exact HCLR]. }

  st1. st1. st1. st1. fold idx. rewrite MW12.
  assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
    evt rsegs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
      (MS (mkR (Z_to_bv 64 0xac2b4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
                a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xac2e0) fc None mX (seg_rom rsegs))) end.
  { intros a2v a4v COND. specialize (SC48 COND).
    assert (STR : stride = 16 * size_class (m_sizeclass mr)).
    { unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
      rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }

    assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
    replace (123112 + m_sizeclass mr * 2) with (123112 + 2 * m_sizeclass mr) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (RS' : ov_read_bytes rsegs mX (Z_to_bv 64 (123112 + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
    { replace (Z_to_bv 64 (123112 + 2 * m_sizeclass mr)) with (wa (RSIZE_CLASSES + 2 * m_sizeclass mr)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
      apply rsize_classes_read; [assumption| lia]. }
    pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
    st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
    st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
    replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
    rewrite Egw. apply K2. }

  st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - apply KS. left. exact Km.
  -
    st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
    + apply KS. right. exact Kl.
    +
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
      2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
      rewrite Egw. apply K2.
Qed.
End CEIL_WRAP_1.

