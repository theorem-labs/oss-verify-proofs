(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed ME, close_kg, drv_file and 10 more; added entry, inp, mbase and 1 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm10DrvG.v, 479 lines within its lines 23-1010. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame LibTail
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib Pm6Startup Pm6MainEntry Hoare MemSplit
  Pm6MemcpyBase Pm6Memcpy Pm6ExitBase Pm6StdioDefs Pm6Exit Pm6LibStdioCall
  HeapIface DrvKit Pm6Drv_defs Pm6DrvLib Pm6DrvA Pm6DrvB Pm6DrvG_defs.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @vals_ev]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Lists; @ListDef; @map]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @gr]; [@Corelib; @Lists; @ListDef; @seq]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@LinuxProcessSemantics; @LinuxProcessSem; @StackLayout; @EntryDraw]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @ENV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @eb]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_lo]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @know_ok]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Plain; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @ksubl_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @know_ok_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @ksubl_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @kn_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knLP6]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @cellR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @cellC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knGbase]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @Zdiv; @Zmod_unique]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @mod_of_decompZ]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @False]; [@stdpp; @bitvector; @definitions; @bv_wrap_small]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_mul64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_small]; [@Stdlib; @Lists; @List; @firstn_nil]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@Corelib; @Lists; @ListDef; @skipn]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @word_to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefReadLib; @word_to_nat_lit]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @file_read]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @file_read_unguarded]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @Lists; @List; @length_skipn]; [@Stdlib; @Lists; @List; @length_firstn]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ELit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @keep_rd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knRe0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @keep_stage]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knRD]; [@Stdlib; @Lists; @List; @flat_map]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Corelib; @Init; @Datatypes; @Some]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @kbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knRa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @msg_refused]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @zbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @hdr_vals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6MainEntry; @p0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6MainEntry; @p1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6MainEntry; @auxvp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6MainEntry; @rnd]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @Lists; @List; @In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @hiv_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_k_per_malloc]; [@Corelib; @Init; @Datatypes; @fst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @CAPk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_b_overhead]; [@Corelib; @Init; @Datatypes; @snd]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_1_r]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@Corelib; @Numbers; @BinNums; @N0]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @or_intror]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @VmMaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hi_heap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hio_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @block_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@stdpp; @base; @NoDup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @refuse_k]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @sc_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SCBr]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @sub_as_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @edenot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @want_x]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @want_x_val]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @mul2_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @cap2_x]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @model_but_vm]; [@Corelib; @Init; @Datatypes; @list_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @cred]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @CAPk_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @dl_k]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @dl_b]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @vals_ev_app_l]; [@Stdlib; @Lists; @List; @Forall_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @lp_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @regs_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srRD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @heap_facts1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @hz_of_block_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @hz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @hiv_facts']; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefNodes; @rz_read_file]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @ECALLW]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @is_ecall_ECALLW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_get]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @reg_val]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_insert]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @fds0]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdFile]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @fds_lookup3]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @model1o]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @m1o_fds]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @Fs]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @fs_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @m1o_fs]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @stage_store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @TASK_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @regupd]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @len_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatExec; @wbytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @with_fds]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @length_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RunEnv; @mkModelE]; [@stdpp; @bitvector; @definitions; @bv_add_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @heap_stagewrite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @above_wbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatExec; @rdn_wbytes_out]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @know_stagewrite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @find_nz]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @sub_block]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @keep_stage_RD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @wbytes_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefReadLib; @rdn_wbytes_self]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @env_app_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @blobs_ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6MainEntry; @blobs0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @sr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @Env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @env_app_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @regs_set_a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ridx]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @rz_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @FUEL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @STOPS_L]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @scr0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srRf0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @scripts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_exec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @carry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_log]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @mem_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @heap_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @log_in_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @IMG_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @above_sp0_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @log_below_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @content_block']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @hz_sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@Stdlib; @Lists; @List; @firstn_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefNodes; @rz_close]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @model2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @cred_exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @close_kg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_48]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_70]; [@Corelib; @Init; @Logic; @proj1]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @regs_ok_by_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srGL]; [@Corelib; @Lists; @ListDef; @nth]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @kentry_ok]; [@Corelib; @Lists; @ListDef; @Forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @kn_blk_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_sptop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relay_know6]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @knGbase_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @with_fds_close]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @fds_remove3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @v_addi_pc4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_pc]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @vals_ev_app_r]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srRe0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @store_ok_of_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @musl; @Pm6MemcpyBase; @MCH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @musl; @Pm6MemcpyBase; @mcH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @musl; @Pm6Memcpy; @ref_memcpy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Hoare; @ret_ok_even]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefPrintfLib; @alu_add_Z]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefMemcpyLib; @keeps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srz_msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @regs_after_keeps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srRe_tk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefMemcpyLib; @callee_kept]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Numbers; @BinNums; @positive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @junk_vals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @sr_after_call_j]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @junk_vals_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @know_blockwrite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @kn_keep_g]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @IMG_CLIENT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @IMG_RW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @keep_rd_Re0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @heap_wbytes]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @firstn_len_firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibTail; @rdn_app_Z]; [@Stdlib; @ZArith; @Znat; @Z2Nat; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @firstn_app_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @hdr_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srRm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @hdr_relay]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_38]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srLP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knLP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @knLP_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefReadLib; @len_word_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvB; @with_fds_read]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @file_read_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @rd_at]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @Morphisms; @respectful]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @PER_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Lists; @List; @Forall_inv]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @know_LP_ranges]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srPa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knRDp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @rPa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @content_block_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @relayV_71]; [@Stdlib; @Lists; @List; @Forall_inv_tail]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @knRD_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knLPp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @sc_ltu_want]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @sc_eq_70_38]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @CAPk_lt10]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knLPg]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @malloc_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srGa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @has_window]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @alu_add_w_lit]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @cap2_x_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit_ok]; [@Stdlib; @micromega; @RingMicromega; @PsatzSquare]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @c_kept]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @keep_alloc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @debit]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vmmaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @m1o_but]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @m1o_vm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @kn_blk2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @MSO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knGa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knGb0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @rdn_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srGb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knGc0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @wbytes_out]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvLib; @free_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srGc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @lb_remove_2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @srGd0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knGd0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @CAPk_S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @loop_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @read_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @srC0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Drv_defs; @knC0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @above_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @model1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @loop_ok]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvA; @file_k]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kread]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kread_rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @flat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @adenot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EMdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EBlob]; [@LinuxProcessSemantics; @Riscv; @Instr; @branch_cond]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @Zdiv; @Z_div_mod_eq_full]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_and64]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @t_die]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @STOPS_Q]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @scr_refuse]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @knLPr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @sc_and3_sp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @msg_refused_k]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @stdio_res]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @SCR_]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @stdio_call]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG_defs; @scR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @stdio_call_sound_fr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @exit_code]; [@Corelib; @Init; @Logic; @eq_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_wb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_wp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_s]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_sp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_fd]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_sr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @sw_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_f]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_bufp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_bufsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6LibStdioCall; @sc_ret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @edenot_add_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @kbytes_rdn_sp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6DrvG; @FPX_1; @DrvG; @m1o_fd2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeLaws; @t_exit_has_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srz_conseq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @W]; [@stdpp; @bitvector; @definitions; @bv_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Exit; @ref_exit_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @know_nth]; [@Stdlib; @Lists; @List; @nth_error]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @exit_common]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6ExitBase; @file_clean]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @stdout_pending]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @Build_exit_common]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @kwr_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @adenot_lit0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ext_val]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @ext_val_zx_id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6Exit; @t_emit_nil_exit]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_blockL" constr(scr) constr(NX) := run_block_gen FUEL STOPS_L scr NX false.
Tactic Notation "run_blockL_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_L scr NX true.
Tactic Notation "run_blockQ" constr(scr) constr(NX) := run_block_gen FUEL STOPS_Q scr NX false.
Tactic Notation "run_blockQ_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_Q scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gr (R : bvmap 5 word) (i : nat) : word := getr R (Z_to_bv 5 (Z.of_nat i)).
Definition relayV (vals : list word) (R : bvmap 5 word) (x38 x48 x70 : word) (ext : list word) : list word := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S90!1,2|600;!1+10!1+01}1}2}3}4}5!1,:1$vals;R2$R;R!2'3!1,2|21;1$x38;R1$x48;R1$x70;R1$ext;R2&z;R!2'40,51!3'61!3,71!2'8#7,9!3,71!2'8#73!3,71!2'8#74!3,71!2'8#75!3,71!2'8#76!3,71!2'8#778!3'61!4';+<1!1'=#6!2'>,9}P!3'61!3,71#5!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#48!3'61!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#1!3,71#38#2").

Lemma relayV_len : forall vals R x38 x48 x70 ext, length (relayV vals R x38 x48 x70 ext) = (71 + length ext)%nat.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?+<!2'@}^J!2'A0#1").
Qed.
Lemma relayV_lo : forall vals R x38 x48 x70 ext j, (j < 6)%nat -> vals_ev (relayV vals R x38 x48 x70 ext) j = vals_ev vals j.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SX0!1+1!1,2|600;!1+00}6!2'B#12!1,E#1!2'B42!1,E#2}1!1,E4!2'B82!1,E6}2!1,E8!2'B<2!1,E:}3!1,E<!2'B@2!1,E>}4!1,E@!2'BD2!1,EB}5!1,EF!1'I#2!1,J,K!1,J|22;!2'G!2'H!2'H!2'H!2'H!2'H!2'HIJJJJJJK$x;R+M!2'H#1J!1MI!1MN!1MO!1MP!1MQ!1+W+M!2,^2+M,K!1,^4+Y!2,^0+MJ!1,E!1,E!1,E!1,E!1,E!1,E#5$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1$j;R+<$Hj;R3!1-<RN$n;R+<%Hj;R3!3+C0!2'8!6'D#:#9#8#7#6#5#2!2'8#:#2#22$Hj;R!2'B,92!2,?0!2'8#9,9$n;R+<!1$j;R+<$Hj;R5!1-<RN$n;R+<%Hj;R5!3+C0!2'8!6'D#=#<#;#:#9#86!2'8#=6#22$Hj;R!2'B72!2,?0!2'8#<7$n;R+<!1$j;R+<$Hj;R9!1-<RN$n;R+<%Hj;R9!3+C0!2'8!6'D#@#?#>#=#<#;:!2'8#@:#22$Hj;R!2'B;2!2,?0!2'8#?;$n;R+<!1$j;R+<$Hj;R=!1-<RN$n;R+<%Hj;R=!3+C0!2'8!6'D#C#B#A#@#?#>>!2'8#C>#22$Hj;R!2'B?2!2,?0!2'8#B?$n;R+<!1$j;R+<$Hj;RA!1-<RN$n;R+<%Hj;RA!3+C0!2'8!6'D#F#E#D#C#B#AB!2'8#FB#22$Hj;R!2'BC2!2,?0!2'8#EC$n;R+<!1$j;R+<$Hj;RE!1-<RN$n;R+<%Hj;RE!3+C0!2'8!6'D#I#H#G#F#E#DF!2'8#IF#22$Hj;R!2'BG2!2,?0!2'8#HG$n;R+<!1$j;R+<$Hj;R!2'B!1,ED2&Hj0;R!4'F!2'BH2L!<'L+<+M'B'I'G'NH!1MR!<'O+<+<+M+M,E'I'IM'PFR!<'O+<+<+M+M,E'I'IM'PBQ!<'O+<+<+M+M,E'I'IM'P>P!<'O+<+<+M+M,E'I'IM'P:O!<'O+<+<+M+M,E'I'IM'P6N!<'O+<+<+M+M,E'I'IM'P#2I!2,?+MI2K!2,?+MK#1L&cstr;R!1'Q#3!2'R,5!1'I#3&__arith;R$__p1;Rw$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,VS'X+Y+Y,Z!7,[S'X+Y+Y,Z!4,\+M!2,^0+M,5,^1T,^3U!8,VS'X+Y+Y,Z!7,[S'X+Y+Y,Z!4,\+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+MTVVVVVV,^6!2,^0+MK,^3U!6,^7S'X+Y+Y,Z#4!2'^8S,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p1;Rw%__x1;R+M%~R!2'R,5#1%~R!2'G!2'H!2'H!2'H!2'H!2'H!2'H#2JJJJJJK#4!4#1!3+C0!2'8!6'D#M#L#K#J#I#HW!2'8#MW!1'I#5#2#3#1#1#1#1#1#1#1#1#1#1#1#1").
Qed.
Lemma relayV_reg : forall vals R x38 x48 x70 ext i, (i < 32)%nat -> vals_ev (relayV vals R x38 x48 x70 ext) (6 + i) = gr R i.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`T0!1+1!1,2|600;!1+00}P!2'B#12}6!1,E#1!2'B52!1,E#2}1!1,E5!2'B92!1,E7}2!1,E9!2'B=2!1,E;}3!1,E=!2'BA2!1,E?}4!1,EA!2'BE2!1,EC}5!1,EE!2'BI2!1,EG!1,EI!2'BL2!1,EK}7!1,EL!2'BP2!1,EN}8!1,EP!2'BT2!1,ER}9!1,ET!2'BX2!1,EV}:!1,EX!2'B\2!1,EZ};!1,E\!2'B^32!1,E^1}<!1,E^3!2'B^72!1,E^5}=!1,E^7!2'B^;2!1,E^9}>!1,E^;!2'B^?2!1,E^=}?!1,E^?!2'B^C2!1,E^A}@!1,E^C!2'B^G2!1,E^E}A!1,E^G!2'B^K2!1,E^I}B!1,E^K!2'B^O2!1,E^M}C!1,E^O!2'B^S2!1,E^Q}D!1,E^S!2'B^W2!1,E^U}E!1,E^W!2'B^[2!1,E^Y}F!1,E^[!2'B_22!1,E_0}G!1,E_2!2'B_62!1,E_4}H!1,E_6!2'B_:2!1,E_8}I!1,E_:!2'B_>2!1,E_<}J!1,E_>!2'B_B2!1,E_@}K!1,E_B!2'B_F2!1,E_D}L!1,E_F!2'B_J2!1,E_H}M!1,E_J!2'B_N2!1,E_L}N!1,E_N!2'B_R2!1,E_P}O!1,E_T!1'I#2!1,J,K|500;!1,J_Y!2'G!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H_W_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_Z$x;R+M!2'H#1_X!1_\_W!1_\`0!1_\`1!1_\`2!1_\`3!1_\`4!1_\`5!1_\`6!1_\`7!1_\`8!1_\`9!1_\`:!1_\`;!1_\`<!1_\`=!1_\`>!1_\`?!1_\`@!1_\`A!1_\`B!1_\`C!1_\`D!1_\`E!1_\`F!1_\`G!1_\`H!1_\`I!1_\`J!1_\`K!1_\`L!1_\`M!1+W+M!2,^2+M,K!1,^4+Y!2,^0+M_X!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E!1,E#5$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1$i;R+<$Hi;R3!1-<RN$n;R+<%Hi;R3!3+C0!2'8!6'D#:#9#8#7#6#5!2'@4#2!2'=#9#2#22$Hi;R!2'B,92!2,?0!2'=#8,9$n;R+<!1$i;R+<$Hi;R6!1-<RN$n;R+<%Hi;R6!3+C0!2'8!6'D#=#<#;#:#9#8!2'@47!2'=#<7#22$Hi;R!2'B82!2,?0!2'=#;8$n;R+<!1$i;R+<$Hi;R:!1-<RN$n;R+<%Hi;R:!3+C0!2'8!6'D#@#?#>#=#<#;!2'@4;!2'=#?;#22$Hi;R!2'B<2!2,?0!2'=#><$n;R+<!1$i;R+<$Hi;R>!1-<RN$n;R+<%Hi;R>!3+C0!2'8!6'D#C#B#A#@#?#>!2'@4?!2'=#B?#22$Hi;R!2'B@2!2,?0!2'=#A@$n;R+<!1$i;R+<$Hi;RB!1-<RN$n;R+<%Hi;RB!3+C0!2'8!6'D#F#E#D#C#B#A!2'@4C!2'=#EC#22$Hi;R!2'BD2!2,?0!2'=#DD$n;R+<!1$i;R+<$Hi;RF!1-<RN$n;R+<%Hi;RF!3+C0!2'8!6'D#I#H#G#F#E#D!2'@4G!2'=#HG#22$Hi;R!2'BH2!2,?0!2'=#GH$n;R+<!1$i;R+<$Hi;RJ!1-<RN$n;R+<%Hi;RJ!3+C0!2'8!6'D#L#K#J#I#H#G!2'@4K!2'=#KK#22$Hi;R!2'B42!2,?0!2'=#J4$n;R+<!1$i;R+<$Hi;RM!1-<RN$n;R+<%Hi;RM!3+C0!2'8!6'D#O#N#M#L#K#J!2'@4N!2'=#NN#22$Hi;R!2'BO2!2,?0!2'=#MO$n;R+<!1$i;R+<$Hi;RQ!1-<RN$n;R+<%Hi;RQ!3+C0!2'8!6'D#R#Q#P#O#N#M!2'@4R!2'=#QR#22$Hi;R!2'BS2!2,?0!2'=#PS$n;R+<!1$i;R+<$Hi;RU!1-<RN$n;R+<%Hi;RU!3+C0!2'8!6'D#U#T#S#R#Q#P!2'@4V!2'=#TV#22$Hi;R!2'BW2!2,?0!2'=#SW$n;R+<!1$i;R+<$Hi;RY!1-<RN$n;R+<%Hi;RY!3+C0!2'8!6'D#X#W#V#U#T#S!2'@4Z!2'=#WZ#22$Hi;R!2'B[2!2,?0!2'=#V[$n;R+<!1$i;R+<$Hi;R^0!1-<RN$n;R+<%Hi;R^0!3+C0!2'8!6'D#[#Z#Y#X#W#V!2'@4^1!2'=#Z^1#22$Hi;R!2'B^22!2,?0!2'=#Y^2$n;R+<!1$i;R+<$Hi;R^4!1-<RN$n;R+<%Hi;R^4!3+C0!2'8!6'D#^1#^0#\#[#Z#Y!2'@4^5!2'=#^0^5#22$Hi;R!2'B^62!2,?0!2'=#\^6$n;R+<!1$i;R+<$Hi;R^8!1-<RN$n;R+<%Hi;R^8!3+C0!2'8!6'D#^4#^3#^2#^1#^0#\!2'@4^9!2'=#^3^9#22$Hi;R!2'B^:2!2,?0!2'=#^2^:$n;R+<!1$i;R+<$Hi;R^<!1-<RN$n;R+<%Hi;R^<!3+C0!2'8!6'D#^7#^6#^5#^4#^3#^2!2'@4^=!2'=#^6^=#22$Hi;R!2'B^>2!2,?0!2'=#^5^>$n;R+<!1$i;R+<$Hi;R^@!1-<RN$n;R+<%Hi;R^@!3+C0!2'8!6'D#^:#^9#^8#^7#^6#^5!2'@4^A!2'=#^9^A#22$Hi;R!2'B^B2!2,?0!2'=#^8^B$n;R+<!1$i;R+<$Hi;R^D!1-<RN$n;R+<%Hi;R^D!3+C0!2'8!6'D#^=#^<#^;#^:#^9#^8!2'@4^E!2'=#^<^E#22$Hi;R!2'B^F2!2,?0!2'=#^;^F$n;R+<!1$i;R+<$Hi;R^H!1-<RN$n;R+<%Hi;R^H!3+C0!2'8!6'D#^@#^?#^>#^=#^<#^;!2'@4^I!2'=#^?^I#22$Hi;R!2'B^J2!2,?0!2'=#^>^J$n;R+<!1$i;R+<$Hi;R^L!1-<RN$n;R+<%Hi;R^L!3+C0!2'8!6'D#^C#^B#^A#^@#^?#^>!2'@4^M!2'=#^B^M#22$Hi;R!2'B^N2!2,?0!2'=#^A^N$n;R+<!1$i;R+<$Hi;R^P!1-<RN$n;R+<%Hi;R^P!3+C0!2'8!6'D#^F#^E#^D#^C#^B#^A!2'@4^Q!2'=#^E^Q#22$Hi;R!2'B^R2!2,?0!2'=#^D^R$n;R+<!1$i;R+<$Hi;R^T!1-<RN$n;R+<%Hi;R^T!3+C0!2'8!6'D#^I#^H#^G#^F#^E#^D!2'@4^U!2'=#^H^U#22$Hi;R!2'B^V2!2,?0!2'=#^G^V$n;R+<!1$i;R+<$Hi;R^X!1-<RN$n;R+<%Hi;R^X!3+C0!2'8!6'D#^L#^K#^J#^I#^H#^G!2'@4^Y!2'=#^K^Y#22$Hi;R!2'B^Z2!2,?0!2'=#^J^Z$n;R+<!1$i;R+<$Hi;R^\!1-<RN$n;R+<%Hi;R^\!3+C0!2'8!6'D#^O#^N#^M#^L#^K#^J!2'@4_0!2'=#^N_0#22$Hi;R!2'B_12!2,?0!2'=#^M_1$n;R+<!1$i;R+<$Hi;R_3!1-<RN$n;R+<%Hi;R_3!3+C0!2'8!6'D#^R#^Q#^P#^O#^N#^M!2'@4_4!2'=#^Q_4#22$Hi;R!2'B_52!2,?0!2'=#^P_5$n;R+<!1$i;R+<$Hi;R_7!1-<RN$n;R+<%Hi;R_7!3+C0!2'8!6'D#^U#^T#^S#^R#^Q#^P!2'@4_8!2'=#^T_8#22$Hi;R!2'B_92!2,?0!2'=#^S_9$n;R+<!1$i;R+<$Hi;R_;!1-<RN$n;R+<%Hi;R_;!3+C0!2'8!6'D#^X#^W#^V#^U#^T#^S!2'@4_<!2'=#^W_<#22$Hi;R!2'B_=2!2,?0!2'=#^V_=$n;R+<!1$i;R+<$Hi;R_?!1-<RN$n;R+<%Hi;R_?!3+C0!2'8!6'D#^[#^Z#^Y#^X#^W#^V!2'@4_@!2'=#^Z_@#22$Hi;R!2'B_A2!2,?0!2'=#^Y_A$n;R+<!1$i;R+<$Hi;R_C!1-<RN$n;R+<%Hi;R_C!3+C0!2'8!6'D#_1#_0#^\#^[#^Z#^Y!2'@4_D!2'=#_0_D#22$Hi;R!2'B_E2!2,?0!2'=#^\_E$n;R+<!1$i;R+<$Hi;R_G!1-<RN$n;R+<%Hi;R_G!3+C0!2'8!6'D#_4#_3#_2#_1#_0#^\!2'@4_H!2'=#_3_H#22$Hi;R!2'B_I2!2,?0!2'=#_2_I$n;R+<!1$i;R+<$Hi;R_K!1-<RN$n;R+<%Hi;R_K!3+C0!2'8!6'D#_7#_6#_5#_4#_3#_2!2'@4_L!2'=#_6_L#22$Hi;R!2'B_M2!2,?0!2'=#_5_M$n;R+<!1$i;R+<$Hi;R_O!1-<RN$n;R+<%Hi;R_O!3+C0!2'8!6'D#_:#_9#_8#_7#_6#_5!2'@4_P!2'=#_9_P#22$Hi;R!2'B_Q2!2,?0!2'=#_8_Q$n;R+<!1$i;R+<$Hi;R_S!1-<RN$n;R+<%Hi;R_S!3+C0!2'8!6'D#_=#_<#_;#_:#_9#_8!2'@4_T!2'=#_<_T#22$Hi;R!2'B_U2!2,?0!2'=#_;_U$n;R+<!1$i;R+<$Hi;R!2'B!1,E_R2&Hi0;R!4'F!2'B_V2_[!<'L+<+M'B'I'G'N_V!1_\`N!<'O+<+<+M+M,E'I'I_\'P_T`N!<'O+<+<+M+M,E'I'I_\'P_P`M!<'O+<+<+M+M,E'I'I_\'P_L`L!<'O+<+<+M+M,E'I'I_\'P_H`K!<'O+<+<+M+M,E'I'I_\'P_D`J!<'O+<+<+M+M,E'I'I_\'P_@`I!<'O+<+<+M+M,E'I'I_\'P_<`H!<'O+<+<+M+M,E'I'I_\'P_8`G!<'O+<+<+M+M,E'I'I_\'P_4`F!<'O+<+<+M+M,E'I'I_\'P_0`E!<'O+<+<+M+M,E'I'I_\'P^Y`D!<'O+<+<+M+M,E'I'I_\'P^U`C!<'O+<+<+M+M,E'I'I_\'P^Q`B!<'O+<+<+M+M,E'I'I_\'P^M`A!<'O+<+<+M+M,E'I'I_\'P^I`@!<'O+<+<+M+M,E'I'I_\'P^E`?!<'O+<+<+M+M,E'I'I_\'P^A`>!<'O+<+<+M+M,E'I'I_\'P^=`=!<'O+<+<+M+M,E'I'I_\'P^9`<!<'O+<+<+M+M,E'I'I_\'P^5`;!<'O+<+<+M+M,E'I'I_\'P^1`:!<'O+<+<+M+M,E'I'I_\'PZ`9!<'O+<+<+M+M,E'I'I_\'PV`8!<'O+<+<+M+M,E'I'I_\'PR`7!<'O+<+<+M+M,E'I'I_\'PN`6!<'O+<+<+M+M,E'I'I_\'PK`5!<'O+<+<+M+M,E'I'I_\'PG`4!<'O+<+<+M+M,E'I'I_\'PC`3!<'O+<+<+M+M,E'I'I_\'P?`2!<'O+<+<+M+M,E'I'I_\'P;`1!<'O+<+<+M+M,E'I'I_\'P7`0!<'O+<+<+M+M,E'I'I_\'P#2_W!2,?+M_W2_Z!2,?+M_Z#1_[&cstr;R!1'Q#3!2'R,5!1'I#3&__arith;R$__p1;Rw$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,V`O'X+Y+Y,Z!7,[`O'X+Y+Y,Z!4,\+M!2,^0+M,5,^1`P,^3`Q!8,V`O'X+Y+Y,Z!7,[`O'X+Y+Y,Z!4,\+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M!3,^5+M`P`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R`R,^6!2,^0+M_Z,^3`Q!6,^7`O'X+Y+Y,Z#4!2'^8`O,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p1;Rw%__x1;R+M%~R!2'R,5#1%~R!2'G!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H!2'H#2_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_X_Z#4!4#1!3+C0!2'8!6'D#_A#_@#_?#_>#_=#_<!2'@4`S!2'=#_@`S!1'I#5#2#3#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1").
Qed.
Lemma relayV_38 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 38 = x38. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#4").
Qed.
Lemma relayV_48 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 48 = x48. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#3").
Qed.
Lemma relayV_70 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 70 = x70. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#2").
Qed.
Lemma relayV_71 : forall vals R x38 x48 x70 w ext, vals_ev (relayV vals R x38 x48 x70 (w :: ext)) 71 = w. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$w;R0$ext;R1!2,?0#2").
Qed.

(* [comment removed for export] *)
Lemma relayV_agree : forall a0s path hw rdraw fdata vals R x38 x48 x70 ext,
  env_agree 6 (ENV a0s path hw rdraw fdata vals) (ENV a0s path hw rdraw fdata (relayV vals R x38 x48 x70 ext)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90|30;!1+0!1+1!1,20!1+1!1,2|600;!1+02!2'B#1}6!6'D#8#7#6#5#4#3!3+C2!2'^@!6'^A#=#<#;#:#9#8#2!2'^@!6'^A#=#<#;#:#95#2%~R+<1!1'^B!6'^A#;#:#9#8#7!6'D#6#5#4#3#2#1$a0s;R1$path;R1$hw;R2$rdraw;R+^>$fdata;R1$vals;R3$R;R!2'3!1,2|21;2$x38;R2$x48;R2$x70;R2$ext;R3!4,^?%n;R+<%~R46!3+C7!1'^B!6'^A#;#:#9#8#7#68$n;R+<$Hn;R4vd!4'^C2!2'85#2!2'8#8#2!8'^D#8#7#6#5#4#3#2#16!2,?78").
Qed.

(* [comment removed for export] *)
Lemma relay_know6 : forall a0s path hw rdraw fdata vals R x38 x48 x70 ext M kn kn6,
  know_ok RSEGS (ENV a0s path hw rdraw fdata vals) M kn -> ksubl_b kn kn6 = true -> kn_vars_lt 6 kn6 = true ->
  know_ok RSEGS (ENV a0s path hw rdraw fdata (relayV vals R x38 x48 x70 ext)) M kn6.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80|30;!1+1!1,20!1+01!1+1!1,2|600;!1+03!1+0+^F}6!6'^A#A#@#?#>#=#<$a0s;R2$path;R2$hw;R3$rdraw;R+^>$fdata;R2$vals;R4$R;R!2'3!1,2|21;3$x38;R3$x48;R3$x70;R3$ext;R4$M;R%~R3!1+^E1$kn;R5$kn6;R5$HK;R!4'^G'^H!6'^A#>#=#<#;#:#9#3#2$Hsub;R!3+C+^:!2'^I#3#2,^;$Hv;R!3+C+^:!2'^J6#3,^;!9'^K'^H67!6'^A#A#@#?#>#=!6'D#<#;#:#9#8#7#6#4!;'^L#A#@#?#>#=#<#;#:#9#8#7#1!7'^M'^H7#6#5#4#3#2").
Qed.

(* [comment removed for export] *)
Lemma knLP_split : knLP = kn_blk 48 65536 ++ knLP6. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2,?!1+0+^F!3'6+^F!2'^N}^3!1,J|@0000;'^O").
Qed.
Lemma knLP6_vars : kn_vars_lt 6 knLP6 = true. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,?+^:,^;!3+C+^:!2'^J}6'^O,^;").
Qed.
Lemma knRD_split : knRD = cellR :: kn_blk 48 65536 ++ knLP6. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2,?!1+0+^F!3,7+^F'^P!3'6+^F!2'^N}^3!1,J|@0000;'^O").
Qed.
Lemma knRe0_split : knRe0 = KRange (EVar 72) 1 65536 :: cellR :: kn_blk 48 65536 ++ knLP6. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1,J|@0000;}^3!2,?!1+0+^F!3,7+^F!3,^Q!1,^R}^K!1,J,K0!3,7+^F'^P!3'6+^F!2'^N10'^O").
Qed.
Lemma knGbase_sub : ksubl_b (kn_blk 48 65536 ++ knLP6 ++ [cellC]) knGbase = true. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,?+^:,^;!3+C+^:!2'^I!3'6+^F!2'^N}^3!1,J|@0000;!3'6+^F'^O!3,7+^F'^S!1,:+^F'^T,^;").
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod_of_decompZ : forall a b q r : Z, (0 < b)%Z -> (0 <= r < b)%Z -> (a = b * q + r)%Z -> (a mod b = r)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>0!2'R,5#2!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^2+M,K|10;!2,^2+M7!7,^[5'X+Y+Y,Z!7,[5'X+Y+Y,Z!4,\+M!2,^0+M,5,^16,^3!7,[5'X+Y+Y,Z!4,\+M6,^68,^3!1,^4+Y!2'^85,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!7,[5'X+Y+Y,Z!4,\+M6,_6!3,^5+M!3,_7+M8!2,^2+M|11;!2,^2+M|20;,^3$a;R+M$b;R+M$q;R+M$r;R+M$Hb;R!2'G,5#3$Hr;R!2+^U0!2'G#2#4$He;R!3+C+M#6!2'H!2'^V#5#4#3!4'^C+M#4!2'^W#7#6!6'^X#7#6#5#4&__arith;R$__x2;R+M$__x1;R+M&__wit;R12&__varmap;R!4,^Y+M!2,T+M#3#234&__ff;R!8,V5'X+Y+Y,Z9:9;<%__x2;R+M%__x1;R+M%~R!2+^U!2'R,5#1!2'G#1#2!2+^U0!2'G#2#3!3#1#7#5#3&__arith;R$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M!3,_1+M!2,_2+M!1,_3,K!2,_4+M}1!2,_4+M,9,_512&__varmap;R!4,^Y+M!4,^Y+M!2,T+M#5#33#2!2,T+M#44&__ff;R!8,V5'X+Y+Y,Z=:=;<%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!3+C+M#1!2'H!2'^V#2#3#4!3+C+M#2!2'H!2'^V#3#4#5!5#1#5#6#7#8#2").
Qed.

(* [comment removed for export] *)
Lemma sub_as_add : forall c l : Z, (0 <= l <= c)%Z -> (c < 2 ^ 64)%Z ->
  alu64 ALU_ADD (Z_to_bv 64 c) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 l)) = Z_to_bv 64 (c - l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_70!2'R,5#1|10;!1,J1|600;!1,J3!2'_824!2'G#35!1+1#1!1+1#2%~R!3+C!1+1#3#2#1!3+C+M!2'_;#4#3!2'_;#4#2%~R!3+C+M!2'_;#3#2!2'_;#3#1!3+C!1+1#4#3#2!1,23!2'4;#5!1,_3,K!2'4;=!2'4;#4!4'_?;,_@>?!3'_=,_><@!2'_A#5#4!2'4;B!1+1;!2'_C<@!2'_A#6#5!2'_;;!2'4;F!2'_;;>!2'_;;?!2'^W!2'^VHI5!2'_;;<!2'HKJ!2'_D;#5!2'_D;=!2'_D;#6!2'_D;#4!2'_D;!2'HO!2'^W!2'^VN#15!2'_D;B!2'_D;F!2'^W=5!1,J,K!2'_A5U!3+C+M#5,5!3+C+M#6,5!1'_HX!3+C+M#7,5!2'^W#15!2'^W,55!2'^W#:5!2'_A5#8!2'_A#:#9!2'^W^25!2'_A#9#8!2'_M24!2'G,55%~R!2'G,52%~R!2'R,54^6!2'R,52$Ha;R^8$~R+_N!3'_O24#2%Ha;R^8%~R+_N!2'R,55!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^0+M,5!3,_P+M!2,^0+M2;!2'^8^?,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2&__sat1;R^5^7&__sat0;R^9^:&__arith;R&__wit;R^;^<&__varmap;R^=^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M^@,^6^A,^3^B^C^6#1}3!2,_4+M^E!2,_4+M,9!4,^Y+M!2,T+M#3#2^=!2,^2+M1!1,^4+Y!2,^2+M,K!7,[^?'X+Y+Y,Z!4,\+M^K,^6^A,^3!7,^[^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1^I,^3!7,[^?'X+Y+Y,Z!4,\+M^I,^1^K,^3!3,_R+M^K^I!2'G#25!2'_A#4#5&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M!2,_4+M}4!3,_0+M^F^G,_5^;^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z!6,_Q^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^I,_6^@,^3^J!8,V^?'X+Y+Y,Z^L^J!8,V^?'X+Y+Y,Z^M^J!7,^[^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1^N,^3!7,[^?'X+Y+Y,Z!4,\+M^N,^6^A,^3^B^C%__x2;R+M%__x1;R+M%~R%~R!3+C+M#2,5+_S%~R^O%~R!2+^U!2'R,5#4!2'R#4#3!2+^U!2'R,5^P!2'G^P5!5#1#;#<#4#9#:!2'_A#1#2!2#1#;#<!2'H#9^1!2,^0+MU!2'^VV#8}1!3,_0+M!2,_4+M^W^G!3,7+S!2,^\!3,_0+M^F^X,_5^;!7,[^?'X+Y+Y,Z!4,\+M^I,^6^A,^3!7,[^?'X+Y+Y,Z!4,\+M^@,^1^K,^3!7,^[^?'X+Y+Y,Z^[!7,[^?'X+Y+Y,Z!4,\+M^K,^1^I,^3!3,_R+M^A^K!2'R,5#3!2'_A5#4}2!7,^[^?'X+Y+Y,Z^[^L!2+^U_16!2'_;;C$c;R+M$l;R+M$Hl;R!2+^U0!2'R#1#2$Hc;R6&H;R$n;R+_9$b1;R7$b2;R8!5'_:9:%~R!3+C+M!2'_;#3#2!2'_;#3#1!3+C!1+1#4#3#2$~R9$~R%~R!3+C+M!2'_;#4#3!2'_;#4#2!3+C!1+1#5#4#3#1!3'_<#3#2#1%n;R+_9%b1;R7%b2;R8:!4#1;AC!6'_BDE$b;RD!3+C+M!2'_;;#1Gvd!6'_B+MJ$z;R+M!3+C+M!2'_;;!2'4;!2'H!2'_;;!2'4;#6#1G!6'_B+M!2'_D;L$z;R+M!3+C+M#1G!6'_B+MM$z;R+M!3+C+M!2'_D;!2'H#1!2'^W!2'^VHK5G!6'_B+MN$z;R+M!3+C+M!2'_D;!2'HO!2'^W!2'^V#1K5G!6'_B+MP$z;R+M!3+C+MQG!6'_B+MR$z;R+M!3+C+M!2'_D;!2'HO!2'^W!2'^VNM5#1!6'_B+M#4$z;R+M!3+C+MQS!6'_B+M#5$z;R+M!3+C+M!2'_D;!2'H#1!2'^W!2'^VN#55Svd&H;R!2,?+MT!3+C+MVT!6'_E+MV$z;R+M!3+C+M!2'^W!2'H#7!2'^W!2'^V#1#655!2'^W!2'_A#7#65&s;R!2'_F#5,5!2+_GW!1'_HW-_GRN$s;R!2+_GXY!3+C+M!2'^W!2'H#8!2'^W!2'^VV#755!2'^W!2'_A#8#75#12$e;RX!1$e;RZ!7'_B+M,5$l;R+M%Hl;R!2+^U0!2'R#1#:!3+C+M!2'^W!2'H#;!2'^W!2'^VV#255!2'^W!2'_A#;#25$Hl;R!2+^U!2'R,5,5!2'R,5#9!6'_B+M,5$z;R+M!3+C+M!2'^W!2'H#;[5!2'^W!2'_A#;,55!6'_B+M#:$z;R+M!3+C+M!2'^W!2'H#;\5[vd!6'_B+M#:$z;R+M!3+C+M[!2'^W#;5!2,?+M^0!2'H#:,5!1'_I#:!3+C+M!2'^W!2'H#:\5^0!2'_A#:,5!1'_J#:!2'^VV,5!1'_KV#8#1#7#1$n;RY!1$Hnz;R!1'_HZ!6'_B+M^1$z;R+M!3+C+M!2'^W!2'H#:#15^3!6'_B+M^4$z;R+M!3+C+M#1^3!6'_B+M^4$z;R+M!3+C+M^2#1!2,?+M^4!2'^W^45!7'_L^45,5^4^D^Q&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^;^<&__varmap;R^H^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M^N,_6!3,^5+M!3,_7+M^A^@^N,^3^B^C%__x2;R+M%__x1;R+M!3+C+M^R!2'H!2'^V5,5^R^S!2'^W^T5!7'_L^T5U^4^D^Q&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^;^<&__varmap;R^H^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M!3,^5+M^K!3,_R+M^A^I,_6!3,^5+M!3,_7+M^A^U^N,^3^B^C%__x2;R+M%__x1;R+M!3+C+M!2'H#1!2'_A5#2!2'H!2'^V5U^R^S!2'^W^V5!7'_L^V5!2'_A#8U^1^D&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^Y^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z!6,_Q^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^K,_6^@,^3^J!8,V^?'X+Y+Y,Z^Z^J!8,V^?'X+Y+Y,Z^\^J!7,^[^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1_0,^3!7,[^?'X+Y+Y,Z!4,\+M_0,^6^A,^3^B^C%__x2;R+M%__x1;R+M%~R%~R!3+C+M#1,5+_S%~R6%~R!2+^U_1!2'R#3#4!2+^U!2'R,5_2!2'G_25!5#1#<#;#4#9#:&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x1;R+M&__wit;R^;^<&__varmap;R!2,T+M#2^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M!3,_7+M!3,_R+M^A^U^K,_6!3,^5+M!3,_7+M^A!3,_R+M^K^U_0,^3^B^C%__x1;R+M!3+C+M!2'^VV#1!2'H!2'^V5!2'_A#1U!2'_A5#1!1#1#;#1T#1!3+C+M!2'_D;!2'H#5!2'^W!2'^VN#45RM!3'_T;#5&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M!2,_4+M_3^X,_5^;^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z^L^J!8,V^?'X+Y+Y,Z^M^J_4^B^C%__x2;R+M%__x1;R+M%~R!2'G#15%~R!2+^U_1!2'R#3#2_5!4#1#7#8#5#6P!3'_T;#4&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^Y^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z^Z^J!8,V^?'X+Y+Y,Z^\^J_4^B^C%__x2;R+M%__x1;R+M%~R^O%~R!2+^U!2'R,5#2!2'R#2#3_5!4#1#8#7#5#6_6!2'_U;BI!2'_U;#4H!2'_U;=K!2'_U;#5!2'_;;!2'4;L!2'_U;L!2'_;;@!2'_V>?!3+C+M!2'_;;E_6A!2'_W<@").
Qed.

(* [comment removed for export] *)
Lemma mul2_lit : forall c : Z, (0 <= c)%Z -> (2 * c < 2 ^ 64)%Z ->
  mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 c) = Z_to_bv 64 (2 * c).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^30|10;!1,J0|600;!1,J2!2'_813!1+1#1!1+1#2%~R!3+C!1+1#3#2#1!3+C+M!2'_;#4#3!2'_;#4#2%~R!3+C+M!2'_;#3#2!2'_;#3#1!3+C!1+1#4#3#2!1,22!2'491!2'49#4!4'_?9,_@:;!2'^V1#4!2'49=!2'_;9:!2'_;9;!2'^V1#5!2'_;9!2'49A!2'^V1#1!2'_M13%~R!2'G,51%~R!2'R,53!2'G,54!2'R,51$Ha;RF$~R+_N!3'_O13#2%Ha;RF%~R+_N!2'R,54!2,_4+M,9!2,_4+M}2!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^0+M1!2,^2+M,K!3,_7+MPQ!3,_P+MP9!7,[O'X+Y+Y,Z!4,\+MR,^6S,^3!1,^4+Y!2,^0+M,5!7,[O'X+Y+Y,Z!4,\+MV,^1Q,^3!2'^8O,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'GC4!2'R,5#2!2'^V1#3!3#1#7#5#6&__sat3;RDE&__sat2;RGH&__arith;R$__x1;R+M&__wit;R!3,7+S!2,_YI!2,^\!3,_0+MIJ,_5KL&__varmap;RMN&__ff;R!8,VO'X+Y+Y,ZTU!8,VO'X+Y+Y,ZWU!7,^[O'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MV,^1R,^3TXY%__x1;R+M%~RZ%~R[!2+^U!2'R,5\!2'G\4^0}1$c;R+M$H0;R!2'R,5#1$H1;R!2'G!2'^V1#24&H;R$n;R+_9$b1;R5$b2;R6!5'_:78%~R!3+C+M!2'_;#3#2!2'_;#3#1!3+C!1+1#4#3#2$~R7$~R%~R!3+C+M!2'_;#4#3!2'_;#4#2!3+C!1+1#5#4#3#1!3'_<#3#2#1%n;R+_9%b1;R5%b2;R68!4#19<>!6'_B+M!2'^W!2'^V?@4$z;R+M!3+C+M#1B!6'_B+M1$z;R+M!3+C+M!2'^W!2'^V#1!2'_;9!2'49#54B!6'_B+M#4$z;R+M!3+C+M!2'^WC4B!6'_B+M=$z;R+M!3+C+M!2'^WA4#1!6'_B+M=$z;R+M!3+C+M#1A!2,?+M=!2'^W=4!3'_X=4^1!2'_;9>!2'_Z=^1@!2'_Z#4&__sat3;RDE&__sat2;RGH&__arith;R$__x1;R+M&__wit;R!3,7+S!2,_YJ!2,^\!3,_0+MI!2,_4+M^2,_5KL&__varmap;RMN&__ff;R!8,VO'X+Y+Y,ZTU!8,VO'X+Y+Y,ZWU!7,^[O'X+Y+Y,ZW!7,[O'X+Y+Y,Z!4,\+MQ,^6S,^3XY%__x1;R+M%~RZ%~R[!2+^U!2'R,5#3!2'G#34^0?!2'_Z1&__sat3;RDE&__sat2;RGH&__arith;R&__wit;RKL&__varmap;R!1,^Z+MN&__ff;R!7,^[O'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MV,^1P,^3!7,[O'X+Y+Y,Z!4,\+MP,^6S,^3XY!2+^UF!2'G14#1!2'_;9<!2'_V:;").
Qed.

Lemma firstn_app_skipn : forall {A} (l : list A) (a b : nat),
  firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;5lcd;g_[d;lcd;g6d;lcd;g_Bd;lcd;g_\d;<scd;%l;R!1+0#4%b;R+<!3+C!1+0#6!3'6#6!3'_\#6#3#2!3'_\#6#1!3'`1#6#3#2!3'_\#6!2'@#3#1#2!1+0#5!1+0#8!1,E#5!1+0#7!1,:#7!1,E#4!1+0#;!3'_\#;!2'@#8#5#1!1,E#8!3,7#;#2#1$A;R{cd;$l;R!1+0#1$a;R+<!5'`0$a;R+<0$l;R!1+0#3$b;R+<!2,?1!3'_\#5!2'@,9#1#2$a;R+<$IH;R0$l;R1$b;R+<-0RN$l;R!1+0#7!3+C2!3'6#8!3'_\#83#1!3'_\#8#2!3'`1#83#1!3'_\#8!2'@3#2#1#22vd!6'_B45$l;R4!3+C2#1!1,:#8!2,?45!3'_\#7#15!2'_[#7#1!3+C4!3'6#7!3'_\#765!3'_\#7#1!3'`1#765!3'_\#7!2'@6#15$a;R#7$l;R!1+0#8!2$x;R#9$l;R!1+0#:vd!6'_B78$l;R7!3+C!1+0#<!3,7#<#3#1!3,7#<#3!3'_\#<!2'@#9#6#2!2,?7!3,7#;#28!3'6#;!3'_\#;#8#1!3'_\#;#5!3'`1#;#8#1!2#7#1#5!3+C7!3'6#;!3'_\#;9:!3'_\#;#5!3'`1#;9:!3'_\#;!2'@9#5:#2#1#1#2").
Qed.

Lemma file_read_lit : forall data (off cnt : Z), (0 <= off < 2 ^ 64)%Z -> (0 <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0|30;!1+1!1,20!1+01|10;!1,J3|600;!1,J5!2'_846!2+^U!2'R,5#2!2'G#27!1,25!2'49#3!1'`2:!2'49#4!1'`2<!1'`3#4!3'_\1>!3'`11!1'`3#5#6!1'`3#3!2'_M46%~R!2'G,54%~R!2'R,56!2'G,57!2'R,54$Ha;RC$~R+_N!3'_O46#2%Ha;RC%~R+_N!2'R,57!1+W+M!2,^2+M,K!7,^[F'X+Y+Y,Z!7,[F'X+Y+Y,Z!4,\+M!2,^0+M,5,^1G,^3!7,[F'X+Y+Y,Z!4,\+MG,^6!3,_P+M!2,^0+M49,^3$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,VF'X+Y+Y,ZH!1,^4+YH!2'^8F,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__x1;R+M%~R!2+^U!2'R,5#1!2'G#178$data;R2$off;R+M$cnt;R+M$~R8$~R8!6'_B2!3'_\1;!3'`11=#5$l;R2!3+C2#1?!6'_B+<@$n;R+<!3+C2!3'_\1#1!3'`11!1'`2!2'49#5#6?!6'_B+<>$n;R+<!3+C2!3'_\1>!3'`11#1#6?!2,?2!3'_\1@!3'`11>#5=!2'`4#4&__sat2;RAB&__sat1;RDE&__arith;RIJ!2#1#7#5;!2'`4#3&__sat2;RAB&__sat1;RDE&__arith;RIJ!2#1#6#4!3'`5#5<:!3'`6#5<:").
Qed.

Lemma length_read : forall (data : list byte) (off cnt : Z), (0 <= off)%Z -> (off <= Z.of_nat (length data))%Z -> (0 <= cnt)%Z ->
  Z.of_nat (length (firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data))) = Z.min cnt (Z.of_nat (length data) - off).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_R0|30;!1+1!1,20!1'`3#4!1'`3#5!3'`113#6!2'A14!1'I#1!2'_A!1'I!2'A1#7#6!2'`8#57!2'A1#6!2'`993!2'`72:!1'I;!1'I9!2'`8#4!2'_A=#5!2'`;,5#4!2'`;,5#5!2'`;,5!2'_A=@!2'`8?A!1+C+M$x;R+M#1$x;R+M!2'`;,5#1!2'`;,5#8!2'_A!1'I!2'A1#;#1!2'`;,5G!2'`;,5#;!2'`8#1#3!2,_2+M!1,_3,K}=!2,_4+ML!3,_1+MKM}:!2,_4+MO}9!2,_4+MQ!3,_1+MKR}7!2,_4+MT}5!2,_4+MV}1!2,_4+MX!2,_4+M,9!3,_0+MW!3,_0+MYZ!3,_0+MS!3,_0+MU[!2,^\!3,_0+MN!3,_0+MP\,_5}8!2,_4+M^1!3,_1+MKW}4!2,^\!3,_0+MM!3,_0+MR!3,_0+M^2!3,_0+M^3!3,_0+M!2,_4+M^4Z,_5}3!3,_0+M^3!3,_0+M!2,_4+M^6Z!2,^\!3,_0+MM!3,_0+MR^7,_5}6!2,_4+M^9!3,_0+MS!3,_0+MU!3,_0+M^:[!2,^\!3,_0+MN!3,_0+MP^;,_5}<!2,_4+M^=!3,_1+MK^>!3,_1+MK^2!3,_0+MWZ!3,_0+M^:^A!3,_0+M^@!3,_0+MU^B!2,^\!3,_0+M^?!3,_0+MR^C,_5!2,^\!3,_0+M^>!3,_0+M^2^7,_5}2!2,^\!3,_0+M^>!3,_0+M^2!3,_0+M^3!3,_0+M!2,_4+M^FZ,_5!3,_0+M^@!3,_0+MU^A!2,^\!3,_0+M^?!3,_0+MR^H,_5};!2,_4+M^J!3,_1+MKU!3,_0+M^L^:!2,^\!3,_0+M^K!3,_0+MR^M,_5!2,^\!3,_0+MM!3,_0+MP!3,_0+MR^@,_5!2,_4+M}>!2,^\!3,_0+M^P!3,_0+M^K!3,_0+MPS,_5!3,_0+M^3Z!3,_0+M^2!3,_0+M^L^R!3,_0+MM!3,_0+MR^S!3,_0+MM!3,_0+M^K^R!3,_0+M^>!3,_0+MP^R!3,_1+MK^K!3,_0+M^WR!2,^\!3,_0+M^P!3,_0+M^>^X,_5!2,^\!3,_0+M^>!3,_0+MP!3,_0+MU!3,_0+M^:Y,_5!2,^\!3,_0+M^K!3,_0+MR!3,_0+MU^:,_5!3,_1+MKP!3,_0+M^\^2!2,^\!3,_0+MM!3,_0+M^K_0,_5!2,^\!3,_0+MM!3,_0+M^\!3,_0+M^2^M,_5!3,_0+M^\^A!3,_0+M^W^A!2,^\!3,_0+M^P^T,_5!3,_0+M^W^B!2,^\!3,_0+MN!3,_0+M^>_6,_5!2,^\!3,_0+MM!3,_0+M^K^7,_5!2,^\!3,_0+MN!3,_0+M^>_4,_5!2,^\!3,_0+M^?!3,_0+M^K_3,_5!2,^\!3,_0+M^>!3,_0+MP^7,_5!1+W+M!2,^2+M0!2,^2+M|23;!2,^2+M,K!1,^4+Y!2,^0+M,5!2,^2+M|21;|20;!2,^2+M_C!2,^2+M|22;!3,_R+M_D_E|11;!2,^2+M_G!3,_R+M_D_H|10;!2,^2+M_J!3+C+M#9#6!3+C+M#9,5!2+^U!2'R#6,5_M!2'_A#6#8!2'_A#8#7!2'R,5#;$data;R!1+01$off;R+M$cnt;R+M$~R!2'R,5#2$~R!2'R#3!1'I!2'A1#4$~R!2'R,5#3!6'_B+<!2'`725$n;R+<!3+C+M68!6'_B+<:$n;R+<!3+C+M!1'I!2'`73#18!4'`:!3+C+M<>!3+C+MB>!<'L+M+MCDC$x;R+M$y;R+M!1'`<!3+C+M#2#1<B!<'O+<+M+M+M'I'IDD$x;R+<!2,?+M6;B!B'`=+<+<+<+M+M+M'`>'I'I'I'`8'`?2?!<'O+M+<+M+M'`3D'IE'`@#4#4!2,?+M#4:A!B'`=+<+<+<+M+M+M'`A'I'I'I$n;R+M$m;R+M!2'`;,5!2'_A#2#1'`B9=!2,?+M=3@!<'O+M+<+M+M'`3D'IE'`@#5#5!2,?+M#5>>!2,?+M>&cstr;R!1'Q9!2'R,5=&H2;R!2'`C#57!2+`D!2+^U!2'G#57!3+C+M8#5!2+^U!2'R7#5!3+C+M87&z2;R!2'`8#6!2'_A!1'I!2'A1#8#7+M&H3;R!2'`E,5#8!2+`D!2+^U!2'G,5#8!3+C+MF#8!2+^U!2'R#8,5!3+C+MF,5&z3;R!2'`;,5#9+M&H4;R!2'`E,5G!2+`D!2+^U!2'G,5G!3+C+MHG!2+^U!2'RG,5!3+C+MH,5&z4;R!2'`;,5!2'_A!1'I!2'A1#<#2+M&H5;R!2'`E,5#;!2+`D!2+^U!2'G,5#;!3+C+MI#;!2+^U!2'R#;,5!3+C+MI,5&z5;R!2'`;,5#<+M&H6;R!2'`C#1#3!2+`D!2+^U!2'G#1#3!3+C+MJ#1!2+^U!2'R#3#1!3+C+MJ#3&z6;R!2'`8#2#4+M&__arith;R$__p1;Rw$__x8;R+M$__x7;R+M$__x6;R+M$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S^0!3,7+S^5!3,7+S^8!3,7+S^<!3,7+S^D!3,7+S^E!3,7+S^G!3,7+S^I!3,7+S^N!3,7+S^N!3,7+S^O!3,7+S^O!3,7+S^Q!3,7+S^Q!3,7+S^Q!3,7+S^Q!3,7+S!2,^\!3,_0+MN\,_5!3,7+S!2,^\^T,_5!3,7+S!2,^\!3,_0+M^P^U,_5!3,7+S!2,^\!3,_0+MN^;,_5!3,7+S!2,^\!3,_0+M^?^C,_5!3,7+S!2,^\!3,_0+MM^V,_5!3,7+S!2,^\!3,_0+M^>^S,_5!3,7+S!2,^\!3,_0+M^?^H,_5!3,7+S^I!3,7+S^G!3,7+S^E!3,7+S^D!3,7+S^<!3,7+S^8!3,7+S^5!3,7+S^0!3,7+S^Y!3,7+S^Y!3,7+S^Z!3,7+S^Z!3,7+S^[!3,7+S^[!3,7+S_1!3,7+S_1!3,7+S_2!3,7+S_2!3,7+S!2,^\^V,_5!3,7+S!2,^\!3,_0+M^?_3,_5!3,7+S!2,^\!3,_0+MN_4,_5!3,7+S!2,^\^U,_5!3,7+S_5!3,7+S!2,^\!3,_0+MN_6,_5!3,7+S_7!3,7+S_5!3,7+S_8!3,7+S_9!3,7+S_:!3,7+S_;!3,7+S^N!3,7+S^N!3,7+S!2,^\!3,_0+M^?!3,_0+M^K!3,_0+M^\^B,_5!3,7+S!2,^\!3,_0+MM_0,_5!3,7+S_;!3,7+S_:!3,7+S_9!3,7+S_8!3,7+S!2,^\!3,_0+M^P^X,_5!3,7+S_7!1,:+S!1+0+S&__varmap;R!4,^Y+M!4,^Y+M!4,^Y+M!2,T+M#9#5!1,^Z+M#3!2,T+M#7#2!4,^Y+M!2,T+M#6#4!2,T+M#8!1+U+M&__ff;R!8,V_<'X+Y+Y,Z!7,`F_<'X+Y+Y,Z!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_=,^6_>,^3!7,[_<'X+Y+Y,Z!4,\+M_?,_6_=,^3!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_>,^1_=,^3!7,[_<'X+Y+Y,Z!4,\+M_?,_6_>,^3_@!8,V_<'X+Y+Y,Z!7,`F_<'X+Y+Y,Z!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^6_B,^3!7,[_<'X+Y+Y,Z!4,\+M_=,_6_B,^3!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_B,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_=,_6_A,^3_@!8,V_<'X+Y+Y,Z!7,`F_<'X+Y+Y,Z!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^6_F,^3!7,[_<'X+Y+Y,Z!4,\+M_>,_6_F,^3!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_F,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_>,_6_A,^3_@!8,V_<'X+Y+Y,Z!7,`F_<'X+Y+Y,Z!7,^[_<'X+Y+Y,Z!6,^7_<'X+Y+Y,Z#;!7,[_<'X+Y+Y,Z!4,\+M_E,_6_H,^3!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_H,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_E,_6_A,^3_@!8,V_<'X+Y+Y,Z!7,`F_<'X+Y+Y,Z!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_B,^6_I,^3!7,[_<'X+Y+Y,Z!4,\+M_K,_6_B,^3!7,^[_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_I,^1_B,^3!7,[_<'X+Y+Y,Z!4,\+M_K,_6_I,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_D,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_B,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_H,^1_D,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_H,^3_@!7,[_<'X+Y+Y,Z!4,\+M_?,_6_K,^3!2'^8_<,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p1;Rw%__x8;R+M%__x7;R+M%__x6;R+M%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+`D!2+^U!2'G#8#7!3+C+M#1#8!2+^U!2'R#7#8!3+C+M#1#7%~R!2+`D!2+^U!2'G,5#6_L_N%~R!2+`D!2+^U!2'G,5_O!3+C+M#9_O!2+^U!2'R_O,5_M%~R!2+`D!2+^U#<_L_N%~R!2+`D!2+^U!2'G#9_P!3+C+M#6#9!2+^U!2'R_P#9!3+C+M#6_P%~R!2'R,5#9%~R_Q%~R!2'R#:#;%~R_Q!3+C+M#:#;!B#1!2'G,5#A#4#6#8#@!1'I!2'A1#B#A#:#2#3#5#7#9#;#<#=#>#?5!3'`G13#6!2'A1!3'_\124!3'`H124").
Qed.

Lemma lb_remove_2 : forall A2 n2 A n, A2 <> A -> lb_remove A [(A2, n2); (A, n)] = [(A2, n2)].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S:0!2'`I#5#3%~R!3+C+^:!2'`I#2#1,`J!1'_H!3+C+M#3#2%~R!1'_H!3+C+M#2#1!3+C+^:!2'`I#3#2,`J!2+`L+M+M!1+03!4,`M+M+M#5#4!1,:3!3,7356!4,`M+M+M#7#6!3,7386$A2;R+M$n2;R+M$A;R+M$n;R+M$H;R!1'_H!3+C+M#4#2vd&H0;R!4'^C+^:0,`J&H0;R$x;R+M$y;R+M!5'_:12%~R!1'_H!3+C+M#2#1!3+C+^:!2'`I#3#2,`J$~R1$~R%~R!1'_H!3+C+M#3#2!3+C+^:!2'`I#4#3,`J#1!2'`K#2#1%x;R+M%y;R+M2!3#1#6#4#2!3+C+^:,`J0!6'_E+^:,`J$b;R+^:!3+C4-^:RN$~R+^:4#127!3,738-^:RN$~R+^:4!2'`I#5#52679!6'_B+^:,^;$b;R+^:!3+C4!3,738-^:RN$~R+^:4#12679!2,?4!3,73!4,`M+M+M#6#56!2'`I#4#4!1'`N#4!2'`I#6#4#1!3+C4!2'`O#3!3,735!3,73!4,`M+M+M#3#267").
Qed.

Lemma keep_rd_Re0 : keep_rd knRe0 = knRe0. Proof. vmc_refl. Qed.
Lemma keep_stage_RD : keep_stage [(48%nat, 65536%Z)] knRD = knRD. Proof. vmc_refl. Qed.

(* [comment removed for export] *)
Fixpoint kbytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kread RSEGS kn b k 1, kbytes kn b (k + 1) n' with
            | Some (ELit z), Some r => Some (z :: r)
            | _, _ => None
            end
  end.
Definition zbytes (zs : list Z) : list byte := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10|30;$zs;R!1+0+M!4'a0+M!1+1!1,20$z;R+M!2'a1}1!2'4!1,2|600;#1#1").

Lemma msg_refused_k : kbytes knRa (EVar 0) (-560) 38 = Some (map bv_unsigned msg_refused) /\ zbytes (map bv_unsigned msg_refused) = msg_refused
                      /\ length msg_refused = 38%nat.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^70!1+0+M!1+^E0!1,J|623;!1,J|62c;!1,J|629;|51a;!1,J5!1,J|500;!1,J|62e;!1,J|630;!1,J|635;!1,J|634;!1,J|51e;!1,J|51d;|516;!1,J>|517;!1,J@|511;!1,JB!1,J|510;|518;!1,JE|514;!1,JG!1,J|622;!1,J|639;!1,J|625;!1,J|633;!1,J|50c;!1,J|632;!1,J|626;!1,J|624;!1,J|32;!2,a20!3,7+M2!3,7+M3!3,7+M4!3,7+M6!3,7+M7!3,7+M4!3,7+M8!3,7+M9!3,7+M:!3,7+M;!3,7+M7!3,7+M<!3,7+M=!3,7+M7!3,7+M?!3,7+MA!3,7+MC!3,7+MD!3,7+MF!3,7+MF!3,7+M?!3,7+MH!3,7+M7!3,7+MI!3,7+MJ!3,7+M;!3,7+MK!3,7+ML!3,7+MM!3,7+M7!3,7+MN!3,7+MK!3,7+MO!3,7+M:!3,7+ML!3,7+MK!3,7+MP!3,7+MQ!1,:+M|30;!1,2S!1+1T!1+0U!3,a3T4!2'a4T4!3,a3T7!2'a4T7!3,a3T:!2'a4T:!3,a3T;!2'a4T;!3,a3T?!2'a4T?!3,a3TF!2'a4TF!3,a3TK!2'a4TK!3,a3TL!2'a4TL!3,7U!3,a3T2!2'a4T2!3,7U!3,a3T3!2'a4T3!3,7UW!3,7U!3,a3T6!2'a4T6!3,7UX!3,7UW!3,7U!3,a3T8!2'a4T8!3,7U!3,a3T9!2'a4T9!3,7UY!3,7UZ!3,7UX!3,7U!3,a3T<!2'a4T<!3,7U!3,a3T=!2'a4T=!3,7UX!3,7U[!3,7U!3,a3TA!2'a4TA!3,7U!3,a3TC!2'a4TC!3,7U!3,a3TD!2'a4TD!3,7U\!3,7U\!3,7U[!3,7U!3,a3TH!2'a4TH!3,7UX!3,7U!3,a3TI!2'a4TI!3,7U!3,a3TJ!2'a4TJ!3,7UZ!3,7U^0!3,7U^1!3,7U!3,a3TM!2'a4TM!3,7UX!3,7U!3,a3TN!2'a4TN!3,7U^0!3,7U!3,a3TO!2'a4TO!3,7UY!3,7U^1!3,7U^0!3,7U!3,a3TP!2'a4TP!3,7U!3,a3TQ!2'a4TQ!1,:U!3+CV^2^2}V!3+C+<^4^4!4';U+M!1'_;T'a7vv!4,^?!3+C1RR!2+^U^3^5!2,?1R!4,^?^3^5!2,?V^2!2,?+<^4!2+^U!3+C1!4'a5'a6!1,^R,9!1,_3|9030;^4!2,a20^6!2+^U!3+CV!1'a8^6'a7!3+C+<!2'AU'a7^4").
Qed.

Section DrvG.
  Context {RE : RunEnv}. Context {RO : ReaderOn}.
  Local Open Scope Z_scope.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable VM0 : VmMaps.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis DL : drv_layout L sp0.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let LEN : Z := Z.of_nat (length fdata).
  Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
  Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
  Let model1o (off : Z) (VM : VmMaps) : Model := model1o path tid fs0 stdin0 off VM.
  Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.

  (* [comment removed for export] *)
  Definition hdr_vals (vals : list word) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 a0s path envv rdraw inp /\ vals_ev vals 2 = p1 a0s path envv rdraw inp /\
    vals_ev vals 3 = auxvp sp0 a0s path envv /\ vals_ev vals 4 = rnd sp0 a0s path envv inp /\ vals_ev vals 5 = tid.

  Lemma hdr_relay : forall vals R x38 x48 x70 ext, hdr_vals vals -> hdr_vals (relayV vals R x38 x48 x70 ext).
  Proof. intros vals R x38 x48 x70 ext H. unfold hdr_vals. rewrite !relayV_lo by lia. exact H. Qed.

  Lemma hiv_facts' : forall vals, hdr_vals vals ->
    forall i, In i [3%nat; 4%nat] -> (bv_unsigned sp0 <= bv_unsigned (vals_ev vals i))%Z /\ (bv_unsigned (vals_ev vals i) + 2 ^ 20 <= 2 ^ 64)%Z.
  (* same Pm6DrvA prefix as Pm6DrvB.v:145 and Pm6DrvH.v:199:
     [sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME Hplen] *)
  Proof.
    intros vals (_ & _ & _ & P3 & P4 & _) i Hi.
    exact (hiv_facts sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME Hplen vals P3 P4 i Hi).
  Qed.

  Definition CAPk (k : Z) : Z := 65536 * 2 ^ k.
  Variables Kc Bc : Z.
  Hypothesis HKc : 0 <= Kc. Hypothesis HBc : 0 <= Bc.
  Definition cred (k : Z) (cr : credit) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'_A!1,J|32;#2|10;!1,J1$k;R+M$cr;R'aC!2+^U!2'R!2'H!2'^V0!1'aD/L;/Kc;!3'aE+M+M#1!2'R!2'H!2'H!2'_A!2'_82!1,J|4b;!2'^V2!1'aF#2!2'^V0!1'aG/L;/Bc;!3'aH+M+M#1").

  Lemma CAPk_S : forall k, 0 <= k -> CAPk (k + 1) = 2 * CAPk k.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^80!2'R,5#1|10;!1,J1!1,J,K!2'_823!1,J|@0000;!2'^V5#1!2'_82#3!2'^V2!2'^V57|30;!1+1!1,29!2'A:/fdata;!1'I;!3+C+M/LEN;<vd!2,?+M<=!2'A:/path;}`m0!1'I?!1,J|;7ff;!2'RAB!4'F!2+a>?@C!<'L+<+M+a>'I'R'a??A!2,?+MA@B!2,?+MB/Hplen;!1'Q?!2'R,5A!1'Q;!2'R,5<!1,J|46;!2'_M2I!2'G,52!2'_82I%~RK%~R!2'R,5I!2'G,5L!2'R,52$Ha;RN$~R+_N!3'_O2I#2%Ha;RN%~R+_N!2'R,5L|600;!2'_;!1,2Q/sp0;|40;!1,JS!2'a@RT%~R!2'R,5R%~R!2'R,5T!2'R,5!2'^WRT!2'_82#<!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^0+M5!2,^2+M,K!2,^0+M2!2'^8\,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'H#23!2,^0+M,5!7,[\'X+Y+Y,Z!4,\+M^6,^1^1,^3$k;R+M$Hk;R0vd!6'_B+M!2'^V!2'_82#24$z;R+M!3+C+M68!6'_B+M2$z;R+M!3+C+M!2'^V5!2'^V7#18&heq_LEN;R>=&Hplen0;RDC&cstr;REF&cstr0;RGH&__sat7;RJM&__sat6;ROP&__sat5;RUV&__sat4;R!2'_M2#9%~RK%~R!2'R,5#:!2'G,5!2'_82#;&__sat3;R$Ha;RN$~R+_N!3'_O2#<#2%Ha;RN%~R+_N!2'R,5W&__arith;R$__x1;R+M&__wit;RXY&__varmap;RZ[&__ff;R!7,[\'X+Y+Y,Z!4,\+M!3,_7+M^0!3,_7+M^1^2,_6!3,_7+M^2!3,_7+M^0^1,^3^3^4%__x1;R+M!3+C+M!2'^V5!2'^V#12!2'^V26!1#1W4!1'aI2!2'_82^5!5'aJ2#23&heq_LEN;R>=&Hplen0;RDC&cstr;REF&cstr0;RGH&__sat5;RJM&__sat4;ROP&__sat3;RUV&__arith;R$__x1;R+M&__wit;RXY&__varmap;RZ[&__ff;R!8,V\'X+Y+Y,Z^7!1,^4+Y^7^3^4%__x1;R+M%~R0!2'R,5#2!2#1#:#9&heq_LEN;R>=&Hplen0;RDC&cstr;REF&cstr0;RGH&__sat5;RJM&__sat4;ROP&__sat3;RUV&__arith;R&__wit;RXY&__varmap;R!1,^Z+M[&__ff;R!7,[\'X+Y+Y,Z!4,\+M^6,^1!2,^0+M3,^3^3^4!2'R,53#1!3+C+M!1'aF^5!2'^V2!1'aF#2").
Qed.
  Lemma CAPk_range : forall k, 0 <= k <= 10 -> 65536 <= CAPk k <= 67108864.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^W0!1,J|32;!2'R#10|@0000;!1,J2|10;!1,J4!2'_85#2!2'^V36|J0000000;!1,J8!2'G,55!2'R,5#3!2'_85,5|30;!1+1!1,2=!2'A>/fdata;!1'I?!3+C+M/LEN;@vd!2,?+M@A!2'A>/path;}`m0!1'IC|;7ff;!1,JF!2'REG!4'F!2+a>CDH!<'L+<+M+a>'I'R'a?CE!2,?+MEDG!2,?+MG/Hplen;!1'QC!2'R,5E!1'Q?!2'R,5@!2'R,55!1,J|46;!2'_M5O!2'_85O%~R:%~R!2'R,5O!2'G,5Q$Ha;RN$~R+_N!3'_O5O#2%Ha;RN%~R+_N!2'R,5Q|600;!2'_;!1,2U/sp0;|40;!1,JW!2'a@VX%~R!2'R,5V%~R!2'R,5X!2'R,5!2'^WVX!2'_85#?!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^0+M,5!2,^0+M5!7,[^3'X+Y+Y,Z!4,\+M^4,^6^5,^3!1,^4+Y|23;!7,[^3'X+Y+Y,Z!4,\+M^4,^1!2,^2+M^8,^3!2,^2+M,K!1,J,K!2'^8^3,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'_M5#:%~R:%~R!2'R,5#;!2'G,5!2'_85#<$Ha;RN$~R+_N!3'_O5#=#2!2'_85#=%Ha;RN%~R+_N!2'R,5^A!2,_4+M,9}4!3,7+S!2,_Y^C!2,^\!3,_0+M^C!2,_4+M^D,_5\!4,^Y+M^1#2!4,^Y+M^1#3!2,T+M#4!7,^[^3'X+Y+Y,Z^9!6,^7^3'X+Y+Y,Z#6!1,J|^13fff80000000;|11;!7,^[^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M!2,^0+M^H,^1!2,^2+M^I,^3!6,^7^3'X+Y+Y,Z#7!2,^0+M3!3,_7+M^K^:!2'R,5#4!2+^U^M#5!2+^U!2'R^H#4#7!2'^V3#4!2'RV!1,J|^2000000000000;!2'R#=0!7,[^3'X+Y+Y,Z!4,\+M^:,^1!2,^0+M0,^3|:000;!1,J^T!1'aF#2$k;R+M$Hk;R!2+^U!2'R,5#11vd!4,^?!2'R37!2'R79&H;R&H;R!3'aK5,5#2%~R:%~R;!2'R<!2'_85#4vd&heq_LEN;RBA&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat9;R!2'_M5,5%~R:%~R!2'R,5,5!2'G,5<&__sat8;R$Ha;RN$~R+_N!3'_O5,5#2%Ha;RN%~R+_N!2'R,5<&__sat7;RPR&__sat6;RST&__sat5;RYZ&__sat4;R!2'_M5#<%~R:%~R!2'R,5#=!2'G,5!2'_85#>&__sat3;R$Ha;RN$~R+_N!3'_O5#?#2%Ha;RN%~R+_N!2'R,5[&__arith;R$__p1;Rw$__x2;R+M$__x1;R+M&__wit;R\^0&__varmap;R!4,^Y+M^1#2!4,^Y+M^1#3!2,T+M#3^2&__ff;R!8,V^3'X+Y+Y,Z!8,V^3'X+Y+Y,Z^6^7!8,V^3'X+Y+Y,Z^9^7!7,[^3'X+Y+Y,Z!4,\+M!3,_P+M^5,aL,^1^:,^3^7!8,V^3'X+Y+Y,Z!7,^[^3'X+Y+Y,Z^9!6,^7^3'X+Y+Y,Z#5^7!7,[^3'X+Y+Y,Z!4,\+M!2,^0+M^;,^1^:,^3^<^=%__p1;Rw%__x2;R+M%__x1;R+M%~R%~R:%~R;!2'R<#3%~R!2+^U;#4!2'R^;#3!5#1!2'R#?0#?[#=#>!2'R^;!2'_85#3!2'R^;6&heq_LEN;RBA&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat7;RPR&__sat6;RST&__sat5;RYZ&__sat4;R^>^?&__sat3;R^@^B&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R^E^0&__varmap;R^F^2&__ff;R!8,V^3'X+Y+Y,Z!8,V^3'X+Y+Y,Z^6^7!8,V^3'X+Y+Y,Z^9^7!7,[^3'X+Y+Y,Z!4,\+M^4,^6^:,^3^7!8,V^3'X+Y+Y,Z^G^7!8,V^3'X+Y+Y,Z^J^7!7,[^3'X+Y+Y,Z!4,\+M^K,^1^L,^3^<^=%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R%~R:%~R^M!2'G,5#3%~R^N%~R^O!2'R3^P!8#1^Q^R#=V^A#3#</Hsp;&H;R!5'aK5#20&heq_LEN;RBA&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat5;RPR&__sat4;RST&__sat3;RYZ&__arith;R&__wit;R\^0&__varmap;R^1^2&__ff;R^6^<^=:#1&heq_LEN;RBA&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat5;RPR&__sat4;RST&__sat3;RYZ&__arith;R$__p1;Rw$__x1;R+M&__wit;R\^0&__varmap;R!2,T+M#2^2&__ff;R!8,V^3'X+Y+Y,Z!7,^[^3'X+Y+Y,Z!6,^7^3'X+Y+Y,Z#4^S^7^S^<^=%__p1;Rw%__x1;R+M%~R!2+^U#21!2'R#20!3#1!2'R,5#:#:#9!2'R6!2'_850&heq_LEN;RBA&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat7;RPR&__sat6;RST&__sat5;RYZ&__sat4;R^>^?&__sat3;R^@^B&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R^E^0&__varmap;R^F^2&__ff;R!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^:,^1!2,^0+M^U,^3^7!8,V^3'X+Y+Y,Z^G^7!8,V^3'X+Y+Y,Z^J^7!7,[^3'X+Y+Y,Z!4,\+M^L,^1!2,^0+M9,^3^<^=%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R#1^U%~R^N%~R^O!2'R^P9!8#1^Q^R#=V^A#;#</Hsp;!2+^U!2'R3^V!2'R^V9").
Qed.
  Lemma CAPk_lt10 : forall k, 0 <= k < 10 -> CAPk k <= 33554432.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^=0!1,J|32;!2'G#10|10;!1,J2!1,J|31;|30;!1+1!1,25!2'A6/fdata;!1'I7!3+C+M/LEN;8vd!2,?+M89!2'A6/path;}`m0!1'I;|;7ff;!1,J>!2'R=?!4'F!2+a>;<@!<'L+<+M+a>'I'R'a?;=!2,?+M=<?!2,?+M?/Hplen;!1'Q;!2'R,5=!1'Q7!2'R,58!1,J|46;!2'_M3F!2'G,53!2'_83F%~RH%~R!2'R,5F!2'G,5I!2'R,53$Ha;RK$~R+_N!3'_O3F#2%Ha;RK%~R+_N!2'R,5I|600;!2'_;!1,2N/sp0;|40;!1,JP!2'a@OQ%~R!2'R,5O%~R!2'R,5Q!2'R,5!2'^WOQ!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^0+M,5!2'^8X,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2,^2+M,K!1,^4+Y!2'_83#=!2,_4+M,9}4|9000;!1,J^4|23;!1,J|^13fff80000000;|11;|@0000;!1,J^9|I0000000;!1,J^;$k;R+M$Hk;R!2+^U!2'R,5#11vd&H;R!5'aK3#24&heq_LEN;R:9&Hplen0;RA@&cstr;RBC&cstr0;RDE&__sat5;RGJ&__sat4;RLM&__sat3;RRS&__arith;R&__wit;RTU&__varmap;RVW&__ff;R!7,[X'X+Y+Y,Z!4,\+MY,^6!2,^0+M3,^3Z[H#1&heq_LEN;R:9&Hplen0;RA@&cstr;RBC&cstr0;RDE&__sat5;RGJ&__sat4;RLM&__sat3;RRS&__arith;R$__p1;Rw$__x1;R+M&__wit;RTU&__varmap;R!2,T+M#2W&__ff;R!8,VX'X+Y+Y,Z!7,^[X'X+Y+Y,Z!6,^7X'X+Y+Y,Z#4!7,[X'X+Y+Y,Z!4,\+M\,^6!2,^0+M0,^3^0!7,[X'X+Y+Y,Z!4,\+M\,^1!2,^0+M4,^3Z[%__p1;Rw%__x1;R+M%~R!2+^U#21!2'R#24!3#1!2'R,5#:#:#9!2'R!2'_83#2!2'_834&heq_LEN;R:9&Hplen0;RA@&cstr;RBC&cstr0;RDE&__sat7;RGJ&__sat6;RLM&__sat5;RRS&__sat4;R!2'_M3#:%~RH%~R!2'R,5#;!2'G,5!2'_83#<&__sat3;R$Ha;RK$~R+_N!3'_O3#=#2%Ha;RK%~R+_N!2'R,5^1&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,_Y^2!2,^\!3,_0+M^2!2,_4+M^3,_5TU&__varmap;R!4,^Y+MV#2!4,^Y+MV#3!2,T+M#4W&__ff;R!8,VX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M\,^1!2,^0+M^5,^3^0!8,VX'X+Y+Y,Z!7,^[X'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+MY,^1!2,^2+M^6,^3!6,^7X'X+Y+Y,Z#6^0!8,VX'X+Y+Y,Z!7,^[X'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M!2,^0+M^7,^1!2,^2+M^8,^3!6,^7X'X+Y+Y,Z#7^0!7,[X'X+Y+Y,Z!4,\+M!3,_7+M!2,^0+M^:\,^1!2,^0+M^<,^3Z[%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R#1^5%~R!2+^U!2'R,5#4#5%~R!2+^U!2'R^7#4#7!2'R!2'^V^:#4^<!8#1!2'RO!1,J|^2000000000000;!2'G#=0#=O^1#;#</Hsp;!2'R!1'aF#2^<").
Qed.
  Lemma CAPk_10 : forall k, 0 <= k <= 10 -> CAPk k = 67108864 \/ k < 10.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SN0!1,J|32;!2+^U!2'R,5#1!2'R#10!3+C+M#20!3+C+M#30!1'_H3!1,J|J0000000;!3+C+M#40|30;!1+1!1,27!2'A8/fdata;!1'I9!3+C+M/LEN;:!2'A8/path;}`m0!1'I<!1,J|;7ff;!2'R>?|10;!1,JA!1,J|46;!2'_8BC!2'R,5B|600;!2'_;!1,2F/sp0;|40;!1,JH!1+W+M!2,^2+M,K!2,^0+M0!1,^4+Y$k;R+M$Hk;R1&s;R!2'_F#20!2+_G2!1'_H2-_GRN$s;R!2+_G34!2+`D!3+C+M!1'aF#45!2'G#40#12$e;R3!1$e;R6!7'_B+M0$k;R+M%Hk;R1!2+`D!3+C+M!1'aF#25!2'G#20$Hk;R!2+^U!2'R,50!2'R00!3,aM!3+C+M!1'aF05!2'G00!2,?+M5#5#1#4#1$n;R4!1$n;R!1'_H6!3,aN!3+C+M!1'aF#55!2'G#50&heq_LEN;Rvd!2,?+M:;;&Hplen0;R!4'F!2+a><=@!<'L+<+M+a>'I'R'a?<>!2,?+M>=?!2,?+M?/Hplen;@&cstr;R!1'Q<!2'R,5>&cstr0;R!1'Q9!2'R,5:&__sat5;R!2'_MBC%~R!2'G,5B%~R!2'R,5C!2'G,5D&__sat4;R$Ha;RE$~R+_N!3'_OBC#2%Ha;RE%~R+_N!2'R,5D&__sat3;R!2'a@GI%~R!2'R,5G%~R!2'R,5I!2'R,5!2'^WGI&__arith;R$__p1;Rw$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,VJ'X+Y+Y,Z!6,_QJ'X+Y+Y,Z!7,[J'X+Y+Y,Z!4,\+MK,_6L,^3M!8,VJ'X+Y+Y,Z!7,^[J'X+Y+Y,Z!6,^7J'X+Y+Y,Z#4!7,[J'X+Y+Y,Z!4,\+MK,^1L,^3M!7,[J'X+Y+Y,Z!4,\+MK,^6L,^3!2'^8J,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p1;Rw%__x1;R+M%~R%~R!3+C+M#10+_S%~R!2+^U#3!2'R#20!2'G#30!4#1!2'R,5#=#=#9#<#1").
Qed.

  (* [comment removed for export] *)
  Lemma heap_facts1 : forall A n cr M VM, hi_heap HI [(A, n)] cr M VM -> block_range L A n /\ defined M A n.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SO0|30;!2+`L+M+M!1,:1!3,71!4,`M+M+M#6#52!3,71!4,`M+M+M#7#62!3'aE+M+M#2!3'aH+M+M#2!3'aR/L;56!3,71!4,`M+M+M#8#72!2'aE+M+M%b;R1%~R!3'aA1#18!2+^U7!2+^U!3'aS#656!3'aT56!2'`O5!3,71!4,`M+M+M#9#82!3,71!4,`M+M+M#:#92!4,`M+M+M#;#:!3,71<2!3'aE+M+M<!3'aH+M+M<!4,`M+M+M#<#;!3'aE+M+M@!3'aH+M+M@!3'aR/L;AB!4,`M+M+M#>#=!4,`M+M+M#?#>!3'aE+M+ME!3'aH+M+ME!4,`M+M+M#@#?!3'aE+M+MH!3'aH+M+MH!3'aS#=IJ!4,`M+M+M#B#A!4,`M+M+M#C#B!3'aE+M+MM$A;R+M$n;R+M$cr;R'aC$M;R%~R!1+1!1,2|600;!1+^E!1+1!1,20$VM;R+aO$HH;R!5'aP/HI;!3,71!4,`M+M+M#5#42#3#2#1&a;R!9'aQ/L;/scfg;/HI;/HIok;3#4#3#2#1!2+^U%b;R1%~R!3'aA1#14!2+^U7!2+^U!3'aS#556!3'aT56!2'`O58!2+^U!2+aU+M!4';1+M93!2+^U!2'R,5!3'aE+M+M#4!2'R,5!3'aH+M+M#4!5'_::!2+^U!2+aU+M!4';1+M94!2+^U!2'R,5!3'aE+M+M#5!2'R,5!3'aH+M+M#5!2+^U!3'aR/L;#7#6!3'aS#4#7#6$~R:$~R!2+^U!2+aU+M!4';1+M9!3,71!4,`M+M+M#8#72!2+^U!2'R,5!3'aE+M+M#6!2'R,5!3'aH+M+M#6!2$WF;R%b;R1%~R!3'aA1#1;!2+^U7!2+^U!3'aS#856!3'aT56!2'`O5=$_H;R!2+^U!2+aU+M!4';1+M9;!2+^U!2'R,5!3'aE+M+M#8!2'R,5!3'aH+M+M#8&a;R!2#2<!3,aM!3+C1<<!3'aA1<2!2,?1<!2+^U!3'aR/L;>?!2+^U!3'aS#8>?!3'aT>?!2'`O>=!5'_:C!2+^U!3'aS#9AB!3'aTAB!2'`OA!3,71@2!2+^U!3'aR/L;#<#;!3'aS#9#<#;$~RC$~R!2+^U!3'aS#:!3'aE+M+M!4,`M+M+M#=#<!3'aH+M+M!4,`M+M+M#=#<!3'aT!3'aE+M+M!4,`M+M+M#=#<!3'aH+M+M!4,`M+M+M#=#<!2'`O!3'aE+M+M!4,`M+M+M#=#<!3,71!4,`M+M+M#=#<2!2$B;R!3'aR/L;!3'aE+M+MD!3'aH+M+MD$H;R!2+^U!3'aS#<FG!3'aTFG!2'`OF!3,71E2!5'_:K!3'aTIJ!2'`OI!3,71H2!2+^U!3'aR/L;#@#?!3'aS#=#@#?$~RK$~R!3'aT!3'aE+M+M!4,`M+M+M#A#@!3'aH+M+M!4,`M+M+M#A#@!2'`O!3'aE+M+M!4,`M+M+M#A#@!3,71!4,`M+M+M#A#@2!2$D;R!3'aS#?!3'aE+M+ML!3'aH+M+ML$_H;R!3'aTN!3'aH+M+MM!2'`ON!3,71M2!4,^?!3'aR/L;#D#C!3'aS#A#D#C#6#2#2#1#1#2#1#1#2#1#1").
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable K : TSet.
  Hypothesis HK0 : K [].

  (* [comment removed for export] *)
  Definition close_kg (CAP : Z) (crC : credit) (KC : TSet) : Prop :=
    forall vals R M VM (A1 : Z),
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
      vals_ev vals 1 = p0 a0s path envv rdraw inp -> vals_ev vals 2 = p1 a0s path envv rdraw inp ->
      vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv inp -> vals_ev vals 5 = tid ->
      regs_ok (ENVb vals) srGL R ->
      (forall lo hi, (lo <= LEN <= hi)%Z -> know_ok RSEGS (ENVb vals) M (knG lo hi)) ->
      above M -> block_range L A1 CAP ->
      rdn RSEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      hi_heap HI [(A1, CAP)] crC M VM ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbb608) M (seg_rom RSEGS)) (model2 VM)) KC.

  Definition lp_at (z : Z) : Prop := forall (k len A : Z) vals R M VM cr,
      0 <= k <= 10 -> 0 <= len <= CAPk k -> len <= LEN -> LEN - len <= z ->
      length vals = 71%nat -> hdr_vals vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 len ->
      regs_ok (ENVb vals) srLP R -> know_ok RSEGS (ENVb vals) M knLP ->
      above M -> rdn RSEGS M (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      hi_heap HI [(A, CAPk k)] cr M VM -> cred k cr ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x39978) M (seg_rom RSEGS)) (model1o len VM)) K.

  (* [comment removed for export] *)
  Definition rd_at (z : Z) : Prop := forall (k len want A : Z) vals R M VM cr,
      0 <= k <= 10 -> 0 <= len < CAPk k -> len <= LEN -> LEN - len <= z ->
      want = Z.min (CAPk k - len) 65536 ->
      length vals = 72%nat -> hdr_vals vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 len ->
      vals_ev vals 71 = Z_to_bv 64 want ->
      regs_ok (ENVb vals) srRD R -> know_ok RSEGS (ENVb vals) M knRD ->
      above M -> rdn RSEGS M (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      hi_heap HI [(A, CAPk k)] cr M VM -> cred k cr ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbb604) M (seg_rom RSEGS)) (model1o len VM)) K.

  (* [comment removed for export] *)
  Definition refuse_k (KR : TSet) : Prop := forall (A : Z) vals R M VM cr,
      length vals = 71%nat -> hdr_vals vals ->
      vals_ev vals 38 = Z_to_bv 64 67108864 -> vals_ev vals 48 = Z_to_bv 64 A -> vals_ev vals 70 = Z_to_bv 64 67108864 ->
      regs_ok (ENVb vals) srLP R -> know_ok RSEGS (ENVb vals) M knLP ->
      above M -> hi_heap HI [(A, 67108864)] cr M VM ->
      srealizes RSEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x39978) M (seg_rom RSEGS)) (model1o 67108864 VM)) KR.
  Definition refuse_at : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'aV/K;").

  (* [comment removed for export] *)
  Hypothesis HKC : LEN < 67108864 -> forall CAP crC,
      65536 <= CAP <= 67108864 -> LEN < CAP -> Kc <= fst crC -> Bc <= snd crC -> close_kg CAP crC K.
  Hypothesis HREF : 67108864 <= LEN -> refuse_at.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
                      let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
  Ltac norm_nth := repeat match goal with |- context [nth ?i ?l (ELit 0)] =>
                      let x := eval vm_compute in (nth i l (ELit 0)) in change (nth i l (ELit 0)) with x end.
  (* [comment removed for export] *)
  Ltac relay1 HR :=
    norm_nth;
    first [ lia
          | reflexivity
          | rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV]; reflexivity
          | idtac ].
  Ltac relay_loop HR i :=
    first [ lia | let j := fresh "i" in destruct i as [|j]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; relay1 HR | relay_loop HR j ] ].
  Ltac relay_regs HR := apply regs_ok_by_nth; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; relay_loop HR i.
  Ltac relay2 HR :=
    rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV];
    rewrite ?relayV_38, ?relayV_48, ?relayV_70, ?relayV_71; unfold gr;
    rewrite ?(reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV].
  (* [comment removed for export] *)
  Ltac regv1 HR := rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVb ENV].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sc_eq_70_38 : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap ->
    0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> Z.eqb len cap = t ->
    sc_denot RSEGS M (ENVb vals) (SCBr t BC_EQ (EVar 70) (EVar 38)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^70|600;!1,20!1+11|30;!1+1!1,23}^I!2'41#3}V|10;!1,J8!1,J0!2'_89:!2+^U!2'R,5#5!2'G#5;!2'41#8!2'41#7!2'_;1=!2'A4/fdata;!1'I@!3+C+M/LEN;Avd!2,?+MAB!2'A4/path;}`m0!1'ID!1,J|;7ff;!2'RFG!4'F!2+a>DEH!<'L+<+M+a>'I'R'a?DF!2,?+MFEG!2,?+MG/Hplen;!1'QD!2'R,5F!1'Q@!2'R,5A!2'_M9:!2'G,59%~RO%~R!2'R,5:!2'G,5;!2'R,59$Ha;RQ$~R+_N!3'_O9:#2%Ha;RQ%~R+_N!2'R,5;!1,J|46;!2'_M9T!2'_89T%~RO%~R!2'R,5T!2'G,5V$Ha;RQ$~R+_N!3'_O9T#2%Ha;RQ%~R+_N!2'R,5V!2'_;1/sp0;|40;!1,J[!2'a@Z\%~R!2'R,5Z%~R!2'R,5\!2'R,5!2'^WZ\!1+W+M!2,^2+M,K!7,^[^2'X+Y+Y,Z!7,[^2'X+Y+Y,Z!4,\+M!2,^0+M,5,^1^3,^3!7,[^2'X+Y+Y,Z!4,\+M^3,^6!3,_P+M!2,^0+M91,^3$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,V^2'X+Y+Y,Z^4!1,^4+Y^4!2'^8^2,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__x1;R+M%~R!2+^U!2'R,5#1!2'G#1;!2+^U!2'R,5#2!2'G#2;$vals;R!1+02$M;R%~R2!1+^E4$len;R+M$cap;R+M$t;R+^:$P70;R!3+C2!2'8#556$P38;R!3+C2!2'8#676$Hl;R<$Hc;R<$Ht;R!3+C+^:!2'`I#7#6#5vd!6'_B2=$b;R2!3+C+^:!3'aW1#1!2'8#;7#7!6'_B2>$b;R2!3+C+^:!3'aW1!2'41#9#1#7vd!6'_B+M#8$z;R+M!3+C+^:!2'`I#1?#7!6'_B+M#7$z;R+M!3+C+^:!2'`I#9#1#7#1!2'_;1>!2'_Z#7&heq_LEN;RCB&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat75;RNP&__sat74;RRS&__sat73;RUW&__sat72;RXY&__sat71;R^0^1&__arith;R^5^6!2#1#A#<?!2'_Z#8&heq_LEN;RCB&Hplen0;RIH&cstr;RJK&cstr0;RLM&__sat75;RNP&__sat74;RRS&__sat73;RUW&__sat72;RXY&__sat71;R^0^1&__arith;R^5^6!2#1#B#=!3+C+^:!3'aW1=>#6!2'8#:7#4!2'8#:5#5!4'aX'^H#9!1/ENVb;#:!4,aY#6,aZ!1,^R5!1,^R7").
Qed.

  Lemma want_x_val : forall vals (len cap : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    edenot (ENVb vals) want_x = Z_to_bv 64 (cap - len).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^:0|600;!1,20!1+11}^I!2'41#2}V|10;!1,J6!1,J0!2'_878!2'41!1,_3,K!2'41!2'_A#6#7|30;!1+1!1,2<!2'A=/fdata;!1'I>!3+C+M/LEN;?vd!2,?+M?@!2'A=/path;}`m0!1'IB!1,J|;7ff;!2'RDE!4'F!2+a>BCF!<'L+<+M+a>'I'R'a?BD!2,?+MDCE!2,?+ME/Hplen;!1'QB!2'R,5D!1'Q>!2'R,5?!2'_M78!2'G,57%~RM%~R!2'R,58!2'G,59!2'R,57$Ha;RO$~R+_N!3'_O78#2%Ha;RO%~R+_N!2'R,59!1,J|46;!2'_M7R!2'_87R%~RM%~R!2'R,5R!2'G,5T$Ha;RO$~R+_N!3'_O7R#2%Ha;RO%~R+_N!2'R,5T!2'_;1/sp0;|40;!1,JY!2'a@XZ%~R!2'R,5X%~R!2'R,5Z!2'R,5!2'^WXZ!1,:+S!1+0+S!1+U+M!1+W+M!2,^2+M,K!7,^[^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M!2,^0+M,5,^1^4,^3!7,[^3'X+Y+Y,Z!4,\+M^4,^1!2,^2+M6,^3!1,^4+Y!2'^8^3,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!7,[^3'X+Y+Y,Z!4,\+M^4,^6!3,_P+M!2,^0+M71,^3$vals;R!1+02$len;R+M$cap;R+M$P70;R!3+C2!2'8#334$P38;R!3+C2!2'8#454$H1;R!2+^U!2'R,5#4!2'R#4#3$H2;R!2'G#49vd!6'_B2!2'41#6$b;R2!3+C2!3'_=,_>!2'8#85!4'_?1,_@:#1;!6'_B2!2'41#5$b;R2!3+C2!3'_=,_>#1!4'_?1,_@:!2'41#7;!4'a[#5#6&heq_LEN;RA@&Hplen0;RGF&cstr;RHI&cstr0;RJK&__sat75;RLN&__sat74;RPQ&__sat73;RSU&__sat72;RVW&__sat71;R[\&__arith;R$__x2;R+M$__x1;R+M&__wit;R^0^1&__varmap;R!4,^Y+M!2,T+M#3#2!1,^Z+M^2&__ff;R!8,V^3'X+Y+Y,Z^5^6^5^7^8%__x2;R+M%__x1;R+M%~R!2+^U!2'R,5#1!2'R#1#2!2+^U!2'R,5#2!2'R#2#3!3#1#?#@#<&heq_LEN;RA@&Hplen0;RGF&cstr;RHI&cstr0;RJK&__sat75;RLN&__sat74;RPQ&__sat73;RSU&__sat72;RVW&__sat71;R[\&__arith;R$__x1;R+M&__wit;R^0^1&__varmap;R!2,T+M#2^2&__ff;R!8,V^3'X+Y+Y,Z^9^6^9^7^8%__x1;R+M%~R!2'G#19!2'G#29!2#1#?#;!2'8#75#3!2'8#73#4!3+C2!2'a\!1/ENVb;#7'b0!2'41!2'_A#5#6").
Qed.

  Lemma sc_ltu_want : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    Z.ltb (cap - len) 65536 = t ->
    sc_denot RSEGS M (ENVb vals) (SCBr t BC_LTU want_x (ELit 65536)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^J0|600;!1,20!1+11|30;!1+1!1,23}^I!2'41#3}V|10;!1,J8!1,J0!2'_89:|@0000;!1,J<!2'_A#7#8!2'41>!1,`R=!2'41=!2'_;1A!2'A4/fdata;!1'IC!3+C+M/LEN;Dvd!2,?+MDE!2'A4/path;}`m0!1'IG|;7ff;!1,JJ!2'RIK!4'F!2+a>GHL!<'L+<+M+a>'I'R'a?GI!2,?+MIHK!2,?+MK/Hplen;!1'QG!2'R,5I!1'QC!2'R,5D!2'_M9:!2'G,59%~RS%~R!2'R,5:!2'G,5;!2'R,59$Ha;RU$~R+_N!3'_O9:#2%Ha;RU%~R+_N!2'R,5;!1,J|46;!2'_M9X!2'_89X%~RS%~R!2'R,5X!2'G,5Z$Ha;RU$~R+_N!3'_O9X#2%Ha;RU%~R+_N!2'R,5Z!2'_;1/sp0;|40;!1,J^2!2'a@^1^3%~R!2'R,5^1%~R!2'R,5^3!2'R,5!2'^W^1^3!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^0+M,5!2,^0+M=!3,_P+M!2,^0+M91!2'^8^:,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2}4}3!2,^2+M,K!1,^4+Y!2,^2+M8!1,J|^13fff80000000;|20;!3,_R+M^B^D!2'_A#4#5!1/ENVb;#:$vals;R!1+02$M;R%~R2!1+^E4$len;R+M$cap;R+M$t;R+^:$P70;R!3+C2!2'8#556$P38;R!3+C2!2'8#676$H1;R!2+^U!2'R,5#5!2'R#5#4$H2;R!2'G#5;$Ht;R!3+C+^:!2'b1!2'_A#6#7=#5vd!6'_B2?$b;R2!3+C+^:!3'b21#1!2'a\!1/ENVb;#;@#7vdvd!6'_B+M>$z;R+M!3+C+^:!2'b1#1B#7!6'_B+M=$z;R+M!3+C+^:!2'b1!2'_A#8#9#1#7#1B!2'_Z=&heq_LEN;RFE&Hplen0;RML&cstr;RNO&cstr0;RPQ&__sat75;RRT&__sat74;RVW&__sat73;RY[&__sat72;R\^0&__sat71;R^4^5&__arith;R&__wit;R^6^7&__varmap;R^8^9&__ff;R!7,^[^:'X+Y+Y,Z!7,[^:'X+Y+Y,Z!4,\+M^;,^1^<,^3!7,[^:'X+Y+Y,Z!4,\+M^<,^6^=,^3^>^?!2+^U!2'R,5=!2'G=;#1!2'_;1?!2'_Z>&heq_LEN;RFE&Hplen0;RML&cstr;RNO&cstr0;RPQ&__sat75;RRT&__sat74;RVW&__sat73;RY[&__sat72;R\^0&__sat71;R^4^5&__arith;R$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M!2,_4+M^@!3,_0+M!2,_4+M^A!2,_4+M,9,_5^6^7&__varmap;R!4,^Y+M!4,^Y+M!2,T+M#4#3^8#2^8^9&__ff;R!8,V^:'X+Y+Y,Z!7,[^:'X+Y+Y,Z!4,\+M^B,^6^=,^3^C!8,V^:'X+Y+Y,Z!7,^[^:'X+Y+Y,Z!7,[^:'X+Y+Y,Z!4,\+M^;,^1^D,^3!7,[^:'X+Y+Y,Z!4,\+M^D,^1^B,^3^C!8,V^:'X+Y+Y,Z!7,^[^:'X+Y+Y,Z!7,[^:'X+Y+Y,Z!4,\+M!2,^0+M^E,^1!2,^2+M^F,^3!6,^7^:'X+Y+Y,Z#6^C!7,^[^:'X+Y+Y,Z!7,[^:'X+Y+Y,Z!4,\+M^;,^1^G,^3!7,[^:'X+Y+Y,Z!4,\+M^G,^6^=,^3^>^?%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'G#1;%~R!2+^U!2'R,5#3!2'R#3#2%~R!2+^U!2'R^E#5#6!2+^U!2'R,5^H!2'G^H;!7#1!2'R^1!1,J|^2000000000000;^1#B#A#<#=/Hsp;!3+C+^:!3'b21?A#6!3+C+^:!3'b21?!2'a\^I@#6!2'a\^I'b0!7'b3#:#8#7#5#4#3#2!4'aX'^H#9^I!4,aY#6,b4'b0@").
Qed.

  Lemma cap2_x_val : forall vals (cap : Z),
    vals_ev vals 70 = Z_to_bv 64 cap -> 0 <= cap -> 2 * cap < 2 ^ 64 ->
    edenot (ENVb vals) cap2_x = Z_to_bv 64 (2 * cap).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^90|600;!1,20!1+11}^I!2'R,5#2|10;!1,J5!1,J0!2'_867|30;!1+1!1,29!2'A:/fdata;!1'I;!3+C+M/LEN;<vd!2,?+M<=!2'A:/path;}`m0!1'I?!1,J|;7ff;!2'RAB!4'F!2+a>?@C!<'L+<+M+a>'I'R'a??A!2,?+MA@B!2,?+MB/Hplen;!1'Q?!2'R,5A!1'Q;!2'R,5<!2'_M67!2'G,56%~RJ%~R!2'R,57!2'G,58!2'R,56$Ha;RL$~R+_N!3'_O67#2%Ha;RL%~R+_N!2'R,58!1,J|46;!2'_M6O!2'_86O%~RJ%~R!2'R,5O!2'G,5Q$Ha;RL$~R+_N!3'_O6O#2%Ha;RL%~R+_N!2'R,5Q!2'_;1/sp0;|40;!1,JV!2'a@UW%~R!2'R,5U%~R!2'R,5W!2'R,5!2'^WUW!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^2+M,K!7,[^1'X+Y+Y,Z!4,\+M!2,^0+M,5,^1^2,^3!1,^4+Y!2'^8^1,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2,^0+M6!7,[^1'X+Y+Y,Z!4,\+M!3,_7+M^7^2,^6!3,_P+M^71,^3$vals;R!1+02$cap;R+M$P70;R!3+C2!2'8#23!2'41#1$H1;R4$H2;R!2'G!2'^V6#38vd!6'_B2!2'41#4$b;R2!3+C2!4'_?1,_@!2'416#1!2'41!2'^V6#5!3'b5#4&heq_LEN;R>=&Hplen0;RDC&cstr;REF&cstr0;RGH&__sat75;RIK&__sat74;RMN&__sat73;RPR&__sat72;RST&__sat71;RXY&__arith;R$__x1;R+M&__wit;RZ[&__varmap;R\^0&__ff;R!8,V^1'X+Y+Y,Z^3^4^3^5^6%__x1;R+M%~R!2'R,5#14!2#1#>#<&heq_LEN;R>=&Hplen0;RDC&cstr;REF&cstr0;RGH&__sat75;RIK&__sat74;RMN&__sat73;RPR&__sat72;RST&__sat71;RXY&__arith;R$__x1;R+M&__wit;RZ[&__varmap;R\^0&__ff;R!8,V^1'X+Y+Y,Z^8^4^8^5^6%__x1;R+M%~R!2'G!2'^V6#18!2'G!2'^V6#28!2#1#>#;!2'8#53#3!3+C2!2'a\!1/ENVb;#5'b6!2'41!2'^V6#4").
Qed.

  Lemma m1o_but : forall off VM m', model_but_vm (model1o off VM) m' -> m' = model1o off (m_vmmaps m').
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$off;R+M$VM;R+aO$m';R+b7$H;R!2'b8!2/model1o;#3#2#1#1").
Qed.
  Lemma m1o_vm : forall off VM, m_vmmaps (model1o off VM) = VM.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$off;R+M$VM;R+aO!2,?+aO#1").
Qed.

  Lemma firstn_len_firstn : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
  Proof. intros X l w. rewrite length_firstn. rewrite <- (firstn_firstn l). rewrite firstn_firstn. f_equal. Abort.
  Lemma firstn_len_firstn : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>6lcd;g_[d;lcd;gAd;lcd;gb9d;lcd;g_Bd;lcd;g_\d;<scd;!1+0#4!3'_\#4#1#2!1+0#3!1,:#3!1,:#4!3'_\#3#13!2'A#35!3'_\#5#1#2!3,7#7#5#4!3'_\#7#18!1+0#8!3'_\#8#1#5!3,7#8#6#5!3'_\#8!1,E#1<$X;R{cd;$l;R!1+0#1!5'b9#2$l;R!1+0#2%w;R+<!3+C0!3'_\#4!2'A#41#21$w;R+<!6'_B23$l;R2!3+C0#1!3'_\#4#24!6'_B23$l;R2!3+C04#1!2,?235!2'_[#3#1!3'_\#363!2'_[#36$x;R#2$l;R2$IH;R%w;R+<!3+C!1+0#5!3'_\#5!2'A#57#27$w;R+<-<RN$n;R+<!3+C!1+0#7!3'_\#7!2'A#7989#12!2,?!1+0#6!3'_\#6,9!3,7#6#4#3$n;R+<!1$w;R+<vd!6'_B:;$l;R:!3+C!1+0#9!3,7#9#7#1!3,7#9#7!3'_\#9#2#6!2,?:!3,7#8#6;!3'_\#8!2'A#8;#5!1#4#1!3+C:!3'_\#8!2'A#8=<=#1#1").
Qed.

  Lemma cred_exit : forall k cr, 0 <= k <= 10 -> cred k cr -> Kc <= fst cr /\ Bc <= snd cr.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^Q0|32;!1,J0!2'_A1#4!1'aD/L;!2'R!2'H!2'^V23/Kc;!3'aE+M+M#3|10;!1,J5|4b;!1,J7!2'_868!1'aG/L;|@0000;!1,J;!1'aF#8|J0000000;!1,J>|30;!1+1!1,2@!2'AA/fdata;!1'IB!3+C+M/LEN;C!2'AA/path;}`m0!1'IE|;7ff;!1,JH!2'RGI!1,J|46;!2'G,56!2'_86K!2'R,56|600;!2'_;!1,2O/sp0;|40;!1,JQ|O00000000;!2,b?+M!1,JS}8}3!2,_4+MV!2,b?+M6}6!2,_4+MY}2!2,_4+M[}1!2,_4+M^0}5!2,_4+M^2!2,_4+M,9!3,b>+M\^4!3,b>+M^1^4}7}4!2,_4+M^8!1,^Z+M!1+W+M!2,^0+M,5!2,^2+M|34;!1,^4+Y!2,^2+M0|33;!2,^2+M^@!2,^0+M6!2,^0+M1!2,^2+M|31;!3,_R+M^C^D|11;!2,^2+M^F|20;!2,^2+M^H!2,^2+M,K!2,^2+M5!1,J|^13fff80000000;|22;!2,^2+M^M!1,J|^2000000000000;!1'aF#E$k;R+M$cr;R'aC$Hk;R!2+^U!2'R,5#2!2'R#21$H;R!2'b:#3#2!5'_:4!2'R!2'H!2'H!2'_A9!2'^V6!1'aF#4!2'^V2:/Bc;!3'aH+M+M#3!2+^U!2'R/Kc;!3'aE+M+M#3!2'R/Bc;!3'aH+M+M#3$~R4$~R!2'R!2'H!2'H!2'_A9!2'^V6!1'aF#5!2'^V!2'_A1#5:/Bc;!3'aH+M+M#4!2$C1;R!2'R!2'H!2'^V!2'_A1#63/Kc;!3'aE+M+M#5$C2;R!2'R!2'H!2'H!2'_A9!2'^V6!1'aF#7!2'^V!2'_A1#7:/Bc;!3'aH+M+M#6&H;R!2'b;#8#6!2+^U!2'R<=!2'R=?&H0;R!3'b</L;/sp0;/DL;!2'R,53&H1;R!3'b=/L;/sp0;/DL;!2'R,5:&heq_LEN;Rvd!2,?+MCDD&Hplen0;R!4'F!2+a>EFJ!<'L+<+M+a>'I'R'a?EG!2,?+MGFI!2,?+MI/Hplen;J&cstr;R!1'QE!2'R,5G&cstr0;R!1'QB!2'R,5C&__sat7;R!2'_M6K%~RL%~R!2'R,5K!2'G,5M&__sat6;R$Ha;RN$~R+_N!3'_O6K#2%Ha;RN%~R+_N!2'R,5M&__sat5;R!2'_M68%~RL%~R!2'R,58!2'G,59&__sat4;R$Ha;RN$~R+_N!3'_O68#2%Ha;RN%~R+_N!2'R,59&__sat3;R!2'a@PR%~R!2'R,5P%~R!2'R,5R!2'R,5!2'^WPR&__arith;R$__p2;Rw$__p1;Rw$__x9;R+M$__x8;R+M$__x7;R+M$__x6;R+M$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M!3,b>+MT!3,b>+M!2,_4+MUW!3,_0+M!3,b>+MX!3,b>+MZ\!3,_0+M!3,b>+MX!3,b>+MZ^1!3,_0+M!3,b>+M\^3!3,_0+M^5!3,_0+M!3,b>+M^1^3^6,_5!3,7+S!2,^\!3,_0+M!3,b>+MT!3,b>+M!2,_4+M^7W!3,_0+M!3,b>+M\^9!3,_0+M^5!3,_0+M!3,b>+M^1^9^6,_5!1,:+S!1+0+S&__varmap;R!4,^Y+M!4,^Y+M!4,^Y+M^:#5!2,T+M#:#3!4,^Y+M!2,T+M#8#6^:#2!4,^Y+M!4,^Y+M!2,T+M#7#:^:#4!4,^Y+M!2,T+M#9#:^:!1+U+M&__ff;R!8,V^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M^<,^1^=,^3^>!8,V^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M^<,^1^?,^3^>!8,V^;'X+Y+Y,Z!7,^[^;'X+Y+Y,Z!6,^7^;'X+Y+Y,Z#<!7,[^;'X+Y+Y,Z!4,\+M^A,^1!2,^0+M?,^3^>!8,V^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M!3,^5+M!3,^5+M!3,_R+M!3,_P+M^B!1,27!3,_7+M^B^A!3,_7+M^E^=^G,^1^I,^3^>!8,V^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M!3,^5+M!3,_7+M^E^?^J,^1^K,^3^>!8,V^;'X+Y+Y,Z!7,^[^;'X+Y+Y,Z!6,^7^;'X+Y+Y,Z#=!7,[^;'X+Y+Y,Z!4,\+M^D,^1^C,^3^>!8,V^;'X+Y+Y,Z!7,^[^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M!2,^0+M^L,^1^N,^3!7,[^;'X+Y+Y,Z!4,\+M^N,^1!2,^0+M^O,^3^>!7,^[^;'X+Y+Y,Z!7,[^;'X+Y+Y,Z!4,\+M^J,^1^K,^3!7,[^;'X+Y+Y,Z!4,\+M^G,^1^I,^3!2'^8^;,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p2;Rw%__p1;Rw%__x9;R+M%__x8;R+M%__x7;R+M%__x6;R+M%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R,5#9%~R!2'R,5#8%~R!2+^U#<!2'R#:?%~R!2'R!2'H!2'H!2'_A9!2'^V6#;!2'^V!2'_A1#9#<#6#7%~R!2'R!2'H!2'^V!2'_A1#:#;#5#6%~R!2+^U#@!2'R#;1%~R!2+^U!2'R^L#;!2'R#;^O!2+^U!2'R#8#9!2'R#:#;!B#1!2'R,5#E!2'R<^P:^P3#EP!3'aH+M+M#D/Bc;!3'aE+M+M#D/Kc;#;#<#=#>#?#C/Hsp;#2#1#1").
Qed.

  Lemma hdr_app : forall vals ext, hdr_vals vals -> (6 <= length vals)%nat -> hdr_vals (vals ++ ext).
  Proof. intros vals ext H HL. unfold hdr_vals. rewrite !vals_ev_app_l by lia. exact H. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma read_ok : forall z, lp_at (z - 1) -> rd_at z.
  Proof.
    intros z IH. unfold rd_at.
    intros k len want A vals R M VM cr Hk Hlen HlL Hz Hwant HL HV P38 P48 P70 P71 HR HK HA HC HH Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (heap_facts1 _ _ _ _ _ HH) as [HBR HDEF].
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
    pose proof (hiv_facts' vals HV) as HIV.
    assert (Hw : 1 <= want <= 65536 /\ want <= CAPk k - len) by lia.

    eapply (rz_read_file RSEGS scfg _ _ M (model1o len VM) ECALLW (Z_to_bv 64 3) path (Z_to_bv 64 len) fdata want);
      try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17%bv : reg). reflexivity.
    - regv HR (10%bv : reg). reflexivity.
    - rewrite u_small by lia. lia.
    - unfold model1o. rewrite m1o_fds. apply fds_lookup3.
    - unfold model1o. rewrite m1o_fs. exact Hfile.
    - regv HR (12%bv : reg). cbn [edenot ev ENVb ENV]. exact P71.
    - lia.
    - lia.
    - lia.
    - regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. apply stage_store_ok. lia.
    - regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. rewrite u_small by lia. unfold TASK_SIZE. lia.
    - cbv zeta. regv HR (12%bv : reg). regv HR (11%bv : reg). cbn [edenot ev ENVb ENV]. rewrite P71.
      rewrite (file_read_lit fdata len want) by lia.
      set (bs := firstn (Z.to_nat want) (skipn (Z.to_nat len) fdata)).
      assert (Hnb : Z.of_nat (length bs) = Z.min want (LEN - len)) by (subst bs; unfold LEN; apply length_read; lia).
      set (nb := Z.of_nat (length bs)) in Hnb.
      rewrite v_addi_pc4 by lia. change (0xbb604 + 4)%Z with 0xbb608%Z.
      unfold model1o. rewrite m1o_fds, with_fds_read. rewrite len_word_Z. fold nb.
      replace (Z_to_bv 64 len + Z_to_bv 64 nb)%bv with (Z_to_bv 64 (len + nb))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64)%Z; lia).
      change (mkModelE (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))) VM stdin0 fs0 None (Some tid) None)
        with (model1o (len + nb) VM).

      set (M1 := wbytes M (Z_to_bv 64 818073) bs).
      assert (HH1 : hi_heap HI [(A, CAPk k)] cr M1 VM).
      { subst M1. apply (heap_stagewrite scfg L HI HIok sp0 Hvsp DL); [lia | exact HH]. }
      assert (HA1 : above M1).
      { subst M1. unfold above. apply (above_wbytes sp0 mem0 Hvsp); [lia | lia | exact HA]. }
      assert (HC1 : rdn RSEGS M1 (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
      { subst M1. rewrite rdn_wbytes_out; [exact HC | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
      assert (HK1 : know_ok RSEGS (ENVb vals) M1 knRD).
      { rewrite <- keep_stage_RD. subst M1. unfold keep_stage.
        eapply (know_stagewrite L sp0 a0s path hw rdraw fdata Hvsp DL vals M bs [(48%nat, 65536%Z)] [(A, CAPk k)] knRD P0 ltac:(lia) _ HIV HK).
        Unshelve. intros i nb0 Hf. cbn in Hf.
        destruct (Nat.eqb i 48) eqn:Ei; [|discriminate]. apply Nat.eqb_eq in Ei. subst i. injection Hf as <-.
        split; [rewrite HL; lia|]. rewrite P48, u_small by lia. exists (CAPk k). split; [lia|]. split; [left; reflexivity | exact HBR]. }
      assert (HDEF1 : defined M1 A (CAPk k)).
      { subst M1. intros i Hi. apply wbytes_grows. apply HDEF. exact Hi. }
      assert (HSRC : rdn RSEGS M1 (Z_to_bv 64 818073) (length bs) = Some bs).
      { subst M1. apply rdn_wbytes_self. rewrite u_small by lia. lia. }
      clearbody M1. clear HK HH HA HC HDEF.
      destruct (Z.eq_dec nb 0) as [Hz0 | Hnz].
      +
        assert (HlenL : len = LEN) by lia.
        rewrite Hz0, Z.add_0_r.
        set (vals1 := vals ++ [Z_to_bv 64 0]).
        assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
        assert (HV1 : hdr_vals vals1) by (subst vals1; unfold hdr_vals; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
        assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (Q38 : vals_ev vals1 38 = Z_to_bv 64 (CAPk k)) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
        assert (Q48 : vals_ev vals1 48 = Z_to_bv 64 A) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
        assert (Q70 : vals_ev vals1 70 = Z_to_bv 64 len) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
        pose proof (env_app_regs vals [Z_to_bv 64 0] _ srRD R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
        pose proof (env_app_know RSEGS vals [Z_to_bv 64 0] _ M1 knRD ltac:(rewrite HL; vm_compute; reflexivity) HK1) as HK2.
        fold vals1 in HR1, HK2. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK2.
        pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 0) (ELit 0) HR1 eq_refl) as HR2.
        change (sr_upd srRD (ridx 10) (ELit 0)) with srRf0 in HR2.
        pose proof (hiv_facts' vals1 HV1) as HIV1.
        clear HR HR1 HK1. rename HR2 into HR. rename HK2 into HK.

        run_blockL_keep scr0 73%nat.
        assert (HH2 : hi_heap HI [(A, CAPk k)] cr M0 VM).
        { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals1 _ []); [exact Q0 | intros i nb' Hf; discriminate | vm_compute; reflexivity | exact HH1]. }
        assert (HA2 : above M0).
        { rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals1); [exact Q0 | vm_compute; reflexivity | exact HA1]. }
        assert (HC2 : rdn RSEGS M0 (Z_to_bv 64 A) (length fdata) = Some fdata).
        { rewrite EQM. apply (content_block' sp0 a0s path hw rdraw fdata Hvsp vals1); [exact Q0 | vm_compute; reflexivity | eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HlL; lia] |].
          rewrite HlenL in HC1. unfold LEN in HC1. rewrite Nat2Z.id, firstn_all in HC1. exact HC1. }
        destruct (heap_facts1 _ _ _ _ _ HH2) as [_ HDEF2].
        clear EQM HH1 HA1 HC1 HDEF1.

        eapply (rz_close RSEGS scfg _ _ M0 (model1o len VM) ECALLW (Z_to_bv 64 3)); try apply is_ecall_ECALLW.
        * vm_compute. reflexivity.
        * reflexivity.
        * reflexivity.
        * regv HR (17%bv : reg). reflexivity.
        * regv HR (10%bv : reg). reflexivity.
        * rewrite u_small by lia. lia.
        * unfold model1o. rewrite m1o_fds. apply fds_lookup3.
        * rewrite v_addi_pc4 by lia. change (0xbb604 + 4)%Z with 0xbb608%Z.
          unfold model1o. rewrite m1o_fds, fds_remove3, with_fds_close.
          pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3. clear HR.
          lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          set (valsG := relayV vals1 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
          pose proof (cred_exit k cr Hk Hcr) as [HX1 HX2];
          pose proof (HKC ltac:(lia) (CAPk k) cr ltac:(lia) ltac:(lia) HX1 HX2) as CL;
          unfold close_kg in CL;
          apply (CL valsG Rc M0 VM A)
          end.
          -- reflexivity.
          -- unfold valsG. rewrite relayV_lo by lia. exact Q0.
          -- unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact Q48.
          -- unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite Q70. f_equal. lia.
          -- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 HV1)).
          -- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 HV1))).
          -- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 (proj2 HV1)))).
          -- unfold valsG. rewrite relayV_lo by lia. exact (proj1 (proj2 (proj2 (proj2 (proj2 HV1))))).
          -- unfold valsG. rewrite relayV_lo by lia. exact (proj2 (proj2 (proj2 (proj2 (proj2 HV1))))).
          -- unfold valsG, ENVb, ENV. relay_regs HR3.
          -- intros lo hi Hlh. unfold knG. constructor.
             ++ cbn [kentry_ok edenot ev ENVb ENV]. unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3.
                rewrite Q70, u_small by lia. lia.
             ++ eapply ksubl_sound; [| exact knGbase_sub]. apply Forall_app. split.
                ** eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsG; rewrite relayV_lo by lia; exact Q0 | | ].
                   { unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact Q48. }
                   { unfold block_range in *. lia. }
                   { intros i Hi. apply HDEF2. lia. }
                ** unfold valsG. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
          -- exact HA2.
          -- exact HBR.
          -- exact HC2.
          -- exact HH2.
      +
        set (vals1 := vals ++ [Z_to_bv 64 nb]).
        assert (HL1 : length vals1 = 73%nat) by (subst vals1; rewrite length_app, HL; reflexivity).
        assert (HV1 : hdr_vals vals1) by (subst vals1; unfold hdr_vals; rewrite !vals_ev_app_l by (rewrite HL; lia); exact HV).
        assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (Q38 : vals_ev vals1 38 = Z_to_bv 64 (CAPk k)) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
        assert (Q48 : vals_ev vals1 48 = Z_to_bv 64 A) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
        assert (Q70 : vals_ev vals1 70 = Z_to_bv 64 len) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
        assert (Q72 : vals_ev vals1 72 = Z_to_bv 64 nb).
        { subst vals1. rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
        pose proof (env_app_regs vals [Z_to_bv 64 nb] _ srRD R ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
        pose proof (env_app_know RSEGS vals [Z_to_bv 64 nb] _ M1 knRD ltac:(rewrite HL; vm_compute; reflexivity) HK1) as HK2.
        fold vals1 in HR1, HK2. change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals1) in HR1, HK2.
        pose proof (regs_set_a0 (ENVb vals1) _ _ (Z_to_bv 64 nb) (EVar 72) HR1 ltac:(cbn [edenot ev ENVb ENV]; exact Q72)) as HR2.
        change (sr_upd srRD (ridx 10) (EVar 72)) with srRe0 in HR2.
        assert (HK3 : know_ok RSEGS (ENVb vals1) M1 knRe0).
        { constructor; [|exact HK2]. cbn [kentry_ok edenot ev ENVb ENV]. rewrite Q72, u_small by lia. lia. }
        pose proof (hiv_facts' vals1 HV1) as HIV1.
        clear HR HR1 HK1 HK2. rename HR2 into HR. rename HK3 into HK.

        run_blockL_keep scr0 73%nat.
        cbn [mem_denot] in EQM. subst M0.

        assert (Hbl : length bs = Z.to_nat nb) by lia.
        assert (WST : store_ok RSEGS M1 (Z_to_bv 64 (A + len)) (length bs) = true).
        { apply store_ok_of_defined; [lia | lia |]. intros i Hi. replace (A + len + i) with (A + (len + i)) by lia. apply HDEF1. lia. }
        assert (MCH : mcH M1 (Z_to_bv 64 (A + len)) (Z_to_bv 64 818073) nb bs).
        { constructor; [lia | exact Hbl | exact HSRC | exact WST
                      | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          destruct (ref_memcpy M1 (Z_to_bv 64 (A + len)) (Z_to_bv 64 818073) nb bs (seg_rom RSEGS) MCH Rc (Z_to_bv 64 0x39970)
                      ltac:(apply ret_ok_even; reflexivity)
                      ltac:(regv HR (1%bv : reg); reflexivity)
                      ltac:(regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; rewrite Q48, Q70, alu_add_Z; reflexivity)
                      ltac:(regv HR (11%bv : reg); reflexivity)
                      ltac:(regv HR (12%bv : reg); cbn [edenot ev ENVb ENV]; exact Q72)) as (R2 & MS & KP)
        end.
        replace (Z_to_bv 64 763484) with (0xba65c%bv : word) by (apply bv_eq; reflexivity).
        eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
        pose proof (regs_after_keeps vals1 _ srRe_tk _ R2 callee_kept ltac:(rewrite HL1; vm_compute; reflexivity) HR KP ltac:(cbn; intuition discriminate)) as HR3.
        rewrite HL1 in HR3. change (sr_after_call_j srRe_tk (map ridx callee_kept) 73) with srRm0 in HR3.
        set (vals2 := vals1 ++ junk_vals R2) in *.
        assert (HL2 : length vals2 = 105%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
        pose proof (know_blockwrite sp0 Hsp' vals1 _ M1 A (CAPk k) (A + len) bs knRe0 Q0 HZ ltac:(lia) ltac:(lia) HIV1 HK) as HK3.
        change (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW knRe0) with (keep_rd knRe0) in HK3. rewrite keep_rd_Re0 in HK3.
        pose proof (env_app_know RSEGS vals1 (junk_vals R2) _ _ knRe0 ltac:(rewrite HL1; vm_compute; reflexivity) HK3) as HK4.
        fold vals2 in HK4. change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR3, HK4.
        clear HK HK3 HR. rename HR3 into HR. rename HK4 into HK.
        set (M2 := wbytes M1 (Z_to_bv 64 (A + len)) bs) in *.
        assert (HH2 : hi_heap HI [(A, CAPk k)] cr M2 VM).
        { subst M2. eapply (heap_wbytes scfg L HI HIok sp0 Hsp' DL); [exact HH1 | left; reflexivity | lia | lia | lia]. }
        assert (HA2 : above M2).
        { subst M2. unfold above. apply (above_wbytes sp0 mem0 Hvsp); [lia | lia | exact HA1]. }
        assert (HC2 : rdn RSEGS M2 (Z_to_bv 64 A) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
        { replace (Z.to_nat (len + nb)) with (Z.to_nat len + length bs)%nat by lia.
          rewrite <- firstn_app_skipn.
          replace (firstn (length bs) (skipn (Z.to_nat len) fdata)) with bs by (subst bs; symmetry; apply firstn_len_firstn).
          apply rdn_app_Z; [ | | lia | lia].
          - subst M2. rewrite rdn_wbytes_out; [exact HC1 | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
          - subst M2. rewrite Z2Nat.id by lia. apply rdn_wbytes_self. rewrite u_small by lia. lia. }
        destruct (heap_facts1 _ _ _ _ _ HH2) as [_ HDEF2].
        assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q0).
        assert (XV : hdr_vals vals2) by (subst vals2; apply hdr_app; [exact HV1 | rewrite HL1; lia]).
        assert (X38 : vals_ev vals2 38 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q38).
        assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q48).
        assert (X70 : vals_ev vals2 70 = Z_to_bv 64 len) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q70).
        assert (X72 : vals_ev vals2 72 = Z_to_bv 64 nb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL1; lia); exact Q72).
        pose proof (hiv_facts' vals2 XV) as HIV2.
        clearbody M2. clear HH1 HA1 HC1 HDEF1 HSRC WST MCH KP.

        run_blockL_keep scr0 105%nat.
        cbn [mem_denot] in EQM. subst M0.
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        set (valsL := relayV vals2 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
        apply (IH k (len + nb) A valsL Rc M2 VM cr)
        end.
        * lia.
        * lia.
        * lia.
        * lia.
        * reflexivity.
        * unfold valsL. apply hdr_relay. exact XV.
        * unfold valsL. rewrite relayV_38. unfold gr. regv1 HR. exact X38.
        * unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact X48.
        * unfold valsL. rewrite relayV_70. unfold gr. regv1 HR. rewrite X70, X72, alu_add_Z. reflexivity.
        * unfold valsL, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
        * rewrite knLP_split. apply Forall_app. split.
          -- eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsL; rewrite relayV_lo by lia; exact X0 | | ].
             { unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact X48. }
             { unfold block_range in *. lia. }
             { intros i Hi. apply HDEF2. lia. }
          -- unfold valsL. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
        * exact HA2.
        * exact HC2.
        * exact HH2.
        * exact Hcr.
  Qed.



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma know_LP_ranges : forall vals M (len cap lo70 hi70 lo38 hi38 : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
    lo70 <= len <= hi70 -> lo38 <= cap <= hi38 ->
    know_ok RSEGS (ENVb vals) M knLP ->
    know_ok RSEGS (ENVb vals) M (KRange (EVar 70) lo70 hi70 :: KRange (EVar 38) lo38 hi38 :: knLP).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^G0|600;!1,20!1+11|30;!1+1!1,23}^I!2'41#6}V|10;!1,J8!1,J0!2'_89:!2+^U!2'R,5#8!2'G#8;!1/ENVb;#?!3'e2'^H=#>!3,^Q!1,^R5#;#:!3,^Q!1,^R7#9#8!2'41#=!2'_;1#1!2'A4/fdata;!1'IC!3+C+M/LEN;Dvd!2,?+MDE!2'A4/path;}`m0!1'IG!1,J|;7ff;!2'RIJ!4'F!2+a>GHK!<'L+<+M+a>'I'R'a?GI!2,?+MIHJ!2,?+MJ/Hplen;!1'QG!2'R,5I!1'QC!2'R,5D!2'_M9:!2'G,59%~RR%~R!2'R,5:!2'G,5;!2'R,59$Ha;RT$~R+_N!3'_O9:#2%Ha;RT%~R+_N!2'R,5;!1,J|46;!2'_M9W!2'_89W%~RR%~R!2'R,5W!2'G,5Y$Ha;RT$~R+_N!3'_O9W#2%Ha;RT%~R+_N!2'R,5Y!2'_;1/sp0;|40;!1,J^1!2'a@^0^2%~R!2'R,5^0%~R!2'R,5^2!2'R,5!2'^W^0^2!1,:+S!1+0+S!1+U+M!1+W+M!2,^2+M,K!2,^2+M8|11;!7,^[^8'X+Y+Y,Z!7,[^8'X+Y+Y,Z!4,\+M^9,^1^:,^3!7,[^8'X+Y+Y,Z!4,\+M^:,^1!2,^2+M^;,^3!1,^4+Y!2'^8^8,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R^5^6&__varmap;R!4,^Y+M!2,T+M#3#2!2,T+M#4^7&__ff;R!8,V^8'X+Y+Y,Z^<^=^<^>^?!2'R#2#3%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+^U!2'R#1#2^A!2+^U^A!2'R#3#4!7,^[^8'X+Y+Y,Z!7,[^8'X+Y+Y,Z!4,\+M!2,^0+M,5,^1^9,^3!7,[^8'X+Y+Y,Z!4,\+M^9,^6!3,_P+M!2,^0+M91,^3$__x1;R+M&__wit;R^5^6&__varmap;R!2,T+M#2^7&__ff;R!8,V^8'X+Y+Y,Z^C^=^C^>^?%__x1;R+M%~R!2+^U!2'R,5#1!2'G#1;!2+^U!2'R,5#2!2'G#2;!2'41#<$vals;R!1+02$M;R%~R2!1+^E4$len;R+M$cap;R+M$lo70;R+M$hi70;R+M$lo38;R+M$hi38;R+M$P70;R!3+C2!2'8#856$P38;R!3+C2!2'8#976$Hl;R<$Hc;R<$H70;R!2+^U!2'R#8#:!2'R#:#7$H38;R!2+^U!2'R#7#:!2'R#:#6$HK;R!4'^G'^H!1/ENVb;#>#='f8!6,e1+^F>?!3,7+^F@'f8vd!6'_B2A$b;R2!2+^U!2'R#<B!2'RB#;!6'_B+M#=$z;R+M!2+^U!2'R#<#1!2'R#1#;&heq_LEN;RFE&Hplen0;RLK&cstr;RMN&cstr0;ROP&__sat75;RQS&__sat74;RUV&__sat73;RXZ&__sat72;R[\&__sat71;R^3^4&__arith;R^@^B!4#1#D#G#E#=!2'_;1A!2'_Z#=&heq_LEN;RFE&Hplen0;RLK&cstr;RMN&cstr0;ROP&__sat75;RQS&__sat74;RUV&__sat73;RXZ&__sat72;R[\&__sat71;R^3^4&__arith;R^D^E!2#1#G#?!2'8#?5#7!4'e2'^H=#>?!6,e1+^F>@'f8vd!6'_B2^F$b;R2!2+^U!2'R#:B!2'RB#9!6'_B+M#<$z;R+M!2+^U!2'R#:#1!2'R#1#9&heq_LEN;RFE&Hplen0;RLK&cstr;RMN&cstr0;ROP&__sat75;RQS&__sat74;RUV&__sat73;RXZ&__sat72;R[\&__sat71;R^3^4&__arith;R^@^B!4#1#B#F#C#<!2'_;1^F!2'_Z#<&heq_LEN;RFE&Hplen0;RLK&cstr;RMN&cstr0;ROP&__sat75;RQS&__sat74;RUV&__sat73;RXZ&__sat72;R[\&__sat71;R^3^4&__arith;R^D^E!2#1#F#>!2'8#?7#6!4'e2'^H=#>@#1").
Qed.

  Lemma content_block_len : forall vals M log (A n len : Z),
    vals_ev vals 0 = sp0 -> log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W log = true ->
    hz sp0 A n -> 0 <= len <= n -> len <= LEN ->
    rdn RSEGS M (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
    rdn RSEGS (mem_denot (ENVb vals) M log) (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`E0|600;!1,20!1+11|30;!1+1!1,23%~R2!1+^E4|10;!1,J6!1,J|508;!2'_878!1+04!1+^E:!1'`3#6!1,J|^13fff80000000;!2'_;1/sp0;!2'R>!1,J|^2000000000000;!1'`3#8!2'A4/fdata;!1'`3#9!1'IA!2,?+MC!3+C+M/LEN;CvdDE!2'`7BA!2'`;,5#9!2'`8HC!1+C+<!1+C+M!1'I#1$x;R+<$y;R+<!3'bN!3+C+M!1'I#2L!3+C+<#2#1!2'bO#2#1$x;R+M#1$x;R+M!2'`;,5#1!<'O+M+<+M+M'`3N'IO'`@#9#9!2,?+M#9!2'A4/path;}`m0!1'IQ|;7ff;!1,JT!2'RSU!4'F!2+a>QRV!<'L+<+M+a>'I'R'a?QS!2,?+MSRU!2,?+MU/Hplen;!1'QQ!2'R,5S!1'QA!2'R,5C!2'`;,5#<!2'`8#1C!2'_M78!2'G,57%~R^2%~R!2'R,58!2'G,59!2'R,57$Ha;R^4$~R+_N!3'_O78#2%Ha;R^4%~R+_N!2'R,59!1,J|46;!2'_M7^7!2'_87^7%~R^2%~R!2'R,5^7!2'G,5^9$Ha;R^4$~R+_N!3'_O7^7#2%Ha;R^4%~R+_N!2'R,5^9|40;!1,J^=!2'a@>^>%~R!2'R,5>%~R!2'R,5^>!2'R,5!2'^W>^>}6}5!2,_4+M^B!2,_4+M,9!2,^\!3,_0+M!2,_4+M^A!3,_0+M^C^D,_5!3,_1+M!2,_2+M!1,_3,K^C}4!2,_4+M^G}3!2,_4+M^I}2!3,_0+M!2,_4+M^K^D!3,_0+M^H!3,_0+M^J^L!2,^\!3,_0+M^F^D,_5!1,:+S!1+0+S!1,^Z+M!2,T+M#5!4,^Y+M!2,T+M#6#6^Q!1+U+M!1+W+M!6,^7^U'X+Y+Y,Z#8!2,^2+M,K!2,^2+M6!7,[^U'X+Y+Y,Z!4,\+M^W,_6^X,^3|33;!2,^2+M^Z!1,^4+Y!6,^7^U'X+Y+Y,Z#9!2,^2+M|31;!6,^7^U'X+Y+Y,Z#:!2,^0+M,5!7,[^U'X+Y+Y,Z!4,\+M^X,_6_3,^3!2,^0+M=|20;!2'^8^U,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'A4!3'_\4@/fdata;!3'_\4B/fdata;!2'A4_:!3+C+<_;B!1+C;!3'dF!1/ENVb;#?#>#=!2'41#<!1'`3#:!3'_\4_@/fdata;!2'A4_A%n;R+<;!1+C2!4'fA+<;J_=%~R2_C!1+C5!4'fA2_C_D_E!1'bE'^H!1+0+fB%~R5_F!1+C_J!4'fA5_F_G_H%~R_J_K!4'fA_J_K_L_M!8'f@_J_K_L_M'bE!4'fC_N_O!3'fD_N_O!4'fE_J_K_M!4'fE5_F_H!4'fE2_C_E!4'fE+<;_=!1'fF;'bE'^H!2'fG_J'^H!2'fG2_?!6'fH+<J!1'fI+<_B_@#1!2,a2:_A!2'fG;_S%~R;w!4'fA;w_='fK!4'fA;w_='fO!2'fQ;_=!1'`3#;!2'A4!3'_\4_Y/fdata;!1'I_Z!2'`;,5#;!3+C+M_[_\!<'O+M+<+M+M'`3N'IO'`@#;#;!2,?+M#;!4'F!3+C+<_Z_Y`0!<'L+<+MJ'IKM_Z_[!2,?+M_[_Y!1O#;`1#3!2'A4!3'_\4!1'`3#?/fdata;!1'Q`3!2'R,5!1'I`3!2'`E,5#@!2'`;,5#@!2+`D!2+^U!2'G,5#@!3+C+M`7#@!2+^U!2'R#@,5!3+C+M`7,5!2'`;,5#A!2,T+M#2!7,[^U'X+Y+Y,Z!4,\+M_3,^1^W,^3!2'H#=#<!1'I_Y!2'H#=`=!2'H#=_\|32;!2,^2+M`@|11;!2,^2+M`B|21;$vals;R!1+02$M;R5$log;R!1+0+d;$A;R+M$n;R+M$len;R+M$P0;R!3+C2!2'8#6,9/sp0;$Hlog;R!3+C+^:!7'dH,999!1,:!2+`L+<+M!1,:+<'dI#5,^;$HZ;R!3'bL/sp0;#5#4$H2;R!2+^U!2'R,5#4!2'R#4#5$H3;R!2'R#5/LEN;$HC;R!3+C;!4'bE'^H#:!2'41#8<!2,a2:!3'_\4</fdata;&Hsp';R/Hsp;!2+^U!2'R=>?&HLn;R!6'_B+<!2'`7@A$n;R+<!3+C+<#1B&heq_LEN;RFE!4'`:!3+C+<GB!3+C+MIH!<'L+<+MJ'IKMGI!B'`=+<+<+<+M+M+M'`>'I'I'I'`8'`?BHPACDBHP&Hplen0;RWV&cstr;RXY&cstr0;RZ[&H4;R!2'`E,5#<!2+`D!2+^U!2'G,5#<!3+C+M\#<!2+^U!2'R#<,5!3+C+M\,5&z4;R!2'`;,5#=+M&H5;R!2'`C#1C!2+`D!2+^U!2'G#1C!3+C+M^0#1!2+^U!2'RC#1!3+C+M^0C&z5;R!2'`8#2C+M&__sat10;R^1^3&__sat9;R^5^6&__sat8;R^8^:&__sat7;R^;^<&__sat6;R^?^@&__arith;R$__p5;Rw$__p4;Rw$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S^E!3,7+S!2,^\!3,_0+M^F^M,_5!3,7+S!2,^\!3,_0+M^F!3,_0+M^H!3,_0+M^J^D,_5!3,7+S^E!3,7+S^N!3,7+S^N^O^P&__varmap;R!4,^Y+M!4,^Y+M!2,T+M#4#3^Q#2!4,^Y+M!4,^Y+M^R#6^Q#6^S^T&__ff;R!8,V^U'X+Y+Y,Z!7,`F^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z^V^Y!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M^[,^1^X,^3!7,[^U'X+Y+Y,Z!4,\+M^W,_6^[,^3^\!8,V^U'X+Y+Y,Z!7,`F^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z_0!7,[^U'X+Y+Y,Z!4,\+M^X,_6_1,^3!7,^[^U'X+Y+Y,Z_2_4^\!8,V^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1^[,^3^\!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_3,^1_1,^3!6,^7^U'X+Y+Y,Z#;^\!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_5,^1!2,^2+M_6,^3!6,^7^U'X+Y+Y,Z#<^\^Y_7_8%__p5;Rw%__p4;Rw%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+`D!2+^U#6!3+C+M#1#2!2+^U!2'R#5#2!3+C+M#1#5%~R!2+`D!2+^U#8!3+C+M#3#5!2+^U#9!3+C+M#3,5%~R!2'R#6#7%~R!2+^U!2'R,5#7#<%~R!2+^U!2'R=#7#>!3+C+M#6#7!?#1?!2'R#F#G!2'R#F,5!2'G,5#F!2'G#9CC#F>#9#7#8#:#A#B/Hsp;_9!3'`H4@/fdata;!3+C+<_9@!2$lemma;R_<!9'f>;_=!1'f?;!4'bE'^H_>_?_@!4'bE'^H_>_?_B!;'f@2_C_D_E!2'bE'^H_>!8'f@5_F_G_H_I_P_>!2'fG5_>_?_Q_@_B_R_S_S_T#1&HC;R!2$lemma;R_<!='fJ%x;R;_U!4'fA;_U_=_V_=!3'fL;_=!3'fM;_=!1'fN;!4'fA;_U_=_W,^3!8'fP;_U_=_=_X_V_W!8'fP;w_=_=_X'fK'fO'fR!4'bE'^H#>_?_@!4'bE'^H#>_?_B!;'f@2_C_D_E!2'bE'^H#>!8'f@5_F_G_H_I_P#>!2'fG5#>_?_Q_@_B_R_S_S_T#1#3!3+C;!4'bE'^H#=!2'41#;_;!2,a2:_:!@'dL/sp0;/a0s;/path;/hw;/rdraw;/fdata;/Hvsp;#?#>#=#<_A#9#8!9'dM/sp0;#<#;#<!1'I_B#7&heq_LEN;RFE&HLn0;R`2`0&Hplen0;RWV&cstr;RXY&cstr0;RZ[&cstr1;R`4`5&H4;R`6`8&z4;R`9+M&__sat9;R^1^3&__sat8;R^5^6&__sat7;R^8^:&__sat6;R^;^<&__sat5;R^?^@&__arith;R$__x1;R+M&__wit;R^O^P&__varmap;R`:^T&__ff;R!7,[^U'X+Y+Y,Z!4,\+M^W,^1^W,^3_7_8%__x1;R+M!2'R#1#1!1#1#J&heq_LEN;RFE&HLn0;R`2`0&Hplen0;RWV&cstr;RXY&cstr0;RZ[&cstr1;R`4`5&H4;R`6`8&z4;R`9+M&__sat9;R^1^3&__sat8;R^5^6&__sat7;R^8^:&__sat6;R^;^<&__sat5;R^?^@&__arith;R$__x1;R+M&__wit;R^O^P&__varmap;R`:^T&__ff;R!8,V^U'X+Y+Y,Z`;^\`;_7_8%__x1;R+M%~R!2'R,5#1!2'R,5#2!2#1!1'I!2'A4!3'_\4!1'`3#H/fdata;#9!6'_B+<_@$n;R+<!2'R!2'H#=L`<&heq_LEN;RFE!4'`:!2'R`>`<!2'R`?`<!<'L+M+M'RN'R$x;R+M$y;R+M!1'`<!2'R#2#1`>`?!B'`=+M+M+M+M+M+M'HNNN'H$n;R+M$m;R+M!2,?+M!4'cH+M+M'cI!2'H#2#1#=#=!2,?+M#=`=_\!<'O+<+M+M+M'I'INN$x;R+<!2,?+ML_Y_\`1`<`<!2,?+M`<&HLn0;R`2`0&Hplen0;RWV&cstr;RXY&cstr0;RZ[&cstr1;R`4`5&H4;R`6`8&z4;R`9+M&__sat9;R^1^3&__sat8;R^5^6&__sat7;R^8^:&__sat6;R^;^<&__sat5;R^?^@&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\^M,_5!3,7+S!2,^\!3,_0+M^H^L,_5^O^P&__varmap;R!4,^Y+M!4,^Y+M^Q#3^S#2!4,^Y+M^R#4^Q^T&__ff;R!8,V^U'X+Y+Y,Z!7,`F^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z^V!7,[^U'X+Y+Y,Z!4,\+M^X,_6`A,^3!7,^[^U'X+Y+Y,Z_0_4^\!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_3,^1`A,^3!7,[^U'X+Y+Y,Z!4,\+M`A,^1`C,^3^\!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_5,^1!2,^2+M`D,^3_2^\!7,[^U'X+Y+Y,Z!4,\+M!3,^5+M^W^X,^1!3,^5+M^W`C,^3_7_8%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+`D!2+^U#6!3+C+M#2#5!2+^U#7!3+C+M#2,5%~R!2+^U!2'R,5#6!2'R#6#4%~R!2+^U!2'R=#6#:!2'R!2'H#4#5!2'H#4#6!;#1?!2'R#H,5!2'G,5#H#H>#I#7#J#8#D/Hsp;_B#2#1").
Qed.

  Lemma loop_step : forall z, rd_at z -> lp_at z.
  Proof.
    intros z HRD. unfold lp_at.
    intros k len A vals R M VM cr Hk Hlen HlL Hz HL HV P38 P48 P70 HR HK HA HC HH Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (heap_facts1 _ _ _ _ _ HH) as [HBR HDEF].
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
    pose proof (hiv_facts' vals HV) as HIV.
    pose proof (dl_k L sp0 DL) as Hkpm. pose proof (dl_b L sp0 DL) as Hovh.
    destruct (Z_lt_le_dec len (CAPk k)) as [Hlt | Hge].
    -
      pose proof (know_LP_ranges vals M len (CAPk k) 0 67108863 65536 67108864 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
      change (KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP) with knLPp in HK1.
      clear HK. rename HK1 into HK.
      assert (TAIL : forall want R1 M1 (sc12 : expr),
                 want = Z.min (CAPk k - len) 65536 ->
                 regs_ok (ENVb vals) (sr_upd srPa (ridx 12) sc12) R1 -> edenot (ENVb vals) sc12 = Z_to_bv 64 want ->
                 know_ok RSEGS (ENVb vals) M1 knRDp ->
                 M1 = mem_denot (ENVb vals) M (s_log (fst (fst rPa))) ->
                 srealizes RSEGS scfg (mkCfg (mkst R1 (Z_to_bv 64 0xbb604) M1 (seg_rom RSEGS)) (model1o len VM)) K).
      { intros want R1 M1 sc12 Hwant HR1 H12 HK1 EQM.
        assert (HH1 : hi_heap HI [(A, CAPk k)] cr M1 VM).
        { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
        assert (HA1 : above M1).
        { rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA]. }
        assert (HC1 : rdn RSEGS M1 (Z_to_bv 64 A) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
        { rewrite EQM. apply (content_block_len vals _ _ A (CAPk k) len); [exact P0 | vm_compute; reflexivity | exact HZ | lia | lia | exact HC]. }
        destruct (heap_facts1 _ _ _ _ _ HH1) as [_ HDEF1].
        set (valsR := relayV vals R1 (gr R1 21) (gr R1 9) (gr R1 19) [gr R1 12]).
        apply (HRD k len want A valsR R1 M1 VM cr); [lia | lia | lia | lia | exact Hwant | reflexivity | | | | | | | | exact HA1 | exact HC1 | exact HH1 | exact Hcr].
        + unfold valsR. apply hdr_relay. exact HV.
        + unfold valsR. rewrite relayV_38. unfold gr. regv1 HR1. exact P38.
        + unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
        + unfold valsR. rewrite relayV_70. unfold gr. regv1 HR1. exact P70.
        + unfold valsR. rewrite relayV_71. unfold gr. regv1 HR1. exact H12.
        + unfold valsR, ENVb, ENV. relay_regs HR1; try (relay2 HR1; reflexivity).
        + assert (K6 : know_ok RSEGS (ENVb valsR) M1 (cellR :: knLP6)).
          { unfold valsR. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity]. }
          assert (KB : know_ok RSEGS (ENVb valsR) M1 (kn_blk 48 65536)).
          { eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact P0 | | ].
            - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
            - unfold block_range in *. lia.
            - intros i Hi. apply HDEF1. lia. }
          rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)]. }
      destruct (Z_lt_le_dec (CAPk k - len) 65536) as [Hsmall | Hbig].
      +
        run_blockL_keep (SCR [false; true] [] []) 71%nat.
        { apply (sc_ltu_want vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.ltb_lt; lia]. }
        { apply (sc_eq_70_38 vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL (CAPk k - len) _ _ want_x); [lia | exact HR | apply (want_x_val vals len (CAPk k) P70 P38); lia | exact HK | exact EQM].
      +
        run_blockL_keep (SCR [false; false] [] []) 71%nat.
        { apply (sc_ltu_want vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.ltb_ge; lia]. }
        { apply (sc_eq_70_38 vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL 65536 _ _ (ELit 65536)); [lia | exact HR | reflexivity | exact HK | exact EQM].
    -
      assert (Heq : len = CAPk k) by lia.
      destruct (Z.eq_dec k 10) as [Hk10 | Hk10].
      +
        assert (HC10 : CAPk k = 67108864) by (rewrite Hk10; reflexivity).
        assert (Hl10 : len = 67108864) by lia.
        rewrite Hl10 in P70 |- *. rewrite HC10 in P38, HH.
        apply (HREF ltac:(lia) A vals R M VM cr); assumption.
      +
        pose proof (CAPk_lt10 k ltac:(lia)) as HC25.
        pose proof (know_LP_ranges vals M len (CAPk k) 65536 33554432 65536 33554432 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
        change (KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP) with knLPg in HK1.
        clear HK. rename HK1 into HK.
        run_blockL_keep (SCR [true] [] []) 71%nat.
        { apply (sc_eq_70_38 vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.eqb_eq; lia]. }
        cbn [mem_denot] in EQM. subst M0.

        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (malloc_site scfg L HI HIok sp0 Hsp' Hal' DL vals _ srGa kn Rc M (model1o len VM) [(A, CAPk k)] cr (2 * CAPk k) (-128)
                  [(48%nat, 65536%Z)] [] 0x39998 K);
          [ exact HR | exact HK
          | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
          | exact P0 | exact HIV | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
          | lia | reflexivity
          | regv HR (10%bv : reg); rewrite Heq in P70; apply (cap2_x_val vals (CAPk k) P70); lia
          | lia
          | destruct Hcr as [Hc1 Hc2]; unfold credit_ok; split; nia
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact HH | reflexivity | reflexivity | reflexivity
          | intros i nb Hf; cbn in Hf;
            destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                             rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
          | intros v b Hf; discriminate
          | exact HK0 | ]
        end end.
        intros R' M' model' A2 vals' E' HL' HA2 HR' HK' HH' HBUT HBR2 HAP HAB HBLK HIMG. subst vals' E'.
        rewrite (m1o_but _ _ _ HBUT). rewrite (m1o_but _ _ _ HBUT), m1o_vm in HH'.
        set (VM2 := m_vmmaps model') in *. clearbody VM2.
        set (vals2 := vals ++ junk_vals R') in *.
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR', HK'.
        rewrite HL in HL', HA2, HR', HK'. change (71 + 10)%nat with 81%nat in HA2.
        pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
        assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (XV : hdr_vals vals2) by (subst vals2; apply hdr_app; [exact HV | rewrite HL; lia]).
        assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
        assert (X70 : vals_ev vals2 70 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); rewrite <- Heq; exact P70).
        pose proof (hiv_facts' vals2 XV) as HIV2.

        apply Forall_app in HK' as [HKB HK'].
        assert (HKU : know_ok RSEGS (ENVb vals2) M' knGb0).
        { change knGb0 with (kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa). apply Forall_app. split.
          - unfold kn_blk2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVb ENV]; rewrite HA2, u_small by lia; lia.
          - exact HK'. }
        clear HK' HKB HK HR. rename HKU into HK. rename HR' into HR.

        destruct (hio_wf L scfg HI HIok _ _ _ _ HH') as [WF2 _].
        destruct (WF2 (A2, 2 * CAPk k) ltac:(left; reflexivity)) as (_ & HDEF2 & _). cbn [fst snd] in HDEF2.
        assert (WST : store_ok RSEGS M' (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = true).
        { apply store_ok_of_defined; [lia | lia |]. intros i Hi. apply HDEF2. lia. }
        assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- Heq, <- HC. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HBLK; [lia|].
          exists (A, CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        clear HC HH HDEF.

        run_blockL_keep scr0 103%nat.
        cbn [mem_denot] in EQM. subst M0.
        assert (HFL : length (firstn (Z.to_nat (CAPk k)) fdata) = Z.to_nat (CAPk k)) by (rewrite length_firstn; unfold LEN in HlL; lia).
        assert (MCH : mcH M' (Z_to_bv 64 A2) (Z_to_bv 64 A) (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata)).
        { constructor; rewrite ?HFL, ?u_small by lia; try lia.
          - exact HC2.
          - exact WST.
          - specialize (HAP (A, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          destruct (ref_memcpy M' (Z_to_bv 64 A2) (Z_to_bv 64 A) (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata) (seg_rom RSEGS) MCH Rc (Z_to_bv 64 0x399b4)
                      ltac:(apply ret_ok_even; reflexivity)
                      ltac:(regv HR (1%bv : reg); reflexivity)
                      ltac:(regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; exact HA2)
                      ltac:(regv HR (11%bv : reg); cbn [edenot ev ENVb ENV]; exact X48)
                      ltac:(regv HR (12%bv : reg); cbn [edenot ev ENVb ENV]; exact X70)) as (R2 & MS & KP)
        end.
        replace (Z_to_bv 64 763484) with (0xba65c%bv : word) by (apply bv_eq; reflexivity).
        eapply srz_msteps; [reflexivity | reflexivity | exact MS |]. clear MS.
        pose proof (regs_after_keeps vals2 _ srGb _ R2 callee_kept ltac:(rewrite HL'; vm_compute; reflexivity) HR KP ltac:(cbn; intuition discriminate)) as HR3.
        rewrite HL' in HR3. change (sr_after_call_j srGb (map ridx callee_kept) 103) with srGc0 in HR3.
        set (vals3 := vals2 ++ junk_vals R2) in *.
        assert (HL3 : length vals3 = 135%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
        pose proof (know_blockwrite sp0 Hsp' vals2 _ M' A2 (2 * CAPk k) A2 (firstn (Z.to_nat (CAPk k)) fdata) knGb0 X0 HZ2 ltac:(lia)
                      ltac:(rewrite HFL; lia) HIV2 HK) as HK3.
        change (kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW knGb0) with knGc0 in HK3.
        pose proof (env_app_know RSEGS vals2 (junk_vals R2) _ _ knGc0 ltac:(rewrite HL'; vm_compute; reflexivity) HK3) as HK4.
        fold vals3 in HK4. change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR3, HK4.
        clear HK HK3 HR. rename HR3 into HR. rename HK4 into HK.
        set (M3 := wbytes M' (Z_to_bv 64 A2) (firstn (Z.to_nat (CAPk k)) fdata)) in *.
        assert (HH3 : hi_heap HI [(A2, 2 * CAPk k); (A, CAPk k)] (debit L cr (2 * CAPk k)) M3 VM2).
        { subst M3. eapply (heap_wbytes scfg L HI HIok sp0 Hsp' DL); [exact HH' | left; reflexivity | lia | rewrite HFL; lia | lia]. }
        assert (HA3 : above M3).
        { subst M3. intros a Ha. rewrite wbytes_out; [rewrite HAB by exact Ha; apply HA; exact Ha | rewrite u_small, HFL by lia; lia | rewrite u_small, HFL by lia; lia]. }
        assert (HC3 : rdn RSEGS M3 (Z_to_bv 64 A2) (length (firstn (Z.to_nat (CAPk k)) fdata)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { subst M3. apply rdn_wbytes_self. rewrite u_small, HFL by lia. lia. }
        rewrite HFL in HC3.
        assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
        assert (YV : hdr_vals vals3) by (subst vals3; apply hdr_app; [exact XV | rewrite HL'; lia]).
        assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
        assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
        assert (Y81 : vals_ev vals3 81 = Z_to_bv 64 A2) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
        pose proof (hiv_facts' vals3 YV) as HIV3.
        clearbody M3 vals3. clear HC2 WST HDEF2 WF2.
        assert (NEQ : A2 <> A).
        { specialize (HAP (A, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }

        run_blockL_keep scr0 135%nat.
        cbn [mem_denot] in EQM. subst M0.

        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (free_site scfg L HI HIok sp0 Hsp' Hal' DL vals3 _ srGc kn Rc M3 (model1o len VM2) [(A2, 2 * CAPk k); (A, CAPk k)]
                  (debit L cr (2 * CAPk k)) A (CAPk k) (-128) [] [] 0x399bc K);
          [ exact HR | exact HK
          | rewrite HL3; vm_compute; reflexivity | rewrite HL3; vm_compute; reflexivity | rewrite HL3; lia
          | exact Y0 | exact HIV3 | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVb ENV]; rewrite Y0; apply alu_add_w_lit
          | lia | reflexivity
          | right; left; reflexivity
          | regv HR (10%bv : reg); cbn [edenot ev ENVb ENV]; exact Y48
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact HH3 | reflexivity | reflexivity | reflexivity
          | intros i nb Hf; discriminate
          | intros v b Hf; discriminate
          | exact HK0 | ]
        end end.
        intros R4 M4 model4 vals' E' HL4 HR4 HK4 HH4 HBUT4 HAB4 HBLK4 HIMG4. subst vals' E'.
        rewrite (lb_remove_2 A2 (2 * CAPk k) A (CAPk k) NEQ) in HH4, HBLK4.
        rewrite (m1o_but _ _ _ HBUT4). rewrite (m1o_but _ _ _ HBUT4), m1o_vm in HH4.
        set (VM4 := m_vmmaps model4) in *. clearbody VM4.
        set (vals4 := vals3 ++ junk_vals R4) in *.
        change (Env (vals_ev vals4) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals4) in HR4, HK4.
        rewrite HL3 in HL4, HR4.
        change (sr_after_call_j srGc (map ridx c_kept) 135) with srGd0 in HR4.
        lazymatch type of HK4 with know_ok _ _ _ ?kn => change kn with knGd0 in HK4 end.
        assert (W0 : vals_ev vals4 0 = sp0) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y0).
        assert (WV : hdr_vals vals4) by (subst vals4; apply hdr_app; [exact YV | rewrite HL3; lia]).
        assert (W70 : vals_ev vals4 70 = Z_to_bv 64 (CAPk k)) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y70).
        assert (W81 : vals_ev vals4 81 = Z_to_bv 64 A2) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y81).
        pose proof (hiv_facts' vals4 WV) as HIV4.
        assert (HC4 : rdn RSEGS M4 (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC3. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HBLK4; [lia|].
          exists (A2, 2 * CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        assert (HA4 : above M4).
        { intros a Ha. rewrite HAB4 by exact Ha. apply HA3. exact Ha. }
        clear HR HK HC3 HA3 HH3. rename HR4 into HR. rename HK4 into HK.

        run_blockL_keep scr0 167%nat.
        assert (HH5 : hi_heap HI [(A2, 2 * CAPk k)] (debit L cr (2 * CAPk k)) M0 VM4).
        { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals4 _ []); [exact W0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH4]. }
        assert (HA5 : above M0).
        { rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals4); [exact W0 | vm_compute; reflexivity | exact HA4]. }
        assert (HC5 : rdn RSEGS M0 (Z_to_bv 64 A2) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite EQM. apply (content_block_len vals4 _ _ A2 (2 * CAPk k) (CAPk k)); [exact W0 | vm_compute; reflexivity | exact HZ2 | lia | lia | exact HC4]. }
        destruct (heap_facts1 _ _ _ _ _ HH5) as [_ HDEF5].
        clear EQM HH4 HA4 HC4.

        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        set (valsR := relayV vals4 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
        apply (HRD (k + 1) len 65536 A2 valsR Rc M0 VM4 (debit L cr (2 * CAPk k)))
        end.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * lia.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * reflexivity.
        * unfold valsR. apply hdr_relay. exact WV.
        * unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. change (nth 21 srGd (ELit 0)) with cap2_x.
          rewrite CAPk_S by lia. apply (cap2_x_val vals4 (CAPk k) W70); lia.
        * unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
        * unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. rewrite Heq. exact W70.
        * unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
        * unfold valsR, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
        * assert (K6 : know_ok RSEGS (ENVb valsR) M0 (cellR :: knLP6)).
          { unfold valsR. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity]. }
          assert (KB : know_ok RSEGS (ENVb valsR) M0 (kn_blk 48 65536)).
          { eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact W0 | | ].
            - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
            - unfold block_range in *. lia.
            - intros i Hi. apply HDEF5. lia. }
          rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)].
        * exact HA5.
        * rewrite Heq. exact HC5.
        * rewrite CAPk_S by lia. exact HH5.
        * destruct Hcr as [Hc1 Hc2]. unfold cred, debit. cbn [fst snd]. rewrite CAPk_S by lia. split; nia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_ok : forall n : nat, lp_at (Z.of_nat n).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^V0!1'I#1!1'bB0!1'I,9!1,2|600;!1+13|21;|30;!1+1!1,26!2'R,5#8!1,J,K!2'_A29}^J}V}^3}^I!1+07!1'`3#C!2+`L+M+M!2'A7/fdata;!1'IB!3+C+M/LEN;Cvd!2,?+MCD!2'A4#E!1'IF!1,J|607;!3+C+MGH!1+C+M!1'I#2!2'_A/LEN;#H!2'_A,59!2'RLM$x;R+M#1!1O,5$n;R+M$m;R+M!2,?+M!4'cH+M+M'cI!2'_A#2#1$x;R+<!2,?+M0!2,?+M9!2'A7/path;}`m0!1'IT!1,J|;7ff;!2'RVW!4'F!2+a>TUX!<'L+<+M+a>'I'R'a?TV!2,?+MVUW!2,?+MW/Hplen;!1'QT!2'R,5V!2'A4#I!1'QB!2'R,5C|10;!1,J^2!1,J|46;!2'_M^3^4!2'_8^3^4%~R!2'G,5^3%~R!2'R,5^4!2'G,5^6!2'R,5^3$Ha;R^8$~R+_N!3'_O^3^4#2%Ha;R^8%~R+_N!2'R,5^6!2'_;3/sp0;|40;!1,J^<!2'a@^;^=%~R!2'R,5^;%~R!2'R,5^=!2'R,5!2'^W^;^=!1,:+S!1+0+S!1,^Z+M!2,T+M#2!1+U+M!1+W+M!2,^2+M|22;!2,^2+M6!2,^0+M9!1,^4+Y!2'^8^E,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!1'I!1,E#2!1'I#3!1,E#3!1'I^N!2'_A^O9!2'H^M9!2'_A^Q9!2,?+M^M!2'H#19!2,^2+M,K$n;R+<!4'`0$n;R+<1!2'gZ2!2'g[2vd$k;R+M$len;R+M$A;R+M$vals;R!1+04$R;R!2'3!1,254$M;R%~R4!1+^E7$VM;R+aO$cr;R'aC$~R!2+^U8!2'R#8!1,J|32;$~R!2+^U8!2'R#8!1'aF#9$~R!2'R#9/LEN;$~R!2'R!2'_A/LEN;#::$~R!3+C+<!2'A4#9;$~R!1'a9#:$~R!3+C4!2'8#;<!2'43!1'aF#>$~R!3+C4!2'8#<=!2'43#=$~R!3+C4!2'8#=>!2'43#?$~R!3'bC!1/ENVb;#>'f7#=$~R!4'^G'^H!1/ENVb;#?#='f8$~R!1/above;#>$~R!3+C!1+^E?!4'bE'^H#?!2'43#B@!2,a2?!3'_\7@/fdata;$~R!5'aP/HI;!3,7A!4,`M+M+M#C!1'aF#E!1,:A#>#@#?$~R!2'b:#F#?!2'cR!4+bG'^H/scfg;!2,bH!5'bI/fx;#C!2'43!1,J|A19978;#B!1'bJ'^H!2/model1o;#F#A/K;&heq_LEN;RED&H14;R!4'F!3+C+<F;I!<'L+<+M!1+C+<'IJ$x;R+<$y;R+<!3'bN!3+C+MK0!3+C+<#2#1!2'bO#2#1FG!2,?+MG;H!2,?+MH#<I&H14;R!4'F!2'RL:N!<'L+M+M'RO'R$x;R+M$y;R+M!1'`<!2'R#2#1LL!2,?+ML:!2'_AP9!B'`=+M+M+M+M+M+M'_AOOO'_AQ2P!<'O+<+M+M+M'I'IOOR,9,5!2,?+M,599S#>N&Hplen0;RYX&cstr;RZ[&cstr0;R!1'Q\!2'R,5!1'I\&cstr1;R^0^1&__sat16;R^5^7&__sat15;R^9^:&__sat14;R^>^?&__arith;R$__p1;Rw$__x2;R+M$__x1;R+M&__wit;R^@^A&__varmap;R!4,^Y+M!4,^Y+M!4,^Y+M!2,T+M#3#3^B#3^C#3^B^D&__ff;R!8,V^E'X+Y+Y,Z!7,[^E'X+Y+Y,Z!4,\+M!3,_R+M^F^G,^1!3,_R+M!2,^0+M,5^H,^3^I!8,V^E'X+Y+Y,Z!7,[^E'X+Y+Y,Z!4,\+M^G,^1^F,^3^I!6,^7^E'X+Y+Y,Z#5^J^K%__p1;Rw%__x2;R+M%__x1;R+M%~R!2'R!2'_A#1#2M%~R!2'R#3#2#5!5#1+_S#Q/LEN;#9#H!1'bB:$n;R+<$IH;R1!2'gZ^L!2'g[^L&H;R&heq_LEN;RED!4'`:!3+C+M^M^P!3+C+M^M^R!<'L+M+MJOJ$x;R+M$y;R+M!1'`<!3+C+M#2#1^M^M^S^P^R!B'`=+M+M+M+M+M+M'_AOOO'_AQ^O^Q!<'O+<+M+M+M'I'IOOR^N^Q!<'O+<+<+M+M,E'I'I$x;R+M^T'P#3^M^S99S&Hplen0;RYX&cstr;RZ[&cstr0;R^0^1&cstr1;R!1'Q#6!2'R,5!1'I#6&__sat5;R^5^7&__sat4;R^9^:&__sat3;R^>^?&__arith;R$__x1;R+M&__wit;R^@^A&__varmap;R^C^D&__ff;R!7,[^E'X+Y+Y,Z!4,\+M^U,_6!3,_R+M!3,^5+M^U^H^H,^3^J^K%__x1;R+M!3+C+M#1!2'_A^T9!1#1!1'I#;!3+C+MK!2'_A^L9!6'_E+M^M$z;R+M!1'bB#1#2^P#1#1").
Qed.

  (* [comment removed for export] *)
  Hypothesis Hcr0 : cred 0 (debit L cr0 65536).

  (* [file_k] (Pm6DrvA.v:137-145) reads [p0 .. inp] and [p1 .. inp], so Pm6DrvA's
     section discharges [inp] as well and [K] was absorbed into that slot -
     "The term "K" has type "TSet" while it is expected to have type "ProcInput"". *)
  Theorem drv_file : file_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata cr0 inp K.
  Proof.
    unfold file_k.
    intros vals R M VM A1 HL P0 P48 P1 P2 P3 P4 P5 HR HK HA HBR HH.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Z1 & Z2 & Z3).
    assert (HV : hdr_vals vals) by (unfold hdr_vals; repeat split; assumption).
    pose proof (hiv_facts' vals HV) as HIV.
    change (Env (vals_ev vals) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals) in HR, HK |- *.
    change (Pm6DrvA.above_sp0 sp0 mem0 M) with (above M) in HA.
    change (model1 path tid fs0 stdin0 VM) with (model1o 0 VM).

    run_blockL_keep scr0 70%nat.
    assert (HH1 : hi_heap HI [(A1, 65536)] (debit L cr0 65536) M0 VM).
    { rewrite EQM. eapply (heap_block scfg L HI HIok sp0 Hsp' DL vals _ []); [exact P0 | intros i nb Hf; discriminate | vm_compute; reflexivity | exact HH]. }
    assert (HA1 : above M0).
    { rewrite EQM. unfold above. apply (above_sp0_block sp0 a0s path hw rdraw mem0 fdata Hvsp Hplen vals); [exact P0 | vm_compute; reflexivity | exact HA]. }
    destruct (heap_facts1 _ _ _ _ _ HH1) as [_ HDEF1].
    clear EQM HH HA.
    pose proof (read_ok (LEN + 1) ltac:(replace (LEN + 1 - 1) with (Z.of_nat (length fdata)) by (unfold LEN; lia); apply loop_ok)) as RD.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    set (valsR := relayV vals Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
    apply (RD 0 0 65536 A1 valsR Rc M0 VM (debit L cr0 65536))
    end.
    - lia.
    - unfold CAPk. rewrite Z.pow_0_r. lia.
    - unfold LEN. lia.
    - unfold LEN. lia.
    - unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - reflexivity.
    - unfold valsR. apply hdr_relay. exact HV.
    - unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact P48.
    - unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. reflexivity.
    - unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
    - unfold valsR, ENVb, ENV. relay_regs HR; try (relay2 HR; reflexivity).
    - assert (K6 : know_ok RSEGS (ENVb valsR) M0 (cellR :: knLP6)).
      { unfold valsR. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity]. }
      assert (KB : know_ok RSEGS (ENVb valsR) M0 (kn_blk 48 65536)).
      { eapply (kn_blk_ok L sp0 Hsp' DL); [ | unfold valsR; rewrite relayV_lo by lia; exact P0 | | ].
        - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact P48.
        - exact HBR.
        - exact HDEF1. }
      rewrite knRD_split. constructor; [exact (Forall_inv K6)|]. apply Forall_app. split; [exact KB | exact (Forall_inv_tail K6)].
    - exact HA1.
    - reflexivity.
    - unfold CAPk. rewrite Z.pow_0_r. exact HH1.
    - exact Hcr0.
  Qed.

  Lemma kbytes_rdn_sp : forall vals M kn n k zs,
    vals_ev vals 0 = sp0 -> know_ok RSEGS (ENVb vals) M kn -> kbytes kn (EVar 0) k n = Some zs ->
    - 2 ^ 20 <= k -> k + Z.of_nat n <= 0 ->
    rdn RSEGS M (Z_to_bv 64 (bv_unsigned sp0 + k)) n = Some (zbytes zs).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "Sa>0|600;!1,20!1+11|30;!1+1!1,23!1+0+M!1+^E5!1,^R,9!2,a25#3|10;!1,J9|44;!1,J;!2'_8:<!1'g>=!2'R>#5!1+04!1+^E@!2'_;1/sp0;%k;R+M%zs;R5%~R!3+C2!2'8#7,9/sp0;%~R!4'^G'^H!1/ENVb;#8#7#6%~R!3+C6!4'a5#77#4#58%~R?%~R!2'R!2'H#6!1'I#7,5!3+CA!4'bE'^H#;!2'41!2'HB#7#8!2,a2@!1'a8#6!1,:+M!2,a2@!1'a8#1}1!1+^E+d:!1,J,K!2,a25!3,7+M#2#1!1,^45!2,a25#:!3+CA!4'bE'^H#A!2'41!2'HB#<!1,E#>!2,a2@!1'a8#;!4'a5#B7!2'H#>H#@!5'h6'^H#A7#=F!2,a25#=!2,a25#B!3+CA!4'bE'^H#I!2'41!2'HB#D!1,E#F!2,a2@!1'a8#C!2,a25#C!3,7+M#:#4!3,7+M#9#3!2,a25#D!3,7+M#;#5!2'HB#H!2'41W!1,E#J!2'HB#G!2'a1F!2'41#;!1/ENVb;#M!1,`R#;!2'A4/fdata;!1'I^1!3+C+M/LEN;^2vd!2,?+M^2^3!2'RHH!2,?+MH!1'IY!2'H#H^7!1'I#J!2'R!2'H#H!2'H^9H,5$x;R+M#1$x;R+M$y;R+M!1'`<!2'R#2#1$x;R+M!2'H#1H!1^=^9!1^;^>$n;R+M$m;R+M!2,?+M!4'cH+M+M'cI!2'H#2#1$x;R+<!2,?+M!1'I#1!2,?+M,5!4'F!2'R^8,5^:!<'L+M+M'R^;'R^<^8!2'H#H^?!B'`=+M+M+M+M+M+M'H^;^;^;'H^@#H#H!2,?+M#H^7^?!<'O+<+M+M+M'I'I^;^;^AY^>!<'O+<+<+M+M,E'I'I^='P#J^9!2,?+M^9,5,5^B#B!2'A4/path;}`m0!1'I^D|;7ff;!1,J^G!2'R^F^H!4'F!2+a>^D^E^I!<'L+<+M+a>'I'R'a?^D^F!2,?+M^F^E^H!2,?+M^H/Hplen;!1'Q^D!2'R,5^F!1'Q#M!2'R,5!1'I#M!1'Q^1!2'R,5^2!2'_M:<!2'G,5:%~R^R%~R!2'R,5<!2'G,5=!2'R,5:$Ha;R^T$~R+_N!3'_O:<#2%Ha;R^T%~R+_N!2'R,5=!1,J|46;!2'_M:^W!2'_8:^W%~R^R%~R!2'R,5^W!2'G,5^Y$Ha;R^T$~R+_N!3'_O:^W#2%Ha;R^T%~R+_N!2'R,5^Y|40;!1,J_0!2'a@B_1%~R!2'R,5B%~R!2'R,5_1!2'R,5!2'^WB_1!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^0+MH!2'^8_8,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2}8!1,J3!2'RH_=!2'_;1#1!2'H_?#H!1,J0!2'_8:_A!1'IF!2'R,5_C!2'R,5W!2'GW_B!2'HW_C!2'R_G_B!2+^U_D_H!2+^U_F_I!2'R,5H!2'HWH!2'R_L_B!2+^U_K_M!2+^U_F_N!<'O+<+M+M+M'I'I^;^;^AFH^6!B'`=+M+M+M+M+M+M'H^;^;^;'H^@WW!2,?+MW_CH_P!2,?+M_B!2'_M:_A%~R^R%~R!2'R,5_A!2'G,5_B$Ha;R^T$~R+_N!3'_O:_A#2%Ha;R^T%~R+_N!2'R,5_B}3!2,_4+M_W}2!2,_4+M_Y!2,_4+M,9}5}4!2,_4+M`0!3,_0+M!2,_4+MF_[!2,^\!3,_0+M!2,_4+M_\!3,_0+M`1`2,_5!2,T+M#3!4,^Y+M`4#2!4,^Y+M!4,^Y+M!2,T+M#4#4_6#4_6!2,^0+M,5!2,^2+M|31;!7,[_8'X+Y+Y,Z!4,\+M`6,^1`7,^3!1,^4+Y!2,^2+M9!7,[_8'X+Y+Y,Z!4,\+M!3,^5+M`:!3,^5+M`7_9,^1`6,^3!2,^0+M:!2,g=+M!3,_P+M`<!1,2;!7,[_8'X+Y+Y,Z!4,\+M`=,^1`:,^3!1,J|^13fff80000000;!2,^2+M,K!7,[_8'X+Y+Y,Z!4,\+M!2,^0+M`?,^1`@,^3!1,J|^2000000000000;!7,^[_8'X+Y+Y,Z`A!7,[_8'X+Y+Y,Z!4,\+M`@,^1!2,^0+M`B,^3!3,^5+M`@`:!7,[_8'X+Y+Y,Z!4,\+M`6,^1`D,^3!3,_P+M`<1!3,^5+M`D_9!2'R,5#3!2'R!2'H#3!2'H#4H,5!2'H#5#6!1'I#W!2,`Q7#G!2'H!2'_;1!2'a\\!1'h:`L!1'h;`L!2'H#HH!2'HB`N!1+C+M!4,^Y+M`4#2_6!3,^5+M`@!3,^5+M`:_9!2'H#2H!2'H#1`S!2'HZ_C!2'41#1!1,E#K!1'I`W!2'H#I`X!1'I#K!2'R!2'H#I!2'H`ZH,5!1^=`Z!1^;`\!4'F!2'R`Y,5`[!<'L+M+M'R^;'R^<`Y!2'H#Ia0!B'`=+M+M+M+M+M+M'H^;^;^;'H^@#I#I!2,?+M#I`Xa0!<'O+<+M+M+M'I'I^;^;^A`W`\!<'O+<+<+M+M,E'I'I^='P#K`Z!2,?+M`Z,5,5^B#C!1'Q#N!2'R,5!1'I#N!3,^5+M`@_9!4'bE'^H#L!2'41Z!2'@F#I$z;R+M!2'a1F`V-^ERN$o;R!1+^E5w#12$~R5+_S+_N$e;R6a7$Hkb;R!3+C6J!2,a25#A&H;R!6'_E6Ja8,bUP#1+_S!2'cRQ#1!5'h6'^H#E7#AF!5'h6'^H#G7#CF!3+C6JR!2'cR!3+CA!4'bE'^H#K!2'41!2'HB#F!1,E#H!2,a2@!1'a8#E#1$vals;R!1+02$M;R%~R2!1+^E4$kn;R!1+0+^F$n;R+<!4'`0$n;R+<C$k;R+M$zs;R5$P0;R!3+C2!2'8#6,9/sp0;$HK;R!4'^G'^H!1/ENVb;#7#6#5$Hkb;R!3+C6!4'a5#67#4,98$Hk1;R?$Hk2;R!2'R!2'H#6!1'I,9,5&H;R!6'cP65$e;R6-^ERN$o;R!1+^E55#12$l;R5#1D!2,a25D!2,a25#6#3!3+C5D#6!1$H;R!3+C5D#7!6'_E5D$zs;R5!3+CA!4'bE'^H#=!2'41!2'HB#:,9E!2,?A!2,a2@!1'a8D#8#1#1$n;R+<$IH;RC$k;R+M$zs;R5$P0;R!3+C2!2'8#8,9/sp0;$HK;R!4'^G'^H!1/ENVb;#9#8#7$Hkb;R!3+C6!4'a5#87#4!1,E#68$Hk1;R?$Hk2;R!2'R!2'H#6!1'I!1,E#8,5&o;R!5'h6'^H#;7#7FG&Hr;R!2,?G#1!3+CG!5'h6'^H#<7#8F#1!2-^ERN$o;R!1+^E+d:%Hr;R!3+CG!5'h6'^H#>7#:F#1%Hkb;R!3+C6-^ERN$x;R!1+^E+d:6#22$e;R+d:-d:RN$e;R+d:6#18$z;R+M-^ERN$x;R!1+^E56!4'a5#A7!2'H#=H#?2$r;R5IJ$n0;R+<J$op;R+h7$a;R+d:$b0;R+d:J$op;R+h7$a;R+d:$b0;R+d:J$op;R+h8$a;R+d:$b0;R+d:J$op;R+h8$a;R+d:$b0;R+d:J$sx;R+^:$lo;R+<$n0;R+<$e0;R+d:J$sx;R+^:$k0;R+<$i;R+M$n0;R+<JJKL#22$e;R+d:!1$e;R+d:-d:RN$e;R+d:%Hr;R!3+CG!5'h6'^H#@7#<F!2,a2+d:#1%Hkb;R!3+C6-d:RN$e;R+d:6#28$z;R+M-^ERN$x;R!1+^E56M2$r;R5IJ$n0;R+<J$op;R+h7$a;R+d:$b0;R+d:J$op;R+h7$a;R+d:$b0;R+d:J$op;R+h8$a;R+d:$b0;R+d:J$op;R+h8$a;R+d:$b0;R+d:J$sx;R+^:$lo;R+<$n0;R+<$e0;R+d:J$sx;R+^:$k0;R+<$i;R+M$n0;R+<J!2,a25#<!3+CA!4'bE'^H#C!2'41!2'HB#>!1,E#@!2,a2@!1'a8#=#18$z;R+M!1$z;R+M$Hr;R!3+CGN!2,a2+d:!1,`R#1$Hkb;R!3+C6-^ERN$x;R!1+^E56M2$r;R5!2,a25!3,7+M#3#1JO&o;R!4'a5#C7!2'H#?H#A6&Hrest;R!2,?6#1!3+C6!4'a5#D7!2'H#@H#B#1!2-^ERN$o;R!1+^E5%Hrest;R!3+C6!4'a5#F7!2'H#BH#D#1%Hkb;R!3+C6-^ERN$x;R!1+^E56#22$r;R5!2,a25!3,7+M#8#1JPQ#22$l;R5!1$r;R5$Hrest;R!3+C6!4'a5#G7!2'H#CH#E!2,a25#1$Hkb;R!3+C6!2,a25!3,7+M#8#2R&H;R!6'cP65$e;R6-^ERN$o;R!1+^E55#12$l;R5#1S!2,a25TU#1!3+C5T#D!1$H;R!3+C5S#E!6'_E5V$zs;R5!3+CA!4'bE'^H#MXYEvdvdvd!;'f0'^H#LZF#I[!1'a8#5&H;R!='h9'^H\#L#K7#GF^0#D#:&heq_LEN;R^4^3!4'`:!2+a>FF^5!<'L+<+M+a>'I'R'a?FH^6FH^6&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R&__wit;R_4_5&__varmap;R_6_7&__ff;R!7,[_8'X+Y+Y,Z!4,\+M_9,^1_9,^3_:_;^5#1&heq_LEN;R^4^3!4'`:!2+a>F_<_>!<'L+<+M+a>'I'R'a?FH^6_<_=!2,?+M_=&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R&__wit;R_4_5&__varmap;R_6_7&__ff;R!7,[_8'X+Y+Y,Z!4,\+M_9,^1!2,^0+M_=,^3_:_;_>#1vdvd!6'_B2/sp0;$b;R2!2+^U!2'R,5_@!2+^U!2'G_@_B!2+^U_D!2'R!2'H_@_C_B&heq_LEN;R^4^3!4'`:!2+^U_E_J!2+^U_E_O!6'e0_E_J_E_O!3'cJ_E_E!2,?w_E!6'e0_F_I_F_N!3'cJ_F_F!2,?w_F!6'e0_D_H_K_M!<'L+M+M'R^;'R^<,5,5^B_CH_P!<'L+M+M'R^;'R^<_G_L_Q_B_B_R&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat9;R^Q^S&__sat8;R^U^V&__sat7;R_S_T&__sat6;R_U_V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M_X!3,_0+M_Z_[,_5!3,7+S`3!3,7+S`3_4_5&__varmap;R`5_7&__ff;R!8,V_8'X+Y+Y,Z`8`9!8,V_8'X+Y+Y,Z`;`9!8,V_8'X+Y+Y,Z`>`9!8,V_8'X+Y+Y,Z`C`9!7,^[_8'X+Y+Y,Z`E!7,^[_8'X+Y+Y,Z!7,[_8'X+Y+Y,Z!4,\+M`D,^6`F,^3!7,^[_8'X+Y+Y,Z!7,[_8'X+Y+Y,Z!4,\+M`6,^1_9,^3!7,[_8'X+Y+Y,Z!4,\+M`G,^1`F,^3_:_;%__x3;R+M%__x2;R+M%__x1;R+M%~R`H%~R`I%~R!2'R>#4%~R!2+^U!2'R`?#4!2'R#4`B!2+^U!2'R,5`J!2+^U!2'G`J_B!2+^U_K!2'R!2'H`JH_B!7#1`K#UB#:#=#P/Hsp;!2'8#M,9#E!2+^U!2'R,5`M!2+^U!2'G`M_B!2+^U_D!2'R!2'H`M_C_B!3'h<\`L_C!3+CA!4'bE'^H#L!2'h=\`LF!2,a2@!2'a1F!2'a\\^0&H;R!6'_E2!2'8#N,9$b;R2!3+CA!4'bE'^H#N!2'41!2'H_?#IF!2,a2@!2'a1F!2'41#=#1/sp0;#F!3+CA!4'bE'^H#MXF!2,a2@!2'a1F!2'41#<#1&H;R&heq_LEN;R^4^3!4'`:!3+C+M`O_G!3+C+M`O_L!<'L+M+M`P^;`P$x;R+M$y;R+M!1'`<!3+C+M#2#1`O`O!2,?+M`O_G_L_Q&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__x2;R+M$__x1;R+M&__wit;R_4_5&__varmap;R`Q_7&__ff;R!7,[_8'X+Y+Y,Z!4,\+M`R,_6`G,^3_:_;%__x2;R+M%__x1;R+M!3+C+M`T!2'H!2'H#1#2H!2#1#SB!3+C+M!2'HB!2'H#GH`U!6'_E+M`O$z;R+M!3+CA!4'bE'^H#N`V#K!2,a2@!1'a8#7!7#I`N#6#F#E#5&heq_LEN;R^4^3&Hk0;Ra1`[&Hplen0;R^J^I&cstr;R^K^L&cstr0;Ra2a3&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__x1;R+M&__wit;R_4_5&__varmap;R!2,T+M#2_7&__ff;R!8,V_8'X+Y+Y,Z!7,[_8'X+Y+Y,Z!4,\+M`=,^1`@,^3`9!7,[_8'X+Y+Y,Z!4,\+M`=,^1a4,^3_:_;%__x1;R+M%~R!2'R>#1!2'R>`S!2#1#T#O&heq_LEN;R^4^3&Hk0;Ra1`[&Hplen0;R^J^I&cstr;R^K^L&cstr0;Ra2a3&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__x2;R+M$__x1;R+M&__wit;R_4_5&__varmap;R`Q_7&__ff;R!8,V_8'X+Y+Y,Z!7,[_8'X+Y+Y,Z!4,\+M`R,^1`6,^3`9!7,[_8'X+Y+Y,Z!4,\+M!3,^5+Ma4`:,^1`6,^3_:_;%__x2;R+M%__x1;R+M%~R!2'R`T,5!2'R!2'H`S#3,5!3#1!1'I#V#T#;_G#1&heq_LEN;R^4^3&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat7;R^Q^S&__sat6;R^U^V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__p1;Rw$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M_Z`2,_5_4_5&__varmap;R`Q_7&__ff;R!8,V_8'X+Y+Y,Z`>`9!8,V_8'X+Y+Y,Z!7,^[_8'X+Y+Y,Z`A!6,^7_8'X+Y+Y,Z#5`9`E_:_;%__p1;Rw%__x2;R+M%__x1;R+M%~R!2'R>#2%~R!2+^U!2'R`?#2#4!2'R,5!2'H#3#4!5#1!2'RB`B#SB#N/Hsp;vd&heq_LEN;R^4^3!4'`:!2'G_G_B!2'G_L_B!<'L+M+M'G^;'G$x;R+M$y;R+M!1'`<!2'G#2#1_G_L_Q_B_B_R&Hk0;R^C^:&Hplen0;R^J^I&cstr;R^K^L&cstr0;R^M^N&cstr1;R^O^P&__sat9;R^Q^S&__sat8;R^U^V&__sat7;R_S_T&__sat6;R_U_V&__sat5;R^X^Z&__sat4;R^[^\&__sat3;R_2_3&__arith;R$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^\!3,_0+M`1!3,_0+M_X`2,_5_4_5&__varmap;R`5_7&__ff;R!8,V_8'X+Y+Y,Z`8`9!8,V_8'X+Y+Y,Z`;`9!8,V_8'X+Y+Y,Z`C`9!7,[_8'X+Y+Y,Z!4,\+M`G,^6`F,^3_:_;%__x3;R+M%__x2;R+M%__x1;R+M%~R`H%~R`I%~R!2+^U!2'R`?#3!2'R#3`B!2'G!2'H!2'H#4#5H_B!6#1`K#UB#:#=/Hsp;!2'G`U_B!3+CAa5!2,a2@!3'64[!4'a0+M4a6#5!3+CAa5!2,a2@!4'a0+M4a6V!3+CAa5!2,a2@!1'a8V#F#1#1#1$Hrest;R!3+C6!4'a5#E7!2'H#AH#CJa9#1#3#1$n;R+<!1$n0;R+<$Hr;R!3+CGN!2,a2+d:!1,^R#1$Hkb;R!3+C6JO&H;R!6'_E6Ja8,bU!2,a25#>#1+_S!2'cR!3+CA!4'bE'^H#E!2'41!2'HB#@!1,E#B!2,a2@!1'a8#?#1#1$op;R+h7$a;R+d:$b;R+d:!3$op;R+h7$a;R+d:$b;R+d:$Hr;R!3+CGa:!2,a2+d:!3,`V#3#2#1a9#3#2#1$op;R+h7$a;R+d:$b;R+d:!3$op;R+h7$a;R+d:$b;R+d:$Hr;R!3+CGa:!2,a2+d:!3,h>#3#2#1a9#3#2#1$op;R+h8$a;R+d:$b;R+d:!3$op;R+h8$a;R+d:$b;R+d:$Hr;R!3+CGa:!2,a2+d:!3,g1#3#2#1a9#3#2#1$op;R+h8$a;R+d:$b;R+d:!3$op;R+h8$a;R+d:$b;R+d:$Hr;R!3+CGa:!2,a2+d:!3,h?#3#2#1a9#3#2#1$sx;R+^:$lo;R+<$n;R+<$e;R+d:!4$sx;R+^:$lo;R+<$n0;R+<$e;R+d:$Hr;R!3+CGa;!2,a2+d:!4,h@#4#3#2#1$Hkb;Ra<&H;R!6'_E6J$e0;R6a7,bUU#1+_Sa=#4#3#2#1$sx;R+^:$k;R+<$i;R+M$n;R+<!4$sx;R+^:$k0;R+<$i;R+M$n0;R+<$Hr;R!3+CGa;!2,a2+d:!4,hA#4#3#2#1$Hkb;Ra<&H;R!6'_E6Ja8,bUU#1+_Sa=#4#3#2#1#1$Hr;R!3+CG!5'h6'^H#=7#9F!1,^4+d:$Hkb;R!3+C6J!2,a25#9&H;R!6'_E6Ja8,bUK#1+_S!2'cRL#1#1#5#1").
Qed.

  (* [comment removed for export] *)
  Lemma sc_and3_sp : forall vals M (off : Z) (c : branch_cond) (t : bool),
    vals_ev vals 0 = sp0 -> off mod 4 <> 0 -> - 2 ^ 20 <= off <= 0 ->
    match c with BC_NE => t = true | BC_EQ => t = false | _ => False end ->
    sc_denot RSEGS M (ENVb vals) (SCBr t c (EAlu ALU_AND (EAlu ALU_ADD (EVar 0) (ELit off)) (ELit 3)) (ELit 0)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`30|600;!1,20!1+11|30;!1+1!1,23|20;!1,J5|10;!1,J7|44;!1,J9!2'_88:!1'g>;|11;!1,J=!2'41>!2'41,5!2'_;1/sp0;!2'HA#7!2'41B!2'_;1C!2'_;1?!2'_;1@!2'HA#8!2'^WB6!3+C+MH,5!3+C+M!2'^WG6,5!1'_HJ!2'^W!2'HA#96!3+C+ML,5|40;!1,JN!2'hFAO!2'^VOP!2'^WAO!2'A4/fdata;!1'IS!3+C+M/LEN;Tvd!2,?+MTU!2'A4/path;}`m0!1'IW|;7ff;!1,JZ!2'RY[!4'F!2+a>WX\!<'L+<+M+a>'I'R'a?WY!2,?+MYX[!2,?+M[/Hplen;!1'QW!2'R,5Y!1'QS!2'R,5T!2'R,56!2'_M8:!2'G,58%~R^7%~R!2'R,5:!2'G,5;!2'R,58$Ha;R^9$~R+_N!3'_O8:#2%Ha;R^9%~R+_N!2'R,5;!1,J|46;!2'_M8^<!2'_88^<%~R^7%~R!2'R,5^<!2'G,5^>$Ha;R^9$~R+_N!3'_O8^<#2%Ha;R^9%~R+_N!2'R,5^>!2'a@AO!2'R,5A!2'R,5O%~R^C%~R^D!2'R,5R!2'hGAO%~R^C%~R^D!2'R,5P!2'HA#F!2,_2+M!1,_3,K}5!2,_4+M^J}2!2,_4+M^L!2,_4+M,9!2,^\!3,_0+M!3,_1+M^I^K!3,_0+M!3,_1+M^I^M^N,_5!2,^\!3,_0+M^K!3,_0+M^M^N,_5!1,:+S!1+0+S!1,^Z+M!1+U+M!1+W+M!2,^2+M,K!2,^2+M7!3,_7+M!2,^0+MO^W!2,^2+M5!1,^4+Y!2,^0+M8!2,g=+M!3,_P+M^[!1,29!2,^2+M3!2,^0+M,5!6,_Q^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_0,_6_1,^3!1,J|^13fff80000000;!7,[^U'X+Y+Y,Z!4,\+M!2,^0+M_3,^1^V,^3!2'^8^U,Z!2,?+^:,^;!4'^9#1#3vv_6!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'^VO#2!3+C+M#6,5!1,J|^2000000000000;!2'HQ#A!2,^0+M6!2'^V6P!2'^V_=6!2'H#=_>!2'^W#>6!2'^W#D6!2'H#C_>%~R!3+C+^:!2'`I#2#1,`J!1'_H!3+C+M#3#2%~R!1'_H!3+C+M#2#1!3+C+^:!2'`I#3#2,`J!2'a@#;6%~R!2'R,5#;%~R^5!2'R,5!2'^W#=6!1,J0!2'_M8_G!2'_88_G!2'G,5_I%~R^7%~R!2'R,5_G_J$Ha;R^9$~R+_N!3'_O8_G#2%Ha;R^9%~R+_N!2'R,5_I!3,_P+M^[1!2,^0+M>}4}1!2,^\!3,_0+M!2,_4+M_P!3,_0+M!2,_4+M_Q^N,_5!3,^5+M^V^W!2'H#5#6!3'_=,hCC?!1/ENVb;#9!1,^R,9!1,`R>!1,`R,5!3+C+^:!3'aW1!2'a\_V!3,`V,hC!3,`V,_>_W!1,`R#7_X!2'a\_V_Y,`J!1/ENVb;#<!3,`V,hC!3,`V,_>_W!1,`R#:_X!1/ENVb;#;!3,`V,hC!3,`V,_>_W!1,`R#9_X!3'aW1!2'a\`0`1!2'a\`0_Y$vals;R!1+02$M;R%~R2!1+^E4$off;R+M$c;R+hB$t;R+^:$P0;R!3+C2!2'8#5,9/sp0;$Hoff;R!1'_H!3+C+M!2'^W#46,5$Hr;R!2+^U!2'R<#5!2'R#5,5$Hc;R-hBRN$c;R+hBw#56!3+C+^:#4,`J!3+C+^:#4,^;+_S+_S+_S+_S&Hv;Rvd!6'_B2/sp0;$b;R2!3+C+^:!3'aW1!3'_=,hC!3'_=,_>#1!2'41#8?@,`J!6'_B2C$b;R2!3+C+^:!3'aW1!3'_=,hC#1?@,`Jvd!6'_B+M!2'hDDE$z;R+M!3+C+^:!2'`I#1F,`J!6'_B+MB$z;R+M!3+C+^:!2'`I!2'hD#1EF,`J!6'_B+M>$z;R+M!3+C+^:!2'`I!2'hDG#1F,`J!6'_B+M,5$z;R+M!3+C+^:!2'`I!2'hDG>#1,`J!6'_B+M!2'^WB!2'_888$z;R+M!3+C+^:!2'`I#1,5,`J&s;R!2'_FH,5!2+_GI!1'_HI-_GRN$s;R!2+_GJK!3+C+^:!2'`IL,5,`J#12$e;RJ!1$E;RM!2'cR!3+C+^:!2'`I!2'^W!2'HA#:6,5,`J!1#6&Hq;R&H;R!2'hEAO!3+C+MA!2'HQR&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R!2'a@#?6%~R!2'R,5#?%~R^5!2'R,5!2'^W#A6&__sat9;R^6^8&__sat8;R^:^;&__sat7;R^=^?&__sat6;R^@^A&__sat5;R^B^E&__sat4;R^F^G&__sat3;R!2'a@^H6%~R!2'R,5^H%~R^5!2'R,5!2'^W!2'HA#H6&__arith;R$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S^O!3,7+S^P!3,7+S^P!3,7+S^O^Q^R&__varmap;R!4,^Y+M!4,^Y+M!4,^Y+M!2,T+M#5#4^S#3^S#2!4,^Y+M!4,^Y+M!2,T+M#6#6^S#6^S^T&__ff;R!8,V^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M^V,_6!3,^5+M^X^Y,^3^Z!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M^\,^1!2,^2+M|31;,^3!6,^7^U'X+Y+Y,Z#8^Z!8,V^U'X+Y+Y,Z_2^Z!8,V^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M^Y,_6_1,^3^Z!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z_4!6,^7^U'X+Y+Y,Z#9^Z!7,[^U'X+Y+Y,Z!4,\+M^V,_6^X,^3_5_7%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!3+C+M#1!2'H_8#3%~R!2+^U!2'R<#6#7%~R%~R_9+_S%~R_9%~R!2+^U!2'R_3#5#;!3+C+M#6!2'^VO#7!<#1!2'RA_:!2'R#H,5#H!2'^W#H6RPA#>#C#D/Hal;/Hsp;!3+C+MAQ&E;R!6'_E+MA$z;R+M!3+C+M!2'^W!2'H#1#<6,5#2Q#1!3+C+M!2'^W!2'HQ#;6,5&H;R&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R!2'a@#@6%~R!2'R,5#@%~R^5!2'R,5!2'^W#B6&__sat9;R!2'a@_;6%~R!2'R,5_;%~R^5!2'R,5!2'^W!2'HQ#C6&__sat8;R^6^8&__sat7;R^:^;&__sat6;R^=^?&__sat5;R^@^A&__sat4;R^B^E&__sat3;R^F^G&__arith;R$__x2;R+M$__x1;R+M&__wit;R^Q^R&__varmap;R!4,^Y+M!2,T+M#3#2^S^T&__ff;R!7,[^U'X+Y+Y,Z!4,\+M!3,^5+M^V!3,_7+M!3,_7+M_<^W_<,_6!3,^5+M^X^V,^3_5_7%__x2;R+M%__x1;R+M!3+C+M!2'H#1!2'^V!2'^V6#26!2'H_8#1!2#1P#I!3+C+M!2'H#<_>!2'HQ#<&E;R!6'_B+M!2'HQ#=$z;R+M!3+C+M!2'^W#16,5#2_?#1!3+C+M!2'^W_?6,5&E;R!6'_E+M!2'^W!2'H#>_>6$z;R+M!3+C+M#1,5#1_@!4'hH#>_=6&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R!2'a@#B6%~R!2'R,5#B%~R^5!2'R,5_A&__sat9;R!2'a@_B6%~R!2'R,5_B%~R^5!2'R,5!2'^W!2'H#E_>6&__sat8;R^6^8&__sat7;R^:^;&__sat6;R^=^?&__sat5;R^@^A&__sat4;R^B^E&__sat3;R^F^G&__arith;R&__wit;R^Q^R&__varmap;R^S^T&__ff;R!6,_Q^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_<,_6_1,^3_5_7%~R!3+C+M6,5+_S#1!3+C+M_@,5#1#1$n;RK!1$E;R!1'_HM&H;R$x;R+M$y;R+M!5'_:_C_D%~R!1'_H!3+C+M#2#1!3+C+^:!2'`I#3#2,`J$~R_C$~R%~R!1'_H!3+C+M#3#2!3+C+^:!2'`I#4#3,`J#1!2'`K#2#1%x;R+M%y;R+M_D!3#1!2'^W!2'HA#;6,5#2#1!2'hDB!1'hI8!3'hJB8&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat8;R_E_F&__sat7;R^6^8&__sat6;R^:^;&__sat5;R^=^?&__sat4;R^@^A&__sat3;R^B^E&__arith;R&__wit;R^Q^R&__varmap;R^S^T&__ff;R!7,[^U'X+Y+Y,Z!4,\+M_1,^1^[,^3_5_7^9#1F!2'_Z,5&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R_E_F&__sat9;R^6^8&__sat8;R^:^;&__sat7;R_H_K&__sat6;R_L_M&__sat5;R^=^?&__sat4;R^@^A&__sat3;R^B^E&__arith;R&__wit;R^Q^R&__varmap;R^S^T&__ff;R!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1_1,^3!7,[^U'X+Y+Y,Z!4,\+M_1,^6_N,^3_5_7!2+^U!2'R,5,5_J#1E!2'_Z>&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R_E_F&__sat9;R^6^8&__sat8;R^:^;&__sat7;R_H_K&__sat6;R_L_M&__sat5;R^=^?&__sat4;R^@^A&__sat3;R^B^E&__arith;R&__wit;R^Q^R&__varmap;R^S^T&__ff;R!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1_O,^3!7,[^U'X+Y+Y,Z!4,\+M_O,^6_N,^3_5_7!2+^U!2'R,5>!2'G>_I#1D!2'_ZB&heq_LEN;RVU&Hplen0;R^0\&cstr;R^1^2&cstr0;R^3^4&__sat10;R_E_F&__sat9;R^6^8&__sat8;R^:^;&__sat7;R_H_K&__sat6;R_L_M&__sat5;R^=^?&__sat4;R^@^A&__sat3;R^B^E&__arith;R$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S^P!3,7+S_R!3,7+S_R!3,7+S^P!3,7+S^P!3,7+S_R^Q^R&__varmap;R!4,^Y+M!4,^Y+M!4,^Y+M!2,T+M#4#4^S#3^S#2^S^T&__ff;R!8,V^U'X+Y+Y,Z!8,V^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1^W,^3^Z!8,V^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1_<,^3^Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1_0,^3^Z!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M^\,^1^W,^3!7,[^U'X+Y+Y,Z!4,\+M^W,^1_1,^3^Z!8,V^U'X+Y+Y,Z_2^Z!8,V^U'X+Y+Y,Z!7,^[^U'X+Y+Y,Z_4!7,[^U'X+Y+Y,Z!4,\+M^V,^1!2,^0+M_:,^3^Z!7,^[^U'X+Y+Y,Z!7,[^U'X+Y+Y,Z!4,\+M_1,^1_S,^3!7,[^U'X+Y+Y,Z!4,\+M_S,^6_N,^3_5_7%__x3;R+M%__x2;R+M%__x1;R+M%~R%~R!2'R,5#2%~R^5!2'R,5#5%~R!2+^U!2'R<#3!2'R#3,5%~R%~R!3+C+M#5,5+_S%~R!2+^U!2'R_3#4!2'R#4_:!2+^U!2'R,5_T!2'G_T_I!7#1_A#DA#9#?#@/Hsp;!2'_;1_U!2'hKC?!3+C+^:!3'aW1_U@,`J!3'_=,_>/sp0;!2'41#7!2'g</sp0;#7!2'8#9,9#4_Z_Z!1-hBRN$b;R+hB%Hc;R-hBRN$c;R+hBw#16!3+C+^:#7,`J!3+C+^:#7,^;+_S+_S+_S+_S!4'aX'^H#;_[!4,aY#8#2_\_Y#76$Hc;R!3+C+^:#6,`J!6'_B+^:,`J$t;R+^:!4'aX'^H#;_[!4,aY#1,aZ_\_Yvd!6'_B+^:,`J$b;R+^:!3+C+^:#1,`J!2,?+^:,`J`2#2!4'aX'^H#:`0!4,aY,`J,aZ`1_Y#7#1$Hc;R!3+C+^:#6,^;!6'_B+^:,^;$t;R+^:!4'aX'^H#;_[!4,aY#1,hL_\_Yvd!6'_B+^:,`J$b;R+^:!3+C+^:!1'hM#1,^;_6`2#2!4'aX'^H#:`0!4,aY,^;,hL`1_Y#7#1$Hc;R+_S!2'cR!4'aX'^H#:`0!4,aY#7,hN`1_Y#1$Hc;R+_S!2'cR!4'aX'^H#:`0!4,aY#7,hO`1_Y#1$Hc;R+_S!2'cR!4'aX'^H#:`0!4,aY#7,b4`1_Y#1$Hc;R+_S!2'cR!4'aX'^H#:`0!4,aY#7,hP`1_Y#1#2").
Qed.

  Lemma m1o_fd2 : forall off VM, fd_lookup (m_fds (model1o off VM)) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10|10;$off;R+M$VM;R+aO!2,?!1+^E+bX!2,a2+bX!1,hQ!2'4!1,2|600;!1,J0").
Qed.

  (* [comment removed for export] *)
  Ltac close_exit2m HR HK P0 P5 :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
    lazymatch goal with |- srealizes _ _ (mkCfg _ ?model) _ =>
      apply (srz_conseq segs scfg _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
      [ | cbn [W map];
          replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
          apply t_eq_sym; apply t_emit_nil_exit ];
      apply ref_exit_Z; [| split; krd_solve HK];
      let Ktid := fresh "Ktid" in
      pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
        as Ktid; cbn [kentry_ok edenot ev ENVb ENV] in Ktid; rewrite P5 in Ktid;
      lazymatch type of HR with regs_ok _ _ ?Rc =>
      eexists (Z_to_bv 64 (bv_unsigned sp0 - 128)); exists (Z_to_bv 64 0xd9620), (bv_unsigned tid);
      eexists; eexists;
      split; [|split; [reflexivity|split; [reflexivity|]]];
      [ constructor;
        [ regv HR (2%bv : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV];
          rewrite P0; f_equal; lia
        | regv HR (4%bv : reg); reflexivity
        | regv HR (10%bv : reg); reflexivity
        | rewrite u_small by lia; lia
        | rewrite u_small by lia; lia
        | rewrite u_small by lia;
          let Hst := fresh "Hst" in
          pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                        _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
          unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENVb ENV] in Hst; rewrite P0 in Hst;
          replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
        | lit_u; lia
        | lit_u; lia
        | lia
        | lit_u; change (890400 - 168)%Z with 0xd9578%Z;
          let Htc := fresh "Htc" in
          krd HK 0xd9578%Z 4%nat Htc; rewrite Htc; cbn [ev ENVb ENV]; rewrite P5;
          rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
          rewrite Z_to_bv_bv_unsigned; reflexivity
        | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
        | repeat split; krd_solve HK
        | repeat split; krd_solve HK
        | krd_solve HK ]
      | left; split; [reflexivity|]; eexists; eexists; repeat split; krd_solve HK ]
    end end end.

  Theorem drv_refuse : refuse_k (t_die msg_refused fs0).
  Proof.
    unfold refuse_k.
    intros A vals R M VM cr HL HV P38 P48 P70 HR HK HA HH.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof HV as HV'. destruct HV' as (P0 & P1 & P2 & P3 & P4 & P5).
    pose proof (know_LP_ranges vals M 67108864 67108864 67108864 67108864 67108864 67108864 P70 P38
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
    change (KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP) with knLPr in HK1.
    clear HK. rename HK1 into HK.

    run_blockQ_keep scr_refuse 71%nat.
    { apply (sc_and3_sp vals _ (-538) BC_NE true P0); [vm_compute; lia | lia | reflexivity]. }
    { apply (sc_and3_sp vals _ (-546) BC_NE true P0); [vm_compute; lia | lia | reflexivity]. }
    { apply (sc_and3_sp vals _ (-546) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
    { apply (sc_and3_sp vals _ (-546) BC_EQ false P0); [vm_compute; lia | lia | reflexivity]. }
    pose proof msg_refused_k as (KB & ZB & LB38).
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
    unfold t_die, W;
    assert (HSC : stdio_call 71 sr kn = Some scR) by vmc_refl;
    pose proof (stdio_call_sound_fr scfg vals _ sr kn Rc Mc (model1o 67108864 VM) scR msg_refused []
             (t_exit (exit_code 2) fs0) ltac:(rdr) HR HK (eq_trans (f_equal (fun n => stdio_call n sr kn) HL) HSC)) as Hsc;
    cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scR app Z.of_nat] in Hsc;
    rewrite app_nil_r, LB38 in Hsc;
    apply Hsc; clear Hsc HSC
    end end.
    - rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
    - rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
    - rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
    - cbn [edenot length Z.of_nat]. lit_u. reflexivity.
    - cbn [length Z.of_nat Z.add]. lia.
    - right. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
    - left. rewrite !edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, !u_small by lia. lia.
    - cbn [edenot]. rewrite !u_small by lia. lia.
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVb ENV]. rewrite P0, u_small by lia.
      rewrite <- ZB. eapply (kbytes_rdn_sp vals _ _ 38%nat (-560)); [exact P0 | exact HK | exact KB | lia | cbn; lia].
    - reflexivity.
    - apply m1o_fd2.
    - reflexivity.
    - reflexivity.
    - apply t_exit_has_nil.
    - clear HR HK EQM.
      intros R' M' HR HK HP.
      assert (HL' : length (vals ++ junk_vals R') = 103%nat) by (rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      assert (P5' : vals_ev (vals ++ junk_vals R') 5 = tid) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P5).
      change (Env (vals_ev (vals ++ junk_vals R')) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb (vals ++ junk_vals R')) in HR, HK.

      run_blockQ scr0 103%nat.
      close_exit2m HR HK P0' P5'.
  Qed.

End DrvG.
End FPX_1.
