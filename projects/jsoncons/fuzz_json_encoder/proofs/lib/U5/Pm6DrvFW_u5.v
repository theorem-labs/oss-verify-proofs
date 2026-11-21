(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the rseq-dependent auxv): changed LH2P, ME, SSP and 11 more; added entry, inp, mbase and 1 more; removed Hfits; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/U/Pm10DrvF_u.v, 346 lines within its lines 23-562. *)
(* [comment removed for export] *)
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
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib RefLayout. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6StartupDefs_u5 Pm6Startup_u5 Pm6MainEntry_u5. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Hoare MemSplit Frame.
  From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.musl Require Import Pm6MemcpyBase_u5 Pm6Memcpy_u5. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6ExitBase_u5 Pm6StdioDefs_u5 Pm6Exit_u5 Pm6LibStdioCall_u5 Pm6LibMainRet_u5 Pm6PrintfBufBase_u5 Pm6PrintfBuf_u5.
  From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface LibIface LibIfaceFp DrvKit. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6Drv_defs_u5 Pm6DrvLib_u5 Pm6DrvA_u5 Pm6DrvB_u5 Pm6DrvC_defs_u5 Pm6DrvC_u5 Pm6DrvD_defs_u5 Pm6DrvLibL_u5 Pm6DrvD_u5 Pm6DrvE_u5.
  From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import LibIfaceFpW. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6DrvLibLW_u5. From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SpecG.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Drv Require Import LibStaticsU.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Datatypes; @cons]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Ubsan; @M; @loaded_segments]; [@Corelib; @Init; @Datatypes; @None]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @VmMaps]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @model_but_vm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvC_u5; @CFG_range]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvC_u5; @CFG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @CALLS]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Datatypes; @length]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvC_u5; @PL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @vals_ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @REG]; [@Corelib; @Init; @Datatypes; @prod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @IMG_PW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @CPpw]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ev]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @find_nz]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @Gt]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @conj]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @log_in_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @mem_denot_frame_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @regions_pw]; [@Stdlib; @micromega; @Tauto; @NOT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ls_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @log_below_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_static]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_static]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @mem_pw_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @mem_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @mem_denot_above]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hi_heap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ls_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @hz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hio_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @alloc_private]; [@Stdlib; @ZArith; @BinInt; @Z; @le_gt_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_sptop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_sptop]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_ge_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @BinInt; @Z; @ge]; [@Corelib; @Init; @Logic; @or_introl]; [@Stdlib; @Logic; @Classical_Prop; @NNPP]; [@Stdlib; @micromega; @RingMicromega; @OpGe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @mem_denot_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Drv; @LibStaticsU; @lsu_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @in_foot]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_foot]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_foot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_rw_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_rw_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @in_initc]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_initc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_heap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_initc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @heap_layout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_heap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @rdn_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6StdioDefs_u5; @sw_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6StdioDefs_u5; @swp_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6StdioDefs_u5; @swp_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @auxvp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @rnd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @know_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @knLB1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @auxvp_u]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefLayout; @auxv_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @lib_init_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @CANZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @rnd_u]; [@Corelib; @Init; @Nat; @add]; [@LinuxProcessSemantics; @LinuxProcessSem; @StackLayout; @stack_to_mem]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @entry_stack_image]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Ubsan; @M; @phdrs]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@LinuxProcessSemantics; @LinuxProcessSem; @StackLayout; @at_random_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @StackLayout; @ed_random]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefLayout; @auxv_off_bound]; [@LinuxProcessSemantics; @LinuxProcessSem; @StackLayout; @build_stack_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @build_stack_bytes_within_span]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @entry_stack_span]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @entry_stack_fits]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @CANZ_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kblob_find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ELit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6StartupDefs_u5; @canary_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kblob_rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @adenot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @eb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6StartupDefs_u5; @length_word_to_le_bytes]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_init_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @cellz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_td_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_td_tid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_td_locale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_locale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_td_canary]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_guard]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_auxvp]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @auxv_words]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_init_cells]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @know_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @kentry]; [@Stdlib; @Lists; @List; @nth_error]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @kentry_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kread_rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @kread]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @edenot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @flat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @adenot_lit0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EExt]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ext_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @ext_val_zx_id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @locale_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @kimg_rdn]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KAlign]; [@Corelib; @Init; @Logic; @eq_trans]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefLayout; @auxv_words]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_phent]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_phnum]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_phnum]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_phent]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_phdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_phdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @auxv_word_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_init_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_auxvp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_guard]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_td_canary]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_locale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_td_locale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_td_tid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_td_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_init_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @dl_segs]; [@Stdlib; @Lists; @List; @length_zero_iff_nil]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @lh_vals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @p0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @p1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @regs_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvA_u5; @ENV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @srLH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @knLH1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvA_u5; @above_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @blk_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @payload]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @cr1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIfaceFp; @fp_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvB_u5; @model2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @b48]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @t_guard]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @b10]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @block_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @hz_of_block_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @PL_range']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @payload_len]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @dll_credit_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ll_credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @CALLS_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeLaws; @t_emit_has_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @zero_lines]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @rz_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6Drv_defs_u5; @FUEL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @STOPS_T]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6Drv_defs_u5; @scr0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @scripts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_exec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @carry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_log]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @sc_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @block_pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @ls_g0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @hz_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Drv; @LibStaticsU; @lsu_init]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @init_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibLW_u5; @lib_sitew]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @blobs_ev]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6MainEntry_u5; @blobs0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @srLB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @sr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @has_window]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_get]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvA_u5; @alu_add_w_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @reg_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @credit_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @credit_le_head]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLib_u5; @sub_block]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Corelib; @Init; @Logic; @ex_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @junk_vals]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @Env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @sr_after_call_j]; [@Corelib; @Lists; @ListDef; @map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ridx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6Drv_defs_u5; @c_kept]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @keep_lib]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vmmaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibIface; @credit_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srz_conseq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @m2_but']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @vals_ev_app_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @knLr1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @STOPS_P]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefNodes; @rz_ioctl_winsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @ECALLW]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @is_ecall_ECALLW]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @regupd]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @errno_ret]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @ENOTTY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @regs_set_a0]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @stdio_res]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @SCR_]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @stdio_call]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @scP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @stdio_call_sound_fr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_wb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_wp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_s]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_sp]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_fd]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_sr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_f]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_bufp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_bufsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @sc_ret]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @edenot_add_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @nl_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @sw_pw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @junk_vals_length]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @STOPS_R]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @relay]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @WP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_u5; @lay_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvB_u5; @vals_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @srR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @relay_ok_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @ksubl_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @wposK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @flagsK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @knR2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKit; @ksubl_b]; [@Stdlib; @Lists; @List; @Forall_inv]; [@Stdlib; @Lists; @List; @Forall_inv_tail]; [@Corelib; @Lists; @ListDef; @Forall]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6LibStdioCall_u5; @flat_abs0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @know_ok_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvD_defs_u5; @knLH2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvLibL_u5; @credit_le_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @v_addi_pc4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @iter1_guard_eq]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @last_S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @step_S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @LH2P]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @iter2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @exit_code]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvE_u5; @SSP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @iter1w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @Pm6DrvFW_u5; @FPX_1; @DrvF; @SS_real]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @succG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpecG; @loop_guard_eq]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_blockT" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX false.
Tactic Notation "run_blockT_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX true.
Tactic Notation "run_blockP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_P scr NX true.
Tactic Notation "run_blockR_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_R scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.

Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10e44) 1 = Some [Z_to_bv 8 10].
Proof. vmc_refl. Qed.
Lemma locale_img : forall k, (k < 6)%nat ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 (0xfd2d8 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^60}6!2'A#10|30;!1,42!1+33!1+24!1+15!1,4|600;$~R!1+37!1,>4!1,8|C7d2d8;!1,82!1'D#2}8!2,55!2'E<!2'?7,F!3,73,F!2'93,F!2,06!2,55!3,64>!3,64>!3,64>!3,64>!3,64>!3,64>!3,64>!3,64>!1,:4!1,H#1!2'A@0!1,H#2}1!1,H@!2'AD0!1,HB}2!1,HD!2'AH0!1,HF}3!1,HH!2'AL0!1,HJ}4!1,HL!2'AP0!1,HN}5!1,HR!1,8,K|22;!1,8V!2'J!2'B!2'B!2'B!2'B!2'B!2'B;UUUUUUW$x;R+M!2'B#1U!1Y;!1YZ!1Y[!1Y\!1Y^0!1+W+M!2,^2+M,K!1,>+Y!2,^0+MU$k;R+@$Hk;R1!1-@RN$n;R+@%Hk;R1!3+;6!4'<'=8!2'?7!2'B9!2'C:;<=#22$Hk;R!2'A,G0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'D,G<=$n;R+@!1$k;R+@$Hk;RA!1-@RN$n;R+@%Hk;RA!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DB<=#22$Hk;R!2'AC0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DC<=$n;R+@!1$k;R+@$Hk;RE!1-@RN$n;R+@%Hk;RE!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DF<=#22$Hk;R!2'AG0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DG<=$n;R+@!1$k;R+@$Hk;RI!1-@RN$n;R+@%Hk;RI!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DJ<=#22$Hk;R!2'AK0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DK<=$n;R+@!1$k;R+@$Hk;RM!1-@RN$n;R+@%Hk;RM!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DN<=#22$Hk;R!2'AO0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DO<=$n;R+@!1$k;R+@$Hk;RQ!1-@RN$n;R+@%Hk;RQ!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DR<=#22$Hk;R!2'AS0vv?!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'DS<=$n;R+@!1$k;R+@$Hk;R!2'A!1,HP0&Hk0;R!4'I!2'AT0X!<'L+@+M'A'D'J'NT!1Y^1!<'O+@+@+M+M,H'D'DY'PR^1!<'O+@+@+M+M,H'D'DY'PN^0!<'O+@+@+M+M,H'D'DY'PJ\!<'O+@+@+M+M,H'D'DY'PF[!<'O+@+@+M+M,H'D'DY'PBZ!<'O+@+@+M+M,H'D'DY'P#2;!2,0+M;0W!2,0+MW#1X&cstr;R!1'Q#3!2'R,F!1'D#3&__arith;R$__p1;Rw$__x1;R+M&__wit;R!1,:+S!1+2+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,V^2'X+Y+Y,Z!7,[^2'X+Y+Y,Z!4,\+M!2,^0+M,F,^1^3,^3^4!8,V^2'X+Y+Y,Z!7,[^2'X+Y+Y,Z!4,\+M!3,^4+M!3,^4+M!3,^4+M!3,^4+M!3,^4+M!3,^4+M^3^5^5^5^5^5^5,^5!2,^0+MW,^3^4!6,^6^2'X+Y+Y,Z#4!2'^7^2,Z!4'^8#1#3vv!2,0+^9,^:!3+;+^9!2'^;#1#3,^:!3'^<+M,F#2%__p1;Rw%__x1;R+M%~R!2'R,F#1%~R!2'J!2'B!2'B!2'B!2'B!2'B!2'B#2UUUUUUW#4!4#1!3+;6!4'<'=8!2'?7!2'B9!2'C:!1'D!1,H!1,H!1,H!1,H!1,H!1,H#5<=!1'D#5#2#3#1#1#1#1#1#1#1#1#1#1#1#1").
Qed.

Section DrvF.
  Context {RE : RunEnv}. Context {RO : ReaderOn}.
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
  Variable CAP : Z.
  Hypothesis HCAP : (65536 <= CAP <= 67108864)%Z.
  Variable crC : credit.
  Hypothesis HLEN : (Z.of_nat (length fdata) < CAP)%Z.
  Variable Lay : lib_layout.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layout Lay L.
  Hypothesis LIok : lib_iface_ok_u Lay scfg HI LSt.
  Hypothesis LXok : lib_exit_ok LSt.
  (* [comment removed for export] *)
  Variable PHI : list byte -> Prop.
  Hypothesis LIokW : LCU.lib_iface_okU Lay scfg HI LSt PHI.
  (* [comment removed for export] *)
  Hypothesis Huid : (bv_unsigned uid < 2 ^ 32)%Z.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let LEN : Z := Z.of_nat (length fdata).
  Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
  Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
  Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
  Let CFG : Z := CFG fdata.
  Let PL : Z := PL fdata.
  Let CALLS : Z := CALLS fdata.
  Let payload : list byte := payload fdata.
  (* U/ twin of Pm6DrvF.v:96 -- [lh_vals] gained [rdraw] before [tid] and a
     trailing [inp].  Sibling U/Pm6DrvE_u5.v:92 already carries this form. *)
  Let lh_vals := lh_vals sp0 a0s path envv rdraw tid fdata inp.
  Let blk_facts := blk_facts L fdata CAP.
  (* Same class as :92 -- [lh1_k] gained a trailing [inp]; U/Pm6DrvE_u5.v:94 has it. *)
  Let lh1_k := lh1_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata inp CAP crC.
  Let cr1 := cr1 L fdata crC.
  Let relay_regs := relay_regs sp0 a0s path hw rdraw tid mem0 VM0 fs0 stdin0 fdata Hvsp Htid Hplen CAP HCAP.
  Let relay_agree := relay_agree sp0 a0s path hw rdraw fdata Hplen.
  Let relay_len := relay_len sp0 path fdata Hplen.
  Let relay_lo := relay_lo sp0 path fdata Hplen.
  Let relay_81 := relay_81 sp0 path fdata Hplen.
  Let relay_101 := relay_101 sp0 path fdata Hplen.
  (* as U/Pm6DrvE_u5.v:104: U/Pm6DrvD_u5's [hiv_facts'] discharges [sp0 a0s path envv uid hw
     rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME Hplen] *)
  Let hiv_facts' := hiv_facts' sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME Hplen.
  Let content_block' := content_block' sp0 a0s path hw rdraw fdata Hvsp.
  (* U/Pm6DrvE_u5's [SSP]/[LH2P] read its [lh_vals], which takes [inp] *)
  Let SSP := SSP scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata inp CAP Lay LSt.
  Let LH2P := LH2P scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata inp CAP Lay LSt.
  Let E := E fs0.

  Hypothesis Hok : (6 + CFG <= LEN)%Z.
  (* [comment removed for export] *)
  Hypothesis Hcr2 : credit_le (credit_scale CALLS (ll_credit Lay PL)) cr1.
  Hypothesis HPHI : PHI payload.
  Hypothesis HPHIu : lsu_phi Lay scfg HI LSt LIok payload.

  Lemma m2_but' : forall VM m', model_but_vm (model2 VM) m' -> m' = model2 (m_vmmaps m').
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$VM;R+^=$m';R+^>$H;R!2'^?!1/model2;#2#1#1").
Qed.
  Lemma PL_range' : (0 <= PL <= 67108857)%Z.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^40!1'^B/fdata;|?0000;!2'J0!1,81!1'^C/fdata;!3+;+M/CALLS;3|30;!1+3!1,45!2'^E6/path;}`m0!1'D7|;7ff;!1,8:!2'R9;!2'^E6/fdata;!1'D=|10;!1,8?|500;!1,8A!2'J,F@!2'^H@B!2'R,F@!1,8|46;!2'^H@F|600;!2'^L!1,4H/sp0;|40;!1,8J}5}2}1!1+W+M!2,^0+M,F!2,^2+M?!1,>+Y|22;!1,8S!2,^0+MT!2,^2+M,K!1,8|^13fff80000000;|20;!2,^2+MX|J0000000;!1,8Z!3,^U+M!3,^U+MVUQ!1,8|I1fffff9;!2'^V!2'^V#6T#7|@0000;!1'^W/fdata;vd&H;R!1'^@/fdata;!2+^A!2'R,F02&heq_CALLS;Rvd!2,0+M344&Hplen0;R!4'I!2+^D78<!<'L+@+M+^D'D'R'^F79!2,0+M98;!2,0+M;/Hplen;<&cstr;R!1'Q7!2'R,F9&cstr0;R!1'Q=!2'R,F>&__sat106;R!2'^G@B%~RC%~R!2'R,FB!2'J,FD&__sat105;R$Ha;RE$~R+^I!3'^J@B#2%Ha;RE%~R+^I!2'R,FD&__sat104;R!2'^G@F%~RC%~R!2'R,FF!2'J,FG&__sat103;R$Ha;RE$~R+^I!3'^J@F#2%Ha;RE%~R+^I!2'R,FG&__sat102;R!2'^KIK%~R!2'R,FI%~R!2'R,FK!2'R,F!2'^MIK&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,6+S!2,^N!3,^O+M!2,^P+ML!3,^O+M!2,^P+MM!3,^O+M!2,^P+MN!2,^P+M,G,^Q!1,:+S!1+2+S&__varmap;R!4,^R+M!4,^R+M!2,T+M#4#3!2,T+M#5#2!1,^S+M!1+U+M&__ff;R!8,VO'X+Y+Y,Z!7,^TO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MP,^1Q,^3!6,^6O'X+Y+Y,Z#7R!8,VO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+M!3,^4+MUQ,^1V,^3R!8,VO'X+Y+Y,Z!7,^TO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+M!2,^0+MW,^1!2,^2+MS,^3!6,^6O'X+Y+Y,Z#8R!8,VO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MV,^5Y,^3R!8,VO'X+Y+Y,Z!7,^TO'X+Y+Y,Z!6,^6O'X+Y+Y,Z#9!7,[O'X+Y+Y,Z!4,\+MY,^1!2,^0+M[,^3R!7,^TO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MP,^1\,^3!7,[O'X+Y+Y,Z!4,\+M\,^1!2,^0+M^0,^3!2'^7O,Z!4'^8#1#3vv!2,0+^9,^:!3+;+^9!2'^;#1#3,^:!3'^<+M,F#2%__p3;Rw%__p2;Rw%__p1;Rw%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+^A!2'R,F#2#5%~R!2'R!2'BT#3#2%~R!2+^A!2'RW#6#8%~R!2'J#4#6%~R!2+^A#;!2'R#7[!2+^A!2'R,F^1!2'R^1^0!<#1!2'R!1,8^2/CAP;!2'RI!1,8|^2000000000000;2I/CAP;0>#;/Hok;/Hsp;/HLEN;/HCAP;!2+^A!2'R,F^3!2'R^3^0").
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition IMG_PW : list (Z * Z) := [(0xcb428, 0xcb510); (0xdb590, 0xdb5a0); (0xfd7f8, 0xfdc00)]%Z.   (* [comment removed for export] *)
  Definition CPpw (a : Z) : Prop := ((0xcb428 <= a < 0xcb510) \/ (0xdb590 <= a < 0xdb5a0) \/ (0xfd7f8 <= a < 0xfdc00) \/ (bv_unsigned sp0 - 8388608 <= a))%Z.

  Lemma regions_pw : forall vals, vals_ev vals 0 = sp0 ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_PW [] (ENVb vals) CPpw (fun _ => True).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SaC0|600;!1,40!1+31!1,8|^13fff80000000;!2'^L1/sp0;!1,8|^2000000000000;|10;!1,86|508;!1,88!2'^H79!1,:!2+^Z+@+M!1,:+@!2+^Z+M+M!1,:=!1/ENVb;#3!2'^L1#1|50f;!1,8A!2'^H7B!1'^C/fdata;!3+;+M/CALLS;Dvd!2,0+MDE!1'^W/fdata;!3+;+M/PL;Gvd!2,0+MGH!1'^B/fdata;!3+;+M/CFG;Jvd!2,0+MJK|30;!1+3!1,4M!2'^EN/fdata;!1'DO!3+;+M/LEN;Pvd!2,0+MPQ!2'^EN/path;}`m0!1'DS|;7ff;!1,8V!2'RUW!4'I!2+^DSTX!<'L+@+M+^D'D'R'^FSU!2,0+MUTW!2,0+MW/Hplen;!1'QS!2'R,FU!1'QO!2'R,FP!2'J,F7!2'R,F7|500;!1,8^3!2'^G7^4!2'^H7^4%~R^1%~R!2'R,F^4!2'J,F^6$Ha;R^2$~R+^I!3'^J7^4#2%Ha;R^2%~R+^I!2'R,F^6!1,8|46;!2'^G7^:!2'^H7^:%~R^1%~R!2'R,F^:!2'J,F^<$Ha;R^2$~R+^I!3'^J7^:#2%Ha;R^2%~R+^I!2'R,F^<|40;!1,8^@!2'^K4^A%~R!2'R,F4%~R!2'R,F^A!2'R,F!2'^M4^A!1,:+S!1+2+S!2,T+M#2!1+U+M!1+W+M!2,^2+M,K!7,[^H'X+Y+Y,Z!4,\+M!2,^0+M3,^1^I,^3!1,>+Y!2,^0+M7!2'^7^H,Z!4'^8#1#3vv!2,0+^9,^:!3+;+^9!2'^;#1#3,^:!3'^<+M,F#2!2'^X#3,G!2'^L1!2'_2?,G!2'^G79%~R^1%~R!2'R,F9!2'J,F:$Ha;R^2$~R+^I!3'^J79#2!2'R,F:%Ha;R^2%~R+^I^T|47;!1,8^V!2'^G7^W!2'^H7^W%~R^1%~R!2'R,F^W!2'J,F^Y$Ha;R^2$~R+^I!3'^J7^W#2%Ha;R^2%~R+^I!2'R,F^Y!1,^S+M!2,_3+M!3,_1+M^L!1,4^V!3,_1+M^L!1,48!2,^0+M,F!1'_4^Y!2'^V::!2+^A!2'R_4_5^T!2'J#1:!2+^A!2'R_4#1_7!1'_5!2+^A!2'R_5#2!2'J#2:!2,^2+M6!6,^6^H'X+Y+Y,Z#5!1,8|C5b590;!2,^0+M_<!3,^4+M^I_:!1,8|C5b5a0;!2,^0+M_?|G000000;!1,8_A!2'B#2#3!1,8|C7d7f8;!2'B4#D!1,8|C7dc00;!1,8|C4b428;!1,8|C4b510;!1/ENVb;#6!2+^A!2'R_5#1_7!2'^L1#3!1/ENVb;#5!2'^L1!2'_2_L,G!1+1+M!3+;_N!2'_:#2;!2,5+M#1$e;R_N-1RN$o;R!1+1+Mw#12$~R+M+_<+^I!1,80!2'^H7_Q!2'R,F#1!2'^L1!2'_2_I#3!2'J#1#3!2'^L1!2'^X#6#3!3'_A+@#1<!2'^L1!2'^X#6#2|44;!2'^H7!1,8_Y!2+^A_S!2'J#1_Z!2'^L1!2'_2_L#2!4,_B+M+M#2#1!3'_A=`0'^[!4,_B+M+M_G_H!4,_B+M+M#3#2!3+;=`2`3!4,_B+M+M_<_?!4,_B+M+M_D_F!3,6=`6>!3,6=`5`7!3'_A=`3`8!1'^\#2!4,_B+M+M#4#3$e;R=-^ZRN$p;R!2+^Z+M+M+M#11$z;R+M$z;R+M#1!4,_B+M+M#5#4$e;R=-^ZRN$p;R!2+^Z+M+M+M#11$z;R+M$z;R+M#2!4,_B+M+M#6#5!2'R,F#2!2'R#3#1!2'R,F_G!2'R#1_R!2'R_G#1!2'J#1#2!2'R_H_R!2+^A`D!2'J#1_H%a;R+M%~R`G`:!2,^0+M_G!2'^G7_Q%~R^1%~R!2'R,F_Q!2'J,F_R$Ha;R^2$~R+^I!3'^J7_Q#2%Ha;R^2%~R+^I!2'R,F_R!2,^0+M_H!3,_1+M^L1!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+M`I,^1^I,^3!7,[^H'X+Y+Y,Z!4,\+M^I,^5`N,^3!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+M_=,^1^I,^3!7,[^H'X+Y+Y,Z!4,\+M^I,^5_@,^3!6,^6^H'X+Y+Y,Z#4!2+^A!2'R_<#2!2'J#2_?!2'R!2'^V4_B#?!2+_7!2+^A!2'R_D#?!2'J#?_F`T!3+;=`5`=!3'_A=`=`7!4,_B+M+M#7#6!4,_B+M+M#8#7!2'R,F_<!2'R_<#1!2'R_?_R!2+^A`[!2'J#1_?%a;R+M%~Ra0`:!2+^A!2'R_G#?!2'J#?_H!3+;=`6`X!3'_A=`X>!2'R,F_D!2'R_D#1!2'R_F_R!2+^Aa6!2'J#1_F%a;R+M%~Ra8`:!2,^0+M_D!2,^0+M_F!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+Ma:,^1^I,^3!7,[^H'X+Y+Y,Z!4,\+M^I,^5a;,^3!2'R,F#3!2'R#2_R!3'_A=`0>%~R2!1+1N!2'B#3!1'D#2!3+;+^9!4'_F'=#5!2'?1#4#3,^:$vals;R!1+22$P0;R!3+;2!2'^X#1,G/sp0;&Hsp';R/Hsp;!2+^A!2'R34!2'R45!E,^Y'=,G::;;<'^[>?'^\$~R+M+^Ivd!6'_02/sp0;$b;R2!2+^A!2'R3@!2'R@C&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat108;R!2'^G7B%~R^1%~R!2'R,FB!2'J,FC&__sat107;R$Ha;R^2$~R+^I!3'^J7B#2%Ha;R^2%~R+^I!2'R,FC&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R$__x1;R+M&__wit;R^D^E&__varmap;R^F^G&__ff;R!8,V^H'X+Y+Y,Z!7,^T^H'X+Y+Y,Z^J!7,[^H'X+Y+Y,Z!4,\+M^I,^1!2,^0+M5,^3^K!7,^T^H'X+Y+Y,Z^J!7,[^H'X+Y+Y,Z!4,\+M^I,^1!3,_1+M^L!1,4A,^3^M^N%__x1;R+M%~R!2+^A!2'R3#1!2'R#15!2+^A!2'R3#2!2'R#2C!2#14/Hsp;^O#2!2+^A!2'R3^P!2'R^PCvd&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat110;R^5^7&__sat109;R^8^9&__sat108;R^Q^R&__sat107;R^S^U&__sat106;R^X^Z&__sat105;R^[^\&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+M_1,^1!3,^U+M_2_2,^3!7,[^H'X+Y+Y,Z!4,\+M_3,^1_2,^3^M^N_6#1_6vd!6'_02/sp0;$b;R2%z;R+M%~R_8%~R_9!1'^\!2'B!2'^L1#4#3$z;R+M$Hz;R_8$Hnot;R_9vd&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat110;R^5^7&__sat109;R^8^9&__sat108;R^Q^R&__sat107;R^S^U&__sat106;R^X^Z&__sat105;R^[^\&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x2;R+M$__x1;R+M&__wit;R^D^E&__varmap;R!4,^R+M!2,T+M#3#2_0^G&__ff;R!8,V^H'X+Y+Y,Z!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+M_1,^1_:,^3_;^K!7,_6^H'X+Y+Y,Z!6,^6^H'X+Y+Y,Z#6!7,_6^H'X+Y+Y,Z!7,^T^H'X+Y+Y,Z!7,[^H'X+Y+Y,Z!4,\+M_=,^1_>,^3!7,[^H'X+Y+Y,Z!4,\+M_>,^5_@,^3!7,_6^H'X+Y+Y,Z!6,^6^H'X+Y+Y,Z#7!7,[^H'X+Y+Y,Z!4,\+M!3,^U+M^I!2,^0+M_B,^1_>,^3^M^N%__p3;Rw%__p2;Rw%__p1;Rw%__x2;R+M%__x1;R+M%~R!2+^A!2'R_4#2#3!2+_7#5!2+_7!2+^A!2'R_<_C!2'J_C_?!2+_7#6!2'R!2'^V#2_B_C!6#1!2+^A!2'R_D_E!2'J_E_F!2+^A!2'R_G_E!2'J_E_H!2'J#D:#D4#C!1'^\!2'B4#3^O#2%z;R+M%~R_8%~R_9!1'^\!2'B!2'^L1!2'_2_I,G#3vd!6'_02/sp0;$b;R2%z;R+M%~R_J!2+_7!1'^\!2'B_K#2+^I$z;R+M$Hz;R_J!3,_8!1'^\!2'B4#2+^I,_9^O#2%z;R+M%~R_J!2+_7!1'^\!2'B_M#2+^Ivd$i;R+@$nb;R+M$Hf;R_O&H;R!6'_;_N!2'_:#3;_P,_9!2,5+M#2#1+_<!2'_=!2+^A!2'R!2'B!2'^L1!2'^X#7#4#3_R%z;R+M%~R!2+^A_S!2'J#1#4!1'^\!2'B!2'^L1!2'^X#9#6#2#1%i;R+@%nb;R+M%~R_O!2+^A!2'R!2'B_T#2_R%z;R+M%~R!2+^A_S_U!1'^\!2'B!2'^L1!2'_2!1/ENVb;#8#5#2vd$v;R+@$b;R+M$Hf;R_Ovd$H;R!3+;+_>!2'_?_V#2,_@&H0;R!6'_;_N!2'_:#4;_P,_9!2,5+M#3#2+_<!2'_=+_<#1!2'R_V#2%v;R+@%b;R+M%~R_O!2'R_T#2vd!6'_02/sp0;$b;R2%i;R+@%~R_W!2+^A!2'R_K_X!2+^A!2'R!2'B_X_Z_R%z;R+M%~R_[!1'^\!2'B!2'^L1!2'^X#8#4#2$i;R+@$H;R_W!2'_=!2+^A!2'R4!2'^L1!2'^X#5#2!2+^A!2'R!2'B!2'^L1!2'^X#5#2_Z_R%z;R+M%~R_[!1'^\!2'B!2'^L1!2'^X#7#4#2#1^O#2%i;R+@%~R_W!2+^A!2'R_M_\!2+^A!2'R!2'B_\_Z_R%z;R+M%~R_[!1'^\!2'B!2'^L1!2'_2!1/ENVb;#7#4#2vd$lo;R+M$hi;R+M$Hin;R`1!6'_C`4`9!2+^A!2'R,F#3!2+^A!2'R#2_R%a;R+M%~R!2+^A!2'R#4#1!2'J#1#3`:$~R`4!1$E1;R!3+;=`2`;&H;R!6'_D=+M`<`2`=#1!3+;+M_H#4!1&H;R!6'_D=+M`>`2`?#2!3+;+M_G#6!1$H;R!3+;+M_G#7!6'_;+M_G$lo;R+M%~R!3+;+M_H#8!2+^A`@!2+^A!2'R#9_R%a;R+M%~R!2+^A`A!2'J#1#:`:$H;R!3+;+M_H#7!6'_;+M_H$hi;R+M!2+^A`B!2+^A`C%a;R+M%~R!2+^A`D`E`:!4,_E`B!2+^A`F`H&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+M_3,^1`I,^3^M^N`B#1!4,_E`F`H&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat108;R^5^7&__sat107;R^8^9&__sat106;R`J`K&__sat105;R`L`M&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+M`N,^1`O,^3^M^N`F#1$a;R+M$Ha;R`Gvd&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R$__p1;Rw$__x1;R+M&__wit;R^D^E&__varmap;R^F^G&__ff;R!8,V^H'X+Y+Y,Z`P^K!7,_6^H'X+Y+Y,Z`P!7,_6^H'X+Y+Y,Z`Q`R^M^N%__p1;Rw%__x1;R+M%~R`G!2+_7!2+^A!2'R_G#2!2'J#2_H!2+_7`S#3!3#1`U#?#>`:#8#1#8#1#1#1#1$~R`9!1$H;R!3'_A=`;`8!6'_C`V`W!2+^A!2'R,F#5!2+^A!2'R#4_R%a;R+M%~R!2+^A!2'R#6#1!2'J#1#5`:$~R`V!1$E1;R!3+;=`5`?&H;R!6'_D=+M`<`5`X#1!3+;+M_?#6!1&H;R!6'_D=+M`>`5`Y#2!3+;+M_<#8!1$H;R!3+;+M_<#9!6'_;+M_<$lo;R+M%~R!3+;+M_?#:!2+^A`@!2+^A!2'R#;_R%a;R+M%~R!2+^A`A!2'J#1#<`:$H;R!3+;+M_?#9!6'_;+M_?$hi;R+M!2+^A`Z!2+^A`C%a;R+M%~R!2+^A`[`E`:!4,_E`Z!2+^A`\a1&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+M_3,^1_=,^3^M^N`Z#1!4,_E`\a1&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat108;R^5^7&__sat107;R^8^9&__sat106;R`J`K&__sat105;R`L`M&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+M_@,^1`O,^3^M^N`\#1$a;R+M$Ha;Ra0vd&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R$__p2;Rw$__p1;Rw$__x1;R+M&__wit;R^D^E&__varmap;R^F^G&__ff;R!8,V^H'X+Y+Y,Z`Q^K!7,_6^H'X+Y+Y,Z`R!7,_6^H'X+Y+Y,Z`Q_;^M^N%__p2;Rw%__p1;Rw%__x1;R+M%~Ra0!2+_7#3!2+_7`S#4!4#1`Ua2#?#>`:#:#1#:#1#1#1#1$~R`W!1$H;R!3'_A=`?`7!6'_Ca3a4!2+^A!2'R,F#7!2+^A!2'R#6_R%a;R+M%~R!2+^A!2'R#8#1!2'J#1#7`:$~Ra3!1$E1;R!3+;=`6`Y&H;R!6'_D=+M`<`6!4,_B+M+M#9#8#1!3+;+M_F#8!1&H;R!6'_D=+M`>`6!4,_B+M+M#:#9#2!3+;+M_D#:!1$H;R!3+;+M_D#;!6'_;+M_D$lo;R+M%~R!3+;+M_F#<!2+^A`@!2+^A!2'R#=_R%a;R+M%~R!2+^A`A!2'J#1#>`:$H;R!3+;+M_F#;!6'_;+M_F$hi;R+M!2+^Aa5!2+^A`C%a;R+M%~R!2+^Aa6`E`:!4,_Ea5!2+^Aa7a9&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+M_3,^1a:,^3^M^Na5#1!4,_Ea7a9&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat108;R^5^7&__sat107;R^8^9&__sat106;R`J`K&__sat105;R`L`M&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R&__wit;R^D^E&__varmap;R_0^G&__ff;R!7,[^H'X+Y+Y,Z!4,\+Ma;,^1`O,^3^M^Na7#1$a;R+M$Ha;Ra8vd&heq_CALLS;RFE&heq_PL;RIH&heq_CFG;RLK&heq_LEN;RRQ&Hplen0;RYX&cstr;RZ[&cstr0;R\^0&__sat106;R^5^7&__sat105;R^8^9&__sat104;R^;^=&__sat103;R^>^?&__sat102;R^B^C&__arith;R$__p2;Rw$__p1;Rw$__x1;R+M&__wit;R^D^E&__varmap;R^F^G&__ff;R!8,V^H'X+Y+Y,Za<^K!7,_6^H'X+Y+Y,Z`R!7,_6^H'X+Y+Y,Z`Q!7,_6^H'X+Y+Y,Za<_;^M^N%__p2;Rw%__p1;Rw%__x1;R+M%~Ra8!2+_7#3!2+_7`S!2+_7!2+^A!2'R_D#2!2'J#2_F#4!4#1`Ta2#?#>`:#<#1#<#1#1#1#1$~Ra4!1$H;R!3'_A=`Y>!2'_=!2+^A!2'R,F#9!2+^A!2'R#8_R%a;R+M%~R!2+^A!2'R#:#1!2'J#1#9`:#1#1#1#1#1#1#1%lo;R+M%hi;R+M%~R`1!2+^Aa=!2+^Aa>%a;R+M%~R!2+^A!2'R#4#1_U`:vd$lo;R+M$hi;R+M$H;Ra?!2'_=!2+^A!2'R,F#3!2+^A!2'R#2_R%Mx;Ra@%d;R+M%m;R+@%~R!2'R#6#2%~R!2'RaA#6aB#1%lo;R+M%hi;R+M%~Ra?!2+^Aa=!2+^Aa>%Mx;Ra@%d;R+M%m;R+@%~R!2'R#6#2%~R!2'RaA#6aB").
Qed.

  Lemma mem_pw_frame : forall vals M log (a : Z),
    vals_ev vals 0 = sp0 -> log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_PW log = true ->
    (0 <= a)%Z -> ~ CPpw a ->
    mem_denot (ENVb vals) M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^=0|600;!1,40!1+31|30;!1+3!1,43|10;!1,85!1,8|508;!2'^H67!1,:!2+^Z+@+M!1,:+@!2'R,F#3!1,8|^13fff80000000;!2'^L1/sp0;!2'R<=!1,8|^2000000000000;!2'R=?!1'^C/fdata;!3+;+M/CALLS;A!1'^W/fdata;!3+;+M/PL;C!1'^B/fdata;!3+;+M/CFG;E!2'^E4/fdata;!1'DG!3+;+M/LEN;H!2'^E4/path;}`m0!1'DJ|;7ff;!1,8M!2'RLN|500;!1,8P!2'J,F6!2'^H6Q!2'R,F6!1,80!2'^H6U!1,8|46;!2'^H6W|40;!1,8Y}6}3!1,^S+M!1+W+M|22;!2,^2+M^2!1,>+Y!1,8|C5b590;!2,^2+M,K!1,8|C5b5a0;!1,8|C7d7f8;!1,8|C7dc00;|G000000;!1,8^:!7,[^1'X+Y+Y,Z!4,\+M!2,^0+M,F,^1^6,^3$vals;R!1+22$M;R%~R2!1+14$log;R!1+2+_G$a;R+M$P0;R!3+;2!2'^X#4,G/sp0;$Hlog;R!3+;+^9!7'_H,G889:'^[#3,^:$Ha;R;$Hn;R!1'_5!1'^\#4&Hsp';R/Hsp;!2+^A>@!C'_I'=,G8899:'^[!1/ENVb;#9'^\$~R+M+^I!1,:!2+^Z+M+M!2'_J#9#5#8#7#6#4&heq_CALLS;Rvd!2,0+MABB&heq_PL;Rvd!2,0+MCDD&heq_CFG;Rvd!2,0+MEFF&heq_LEN;Rvd!2,0+MHII&Hplen0;R!4'I!2+^DJKO!<'L+@+M+^D'D'R'^FJL!2,0+MLKN!2,0+MN/Hplen;O&cstr;R!1'QJ!2'R,FL&cstr0;R!1'QG!2'R,FH&__sat110;R!2'^G6Q%~RR%~R!2'R,FQ!2'J,FS&__sat109;R$Ha;RT$~R+^I!3'^J6Q#2%Ha;RT%~R+^I!2'R,FS&__sat108;R!2'^G67%~RR%~R!2'R,F7!2'J,F8&__sat107;R$Ha;RT$~R+^I!3'^J67#2%Ha;RT%~R+^I!2'R,F8&__sat106;R!2'^G6U%~RR%~R!2'R,FU!2'J,FV&__sat105;R$Ha;RT$~R+^I!3'^J6U#2%Ha;RT%~R+^I!2'R,FV&__sat104;R!2'^G6W%~RR%~R!2'R,FW!2'J,FX&__sat103;R$Ha;RT$~R+^I!3'^J6W#2%Ha;RT%~R+^I!2'R,FX&__sat102;R!2'^K=Z%~R!2'R,F=%~R!2'R,FZ!2'R,F!2'^M=Z&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x2;R+M$__x1;R+M&__wit;R!3,6+S!2,^N!3,^O+M!2,^P+M[!3,^O+M!2,^P+M\!2,^P+M,G,^Q!1,:+S!1+2+S&__varmap;R!4,^R+M!4,^R+M^0#3!2,T+M#3#2^0!1+U+M&__ff;R!8,V^1'X+Y+Y,Z!7,^T^1'X+Y+Y,Z!6,^6^1'X+Y+Y,Z#5!7,[^1'X+Y+Y,Z!4,\+M^3,^1!2,^0+M?,^3^4!8,V^1'X+Y+Y,Z!6,_K^1'X+Y+Y,Z!7,_6^1'X+Y+Y,Z!6,^6^1'X+Y+Y,Z#6!7,_6^1'X+Y+Y,Z!7,^T^1'X+Y+Y,Z!7,[^1'X+Y+Y,Z!4,\+M!2,^0+M^5,^1^6,^3!7,[^1'X+Y+Y,Z!4,\+M^6,^5!2,^0+M^7,^3!7,_6^1'X+Y+Y,Z!7,^T^1'X+Y+Y,Z!7,[^1'X+Y+Y,Z!4,\+M!2,^0+M^8,^1^6,^3!7,[^1'X+Y+Y,Z!4,\+M^6,^5!2,^0+M^9,^3!7,[^1'X+Y+Y,Z!4,\+M!3,^U+M^3!2,^0+M^;,^1^6,^3^4!8,V^1'X+Y+Y,Z^<^4!8,V^1'X+Y+Y,Z!7,^T^1'X+Y+Y,Z!7,[^1'X+Y+Y,Z!4,\+M!2,^0+M<,^1^3,^3!6,^6^1'X+Y+Y,Z#7^4!7,^T^1'X+Y+Y,Z^<!7,[^1'X+Y+Y,Z!4,\+M^6,^5!3,_1+M!2,^0+M61,^3!2'^7^1,Z!4'^8#1#3vv!2,0+^9,^:!3+;+^9!2'^;#1#3,^:!3'^<+M,F#2%__p3;Rw%__p2;Rw%__p1;Rw%__x2;R+M%__x1;R+M%~R!2+^A#3!2'R#2?%~R%~R!2+_7#5!2+_7!2+^A!2'R^5#2!2'J#2^7!2+_7!2+^A!2'R^8#2!2'J#2^9!2'R!2'^V#3^;#2+_<%~R;%~R!2+^A!2'R<#5#8!2+^A!2'R,F#5!2'J#5V!9#1@!2+^A!2'R!1,8|C4b428;#G!2'J#G!1,8|C4b510;>=#G#B#C#D/Hsp;#2").
Qed.

  (* [comment removed for export] *)
  Lemma block_pw : forall vals M log LB cr VM g,
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_PW log = true -> log_below_b 0 0xfe000 log = true ->
    (hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot (ENVb vals) M log) VM)
    /\ (above M -> above (mem_denot (ENVb vals) M log))
    /\ (ls_ok LSt g M -> ls_ok LSt g (mem_denot (ENVb vals) M log))
    /\ (forall (a : Z) n bs, hz sp0 a (Z.of_nat n) ->
          rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS (mem_denot (ENVb vals) M log) (Z_to_bv 64 a) n = Some bs).
  Proof.
    intros vals M log LB cr VM g P0 Hlog Hbelow. pose proof Hsp as Hsp'.
    (* [RO] now names the section's [Context {RO : ReaderOn}]: Error: RO is already used *)
    pose proof (dl_ro L sp0 DL) as ROd. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    assert (FR : forall a, (0 <= a)%Z -> ~ CPpw a -> mem_denot (ENVb vals) M log (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      by (intros; apply mem_pw_frame; assumption).
    assert (AB : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem_denot (ENVb vals) M log a = M a).
    { intros a Ha. apply (mem_denot_above (ENVb vals) M log 0%nat 0xfe000 a Hbelow); cbn [ev ENVb ENV]; rewrite ?P0; lia. }
    split; [|split; [|split]].
    - intros HH. apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
      + intros a Ha Hpriv. destruct (Z.le_gt_cases (bv_unsigned sp0) a) as [Hup|Hdown].
        { rewrite <- (u_small a) in Hup by lia. exact (AB (Z_to_bv 64 a) Hup). }
        apply FR; [lia|]. unfold CPpw.
        destruct Hpriv as [[A [_ B]]|A].
        * rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
          assert (~ (0xcb000 <= a < 0xfe000) \/ hl_alloc_static L a)%Z as [C|C]
            by (destruct (Z_lt_ge_dec a 0xcb000); [left; lia|]; destruct (Z_lt_ge_dec a 0xfe000); [|left; lia];
                right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
          -- lia.
          -- apply STA in C. lia.
        * apply ROd in A. lia.
      + intros x Hx. exact (mem_denot_grows (ENVb vals) M log x Hx).
    - intros HA a Ha. rewrite AB by exact Ha. apply HA. exact Ha.
    - intros Hls. apply (lsu_frame Lay scfg HI LSt LIok g M _ Hls).
      + intros a Ha Hf. apply FR; [lia|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpw. lia.
      + intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
        rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | unfold CPpw; lia].
      + intros a Ha Hi. destruct Hi as [(iv & Hin & Hr) | Hi].
        * apply FR; [lia|]. apply (dll_initc Lay L DLL) in Hin. unfold CPpw. lia.
        * rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. rewrite <- (u_small a) in Hi by lia. apply AB. lia.
    - intros a n bs (Ha1 & Ha2 & Ha3) HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; [lia | unfold CPpw; lia].
  Qed.

  Lemma sw_pw : forall M M' (su : Z) bufp bufsz LB cr VM g,
    sw_post M su 0xcb428 bufp bufsz M' -> (bv_unsigned sp0 - 8388608 + 112 <= su)%Z -> (su <= bv_unsigned sp0)%Z ->
    (hi_heap HI LB cr M VM -> hi_heap HI LB cr M' VM)
    /\ (above M -> above M')
    /\ (ls_ok LSt g M -> ls_ok LSt g M')
    /\ (forall (a : Z) n bs, hz sp0 a (Z.of_nat n) ->
          rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs).
  Proof.
    intros M M' su bufp bufsz LB cr VM g HP Hlo Hhi. pose proof Hsp as Hsp'.
    (* [RO] now names the section's [Context {RO : ReaderOn}]: Error: RO is already used *)
    pose proof (dl_ro L sp0 DL) as ROd. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    assert (FR : forall a, (0 <= a < 2 ^ 64)%Z -> ~ CPpw a \/ ((0xcb428 <= a < 0xcb448) \/ (0xcb458 <= a < 0xcb460) \/ (0xcb468 <= a))%Z /\ (a < su - 112 \/ su <= a)%Z ->
                 M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hc. apply (swp_agree _ _ _ _ _ _ HP); rewrite u_small by lia; unfold CPpw in Hc; lia. }
    split; [|split; [|split]].
    - intros HH. apply (hio_frame L scfg HI HIok LB cr M M' VM HH).
      + intros a Ha Hpriv. apply FR; [exact Ha|]. unfold CPpw.
        destruct Hpriv as [[A [_ B]]|A].
        * rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
          assert (~ (0xcb000 <= a < 0xfe000) \/ hl_alloc_static L a)%Z as [C|C]
            by (destruct (Z_lt_ge_dec a 0xcb000); [left; lia|]; destruct (Z_lt_ge_dec a 0xfe000); [|left; lia];
                right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
          -- left. lia.
          -- apply STA in C. left. lia.
        * apply ROd in A. lia.
      + exact (swp_grows _ _ _ _ _ _ HP).
    - intros HA a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; apply HA; exact Ha | lia | right; lia].
    - intros Hls. apply (lsu_frame Lay scfg HI LSt LIok g M M' Hls).
      + intros a Ha Hf. apply FR; [exact Ha|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpw. left. lia.
      + intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
        rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | unfold CPpw; left; lia].
      + intros a Ha Hi. apply FR; [exact Ha|]. destruct Hi as [(iv & Hin & Hr) | Hi].
        * apply (dll_initc Lay L DLL) in Hin. unfold CPpw. left. lia.
        * rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. right. lia.
    - intros a n bs (Ha1 & Ha2 & Ha3) HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; [lia | unfold CPpw; left; lia].
  Qed.

  Lemma init_facts : forall vals M,
    vals_ev vals 0 = sp0 -> vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv inp -> vals_ev vals 5 = tid ->
    know_ok RSEGS (ENVb vals) M knLB1 -> above M ->
    lib_init_facts Lay (bv_unsigned (auxvp sp0 a0s path envv)) (bv_unsigned uid) (bv_unsigned (rnd sp0 a0s path envv inp)) (bv_unsigned tid)
                   (CANZ rdraw) (bv_unsigned hw) M.
  Proof.
    intros vals M P0 P3 P4 P5 HK HA. pose proof Hsp as Hsp'.
    destruct (auxvp_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as [AV1 AV2].
    destruct (rnd_u sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Htid inp mbase entry ME) as (RN1 & RN2 & RN3 & RN4).
    (* 727298f3: [RefLayout]'s bounds are section lemmas over the launch, and
       [PropExec.build_stack_bytes_within_span] is retired (its span is no longer an
       upper bound on the kernel's block).  Same shape as [Pm6HeapBridge]'s AOB and
       [Pm6MainEntry]'s Hl: [lay_bsb_len] carries [StepTac.bsb_bound]. *)
    destruct (main_entry_inp inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME)
      as (Eav & Eev & _ & _ & Hvl & brk & Hlau).
    assert (Hva' : valid_argv (in_argv inp)) by (rewrite Eav; exact Hva).
    assert (Hve' : valid_envp (in_envp inp)) by (rewrite Eev; exact Hve).
    assert (AOB : (auxv_off (in_argv inp) (in_envp inp) + auxv_size (kb_rseq (in_kernel inp)) + 16
                   <= length (entry_stack_image inp mbase RPH entry sp0 rdraw))%nat)
      by (first
            [ solve [eapply auxv_off_bound; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | exact Hal
                                                  | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]]
            | (unfold entry_stack_image; rewrite length_build_stack_bytes; cbn [launch_auxv la_rseq];
               unfold auxv_off, block_head_size, block_items; lia) ]).
    assert (BSB : (Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) <= 2101782)%Z)
      by (eapply lay_bsb_len; first [exact Hva' | exact Hve' | exact Hvl | exact Hlau | (unfold sp_window_lo; lia) | (unfold sp_window_hi; lia)]).
    pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv inp)) as RNR.
    pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (CANZ_range rdraw) as CR.
    assert (KC : forall addr, kblob_find knLB1 (ELit 0) addr = Some (ELit 8, 2%nat) ->
                 rdn RSEGS M (Z_to_bv 64 addr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (CANZ rdraw)))).
    { intros addr Hc. unfold CANZ. rewrite Z_to_bv_bv_unsigned.
      pose proof (kblob_rdn RSEGS (ENVb vals) M knLB1 (ELit 0) addr (ELit 8) 2%nat HK Hc) as R.
      unfold adenot, v_addi in R. cbn [a_base a_off edenot eb ENVb ENV blobs_ev nth app blobs0] in R.
      rewrite length_word_to_le_bytes, u_small in R by lia. rewrite Z.add_0_l in R. exact R. }
    (* LibIface.lib_init_facts lost its two auxv conjuncts (the __auxv cell bundle and the
       20 auxv words; Main's ruling, option D): false at LPS 75d69e00 and read by no
       consumer.  OLD: [(dll_auxvp Lay L DLL)] in this rewrite and five more splits. *)
    unfold lib_init_facts. rewrite (dll_heap Lay L DLL), (dl_segs L sp0 DL), (dl_sptop L sp0 DL), (dll_init_img Lay L DLL),
      (dll_td_self Lay L DLL), (dll_td_tid Lay L DLL), (dll_td_locale Lay L DLL), (dll_locale Lay L DLL), (dll_td_canary Lay L DLL),
      (dll_guard Lay L DLL), (dll_init_cells Lay L DLL). cbv zeta. unfold cellz.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]].
    - intros iv a Hin Hr.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; cbn [fst snd] in Hr.
      (* the first cell is (0x10000, 0xcb538) ([dll_init_img]): ask for a [KImg] covering all of it *)
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0x10000 0xbb538) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xdb591 0x3) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xdb595 0x195b) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd018 0x20) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd058 0x8) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd064 0x4) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd070 0x8) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd080 0xf8) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd180 0xf8) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd2a3 0x1) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
      + pose proof (know_nth RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd378 0x4) in exact q) _ HK eq_refl) as KI.
        cbn [kentry_ok] in KI. destruct KI as (_ & _ & KI). apply KI. lia.
    - krd_solve HK.
    - krd HK 0xdcf68%Z 4%nat Htc. rewrite Htc. cbn [ev ENVb ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - lia.
    - krd_solve HK.
    - intros k Hk. rewrite (kimg_rdn RSEGS _ _ knLB1 ltac:(let q := kidx knLB1 (is_kimg_cov 0xfd2d8 48) in exact q) _ _ (0xfd2d8 + 8 * Z.of_nat k) 8 HK eq_refl) by lia.
      apply locale_img. exact Hk.
    - apply KC. vm_compute. reflexivity.
    - apply KC. vm_compute. reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
      -
      intros c Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; krd_solve HK.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* Proof, old beside new: the recorded proof term is replaced by a text proof at LPS 727298f3,
     [Pm6DrvFW.iter1w]'s with this file's addresses: [lib_sitew] of [Pm6DrvLibLW_u5] for [lib_site]
     (its premise [PHI payload] is the section's [HPHI]; its continuation gives [PHI payload] again),
     [lsu_init] for [liof_init] ([LIok] is a [lib_iface_ok_u]), and the trace moved to [iter1]'s by
     [SpecG.iter1_guard_eq]. *)
  Lemma iter1w : forall K, K [] -> SSP CALLS 0 K -> lh1_k (t_emit (W 1 [b48]) (t_guard (PHI payload) (t_emit (W 1 [b10]) K))).
  Proof.
    intros K HK0 HSS. unfold lh1_k, Pm6DrvD_u5.lh1_k.
    intros fx' vals R M VM A1 PTR OWN LB (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
           HR HK HA HBLK HC HPAY HH HFP.
    fold payload in HPAY. fold PL CALLS in P81. fold PL in P79. fold CFG in P73. fold cr1 in HH.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hiv_facts' vals P3 P4) as HIV.
    destruct HBLK as [HBR REST]. unfold Pm6DrvD_u5.blk_facts in REST. fold PL in REST.
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
    pose proof PL_range' as HPr. pose proof (payload_len fdata) as PLN. fold PL in PLN. fold payload in PLN.
    pose proof (dll_credit_pos Lay L DLL PL ltac:(lia)) as [CP1 CP2]. pose proof (CALLS_range fdata) as HKr. fold CALLS in HKr.
    assert (HKe : t_emit (W 1 [b48]) (t_guard (PHI payload) (t_emit (W 1 [b10]) K)) []) by apply t_emit_has_nil.

    run_blockT_keep scr0 102%nat.
    lazymatch type of EQM with _ = mem_denot ?E _ _ => change E with (ENVb vals) in EQM end.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals mp lg LB cr1 VM (ls_g0 LSt) P0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH) as HH0. pose proof (BA HA) as HA0.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC) as HC0.
    assert (HPAY0 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY). }
    clear BH BA BL BRd EQM HH HA HC HPAY. rename HH0 into HH. rename HA0 into HA. rename HC0 into HC. rename HPAY0 into HPAY.

    pose proof (lsu_init Lay scfg HI LSt LIok _ _ _ _ _ _ M0 (init_facts vals M0 P0 P3 P4 P5 HK HA)) as Hls0.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (lib_sitew scfg L HI HIok sp0 Hsp' Hal' DL Lay LSt DLL PHI LIokW vals _ srLB knLB1 Rc M0 (model2 VM) LB cr1 (ls_g0 LSt) (-208)
              [(48%nat, 65536%Z)] [] PTR 0x3a50c payload (t_emit (W 1 [b48]) (t_guard (PHI payload) (t_emit (W 1 [b10]) K))));
      [ exact HR | exact HK
      | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
      | exact P0 | exact HIV | vm_compute; reflexivity
      | regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
      | lia | reflexivity
      | regv HR (1 : reg); reflexivity | lia | reflexivity
      | regv HR (3 : reg); reflexivity | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P82
      | regv HR (11 : reg); cbn [edenot ev ENVb ENV]; rewrite P79, PLN; f_equal; lia
      | rewrite PLN; lia
      | destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)];
        [ left; split; [rewrite PLN; lia | exact HPTR] | right; split; [rewrite PLN; lia|]; subst LB PTR; left; rewrite PLN; f_equal; lia ]
      | exact HPAY
      | rewrite PLN; replace (Z.of_nat (Z.to_nat PL)) with PL by lia; exact (credit_le_head sp0 Hsp' CALLS (ll_credit Lay PL) cr1 ltac:(lia) CP1 CP2 Hcr2)
      | exact Hls0 | exact HFP
      | exact HH | reflexivity | reflexivity | reflexivity
      | intros i nb Hf; cbn in Hf;
        destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                         rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
                                         destruct REST as [(_ & _ & _ & ->) | (_ & _ & _ & _ & ->)]; [left | right; left]; reflexivity
                                       | discriminate]
      | intros v b Hf; discriminate
      | exact HKe | exact HPHI | ]
    end.
    clear HR HK Hls0.
    intros fx2 R' M' model' g' cr' vals' E' HL' HPHI2 HR HK HH' HBUT Hls' HFP' Hcr' HAB HBLK' HIMG. subst vals' E'.
    apply (srz_conseq _ _ _ (t_emit (W 1 (zero_lines 1)) K)); [| exact (iter1_guard_eq (PHI payload) K HPHI2 HK0)].
    rewrite (m2_but' _ _ HBUT). rewrite (m2_but' _ _ HBUT) in HH'. cbn [m_vmmaps Pm6DrvB_u5.model2 mkModelE with_net with_creds mkModel m_vm vmst_maps] in HH'.
    set (VM2 := m_vmmaps model') in *. clearbody VM2.
    rewrite HL in HR, HL'. change (keep_lib (-208) [(48%nat, 65536%Z)] [] knLB1) with knLr1 in HK.
    set (vals2 := vals ++ junk_vals R') in *.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR, HK.
    assert (XL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals2 q = x).
    { intros q x Hq Hx. subst vals2. rewrite vals_ev_app_l by (rewrite HL; exact Hq). exact Hx. }
    pose proof (XL 0%nat _ ltac:(lia) P0) as X0. pose proof (XL 3%nat _ ltac:(lia) P3) as X3. pose proof (XL 4%nat _ ltac:(lia) P4) as X4.
    pose proof (XL 5%nat _ ltac:(lia) P5) as X5. pose proof (XL 48%nat _ ltac:(lia) P48) as X48.
    pose proof (hiv_facts' vals2 X3 X4) as HIV2.
    assert (HA2 : above M') by (intros a Ha; rewrite HAB by exact Ha; apply HA; exact Ha).
    assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply HBLK'; [lia|].
      exists (A1, CAP). split; [destruct REST as [(_ & _ & _ & ->)|(_ & _ & _ & _ & ->)]; [left|right; left]; reflexivity|]. cbn [fst snd]. lia. }
    assert (HPAY2 : rdn RSEGS M' (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4).
        rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply HBLK'; [lia|].
        exists (OWN, PL). subst LB PTR. split; [left; reflexivity|]. cbn [fst snd]. lia. }
    clear HA HC HPAY HAB HBLK' HIMG HH.

    clear M0. run_blockT_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals2 mp lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH') as HH0. pose proof (BA HA2) as HA0. pose proof (BL Hls') as Hls0'.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC0.
    assert (HPAY0 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear BH BA BL BRd EQM HH' HA2 Hls' HC2 HPAY2. rename HH0 into HH'. rename HA0 into HA2. rename Hls0' into Hls'. rename HC0 into HC2. rename HPAY0 into HPAY2.
    clear M'. rename M0 into M'.

    run_blockP_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_pw vals2 M' lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH') as HH1. pose proof (BA HA2) as HA1. pose proof (BL Hls') as Hls1.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC1.
    assert (HPAY1 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear BH BA BL BRd EQM HH' HA2 Hls' HC2 HPAY2.

    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      eapply (rz_ioctl_winsz RSEGS scfg Rc _ Mc (model2 VM2) ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | reflexivity | reflexivity
      | regv HR (17 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | reflexivity
      | reflexivity
      | regv HR (11 : reg); reflexivity
      | ]
    end.
    rewrite v_addi_pc4 by lia. change (0xb35dc + 4)%Z with 0xb35e0%Z.
    pose proof (regs_set_a0 (ENVb vals2) _ _ (errno_ret ENOTTY) (ELit 18446744073709551591) HR ltac:(apply bv_eq; reflexivity)) as HR1.
    clear HR. rename HR1 into HR.

    run_blockP_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals2 mp lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH1) as HH2. pose proof (BA HA1) as HA2. pose proof (BL Hls1) as Hls2.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC1) as HC2.
    assert (HPAY2 : rdn RSEGS M1 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY1). }
    clear BH BA BL BRd EQM HH1 HA1 Hls1 HC1 HPAY1.

    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      assert (HSC : stdio_call 134 sr kn = Some scP) by vmc_refl;
      pose proof (stdio_call_sound_fr scfg vals2 _ sr kn Rc Mc (model2 VM2) scP [Z_to_bv 8 48] [Z_to_bv 8 10] K ltac:(rdr) HR HK
                    (eq_trans (f_equal (fun n => stdio_call n sr kn) HL') HSC)) as Hsc;
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scP length app Z.of_nat Pos.of_succ_nat Pos.succ] in Hsc;
      unfold W; cbn [map zero_lines app];
      apply Hsc; clear Hsc HSC;
      [ cbn [edenot]; rewrite !u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; reflexivity
      | cbn [edenot]; lit_u; reflexivity
      | cbn; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite X0; rewrite ?u_small by lia; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite X0; rewrite ?u_small by lia; lia
      | cbn [edenot]; rewrite ?u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; krd_solve HK
      | cbn [edenot]; rewrite (kimg_rdn RSEGS _ _ kn ltac:(let q := kidx kn (is_kimg_cov 0x10e44 1) in exact q) _ _ 0x10e44 1 HK eq_refl) by (cbn; lia);
        apply nl_img
      | reflexivity
      | reflexivity
      | reflexivity
      | exact HK0
      | ]
    end end.
    clear HR HK.
    intros RW MW HR HK HP.
    rewrite edenot_add_lit in HP. unfold adenot, v_addi in HP. cbn [a_base a_off edenot ev ENVb ENV] in HP. rewrite X0 in HP.
    destruct (sw_pw M1 MW _ _ _ LB cr' VM2 g' HP ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; lia)) as (SH & SA & SL & SRd).
    pose proof (SH HH2) as HH3. pose proof (SA HA2) as HA3. pose proof (SL Hls2) as Hls3.
    pose proof (SRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC3.
    assert (HPAY3 : rdn RSEGS MW (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (SRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear SH SA SL SRd HP HH2 HA2 Hls2 HC2 HPAY2.
    try rewrite HL' in HR. try rewrite HL' in HK.
    set (vals3 := vals2 ++ junk_vals RW) in *.
    assert (HL3 : length vals3 = 166%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
    change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR, HK.
    assert (YL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals3 q = x).
    { intros q x Hq Hx. subst vals3. rewrite vals_ev_app_l by (rewrite HL'; lia). apply XL; assumption. }
    pose proof (YL 0%nat _ ltac:(lia) P0) as Y0. pose proof (YL 3%nat _ ltac:(lia) P3) as Y3. pose proof (YL 4%nat _ ltac:(lia) P4) as Y4.
    pose proof (hiv_facts' vals3 Y3 Y4) as HIV3.

    run_blockR_keep scr0 166%nat.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals3 mp lg LB cr' VM2 g' Y0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ => rename Rc into RS; rename Mc into MS end.
    pose proof (BH HH3) as HH4. pose proof (BA HA3) as HA4. pose proof (BL Hls3) as Hls4.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC3) as HC4.
    assert (HPAY4 : rdn RSEGS MS (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY3). }
    clear BH BA BL BRd EQM HH3 HA3 Hls3 HC3 HPAY3.

    set (valsS := relay vals3 RS (Z_to_bv 64 (WP 0))).
    apply (HSS fx2 valsS RS MS VM2 A1 PTR OWN LB cr' g').
    - unfold lh_vals, Pm6DrvD_u5.lh_vals. subst valsS. rewrite (relay_len vals3 RS _ ltac:(lia)), relay_81 by lia.
      rewrite !(relay_lo vals3 RS _) by lia.
      repeat split; try (apply YL; [lia | assumption]).
      + unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (9 : reg). cbn [edenot ev ENVb ENV]. apply YL; [lia | exact P82].
      + unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (18 : reg). cbn [edenot ev ENVb ENV]. apply YL; [lia | exact P83].
    - subst valsS. unfold relay. change 84%nat with (81 + 3)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (19 : reg). reflexivity.
    - subst valsS. apply relay_101. lia.
    - cbn [Z.of_nat]. lia.
    - lia.
    - subst valsS. eapply (relay_regs vals3 srR RS _ ltac:(lia)); [vm_compute; reflexivity | exact HR].
    -
      subst valsS.
      assert (HK2 : know_ok RSEGS (ENVb vals3) MS (wposK (ELit 0xfd800) :: flagsK :: knR2)) by (eapply ksubl_sound; [exact HK | vm_compute; reflexivity]).
      pose proof (Forall_inv HK2) as K1. pose proof (Forall_inv (Forall_inv_tail HK2)) as K2. pose proof (Forall_inv_tail (Forall_inv_tail HK2)) as K3.
      unfold knLH2. constructor; [|constructor; [|constructor]].
      + cbn [kentry_ok] in K1 |- *. destruct K1 as (K1a & K1b & K1c). split; [exact K1a|]. split; [apply flat_abs0; lia|].
        rewrite SymDriveX.adenot_lit0 in K1c |- *. cbn [edenot ev ENVb ENV] in K1c |- *. rewrite relay_101 by lia. exact K1c.
      + cbn [kentry_ok edenot ev ENVb ENV]. rewrite relay_101 by lia. unfold WP. rewrite u_small by lia. lia.
      + exact K2.
      + eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity | exact K3].
    - exact HA4.
    - split; [exact HBR | exact REST].
    - exact HC4.
    - exact HPAY4.
    - reflexivity.
    - exact HH4.
    - rewrite PLN in Hcr'. replace (Z.of_nat (Z.to_nat PL)) with PL in Hcr' by lia.
      exact (credit_le_step sp0 Hsp' CALLS (ll_credit Lay PL) cr1 cr' ltac:(lia) CP1 CP2 Hcr2 Hcr').
    - split; [exact HFP' | exact Hls4].
  Qed.

  (* Proof, old beside new: the recorded proof term applied [Pm6DrvE_u5]'s [last_S] / [step_S] / [iter2]
     at main's section arguments (no [RO], no [inp]), which they no longer take at LPS 727298f3; it is
     replaced by the text proof of [SS_real] in projects/jsoncons/fuzz_json_cursor/proofs/lib/U/Pm10DrvF_u.v,
     with [eapply] / [eassumption] so the section arguments are found by unification. *)
  Lemma SS_real : forall (n j : nat), (1 <= n)%nat -> (Z.of_nat j + Z.of_nat n <= 4)%Z -> SSP (Z.of_nat n) j (E (j + n - 1)%nat).
  Proof.
    induction n as [|n IH]; intros j Hn Hjn; [lia|].
    destruct n as [|n'].
    - replace (j + 1 - 1)%nat with j by lia. change (Z.of_nat 1) with 1%Z.
      eapply last_S; eassumption.
    - eapply step_S; try eassumption; [lia|].
      replace (Z.of_nat (S (S n')) - 1)%Z with (Z.of_nat (S n')) by lia.
      eapply iter2; try eassumption; [lia | unfold E, Pm6DrvE_u5.E; apply t_emit_has_nil |].
      replace (j + S (S n') - 1)%nat with (S j + S n' - 1)%nat by lia. apply IH; lia.
  Qed.

  (* Proof, old beside new: the recorded proof term (over main's [lh1_k], without [inp]) is replaced by
     a text proof: [iter1w] then [SS_real], as [drv_loop] is proved in
     projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm10DrvF.v, with the trace turned into [succG] by
     [SpecG.loop_guard_eq]. *)
  Theorem drv_loopw : lh1_k (succG (PHI payload) (Z.to_nat CALLS) fs0).
  Proof.
    pose proof (CALLS_range fdata) as HKr. fold CALLS in HKr.
    set (n := Z.to_nat CALLS). assert (En : Z.of_nat n = CALLS) by (subst n; lia). clearbody n.
    assert (H1 : lh1_k (t_emit (W 1 [b48]) (t_guard (PHI payload) (t_emit (W 1 [b10]) (E (0 + n - 1)%nat))))).
    { apply iter1w; [unfold E, Pm6DrvE_u5.E; apply t_emit_has_nil|]. rewrite <- En. apply SS_real; lia. }
    unfold lh1_k, Pm6DrvD_u5.lh1_k in H1 |- *. intros fx' vals R M VM A1 PTR OWN LB HLV HR HK HA HBLK HC HPAY HH HFP.
    eapply srz_conseq; [eapply H1; eassumption|].
    unfold E, Pm6DrvE_u5.E. replace (0 + n - 1)%nat with (n - 1)%nat by lia.
    apply loop_guard_eq. lia.
  Qed.

End DrvF.
End FPX_1.
