(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact): changed drv_fileA, loop_okA, loop_stepA and 1 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8DrvG.v, lines 347-524, 530-545, 550-789, 794-796, 804-839. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  LibTail RefReadLib RefPrintfLib RefNodes HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm4IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm4DrvEntry Pm4Drv_defs Pm4DrvLib Pm4DrvRead Pm4DrvA Pm4DrvG_defs.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @list]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @vals_ev]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Lists; @ListDef; @map]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @gr]; [@Corelib; @Lists; @ListDef; @seq]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @Env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @eb]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_lo]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @know_ok]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @ksubl_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @know_ok_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @ksubl_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @kn_blkA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knLP6A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @cellCA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knGbaseA]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @Zdiv; @Zmod_unique]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @N]; [@Corelib; @Init; @Logic; @and_ind]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @mod_of_decompZ]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Corelib; @Init; @Logic; @False]; [@stdpp; @bitvector; @definitions; @bv_wrap_small]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_mul64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_add]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @u_small]; [@Stdlib; @Lists; @List; @firstn_nil]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@Corelib; @Lists; @ListDef; @skipn]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @word_to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefReadLib; @word_to_nat_lit]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @file_read]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @file_read_unguarded]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Corelib; @Init; @Nat; @sub]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Corelib; @Init; @Logic; @or]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @Lists; @List; @length_skipn]; [@Stdlib; @Lists; @List; @length_firstn]; [@Corelib; @Init; @Datatypes; @list_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @edenot]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ELit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @ridx]; [@Stdlib; @micromega; @Tauto; @EQ]; [@Stdlib; @micromega; @Tauto; @isBool]; [@Stdlib; @micromega; @Tauto; @TT]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @ridx_roundtrip]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @bv_eqb_refl]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @ridx_range]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @not_morph]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @regs_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @hdr_valsA]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Corelib; @Init; @Peano; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @vals_ev_app_l]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvA; @fds0]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_insert]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_k_per_malloc]; [@Corelib; @Init; @Datatypes; @fst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_b_lin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @CAPk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_b_overhead]; [@Corelib; @Init; @Datatypes; @snd]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_1_r]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_le_mono_r]; [@Corelib; @Numbers; @BinNums; @N0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @credA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @CAPk_range]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv]; [@Stdlib; @Lists; @List; @In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @di_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ablock_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @shadow_blk_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframes_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @FS_BYTES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_addr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_class]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @PM_FS_CLASSES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @app_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_sptop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_bottom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_top]; [@stdpp; @base; @NoDup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @hzA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @hzA_of_block_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @sc_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvA; @ENVA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SCBr]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @sub_as_addA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @want_xA]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @want_x_valA]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @mul2_litA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @cap2_xA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knLPA]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @kentry_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @REG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @IMG_W_A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @CW0]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @find_nz]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @Gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @img_w_client]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @IMG_CLIENT_A]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @ex_intro]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @log_in_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @mrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ahid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2Sound; @SX2S; @mem_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @regions_write0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @regions_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvKitA; @mem_denot_frame_Z]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @rdn_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @block_frame0]; [@Corelib; @Init; @Logic; @or_ind]; [@Stdlib; @Lists; @List; @Forall_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @lp_atA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srRDA]; [@Stdlib; @Lists; @List; @incl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @mdl3]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdFile]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @Fs]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @inv_block1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvRead; @aread_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @blobs_ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @MSO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @sr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @has_window]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvA; @alu_add_w_litA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymRun; @reg_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvRead; @STAGE]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @fds_lookup3A]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @fs_lookup]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @sub_blockA]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @junk_vals]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @len_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @sr_after_call_j]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @c_kept]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvRead; @keep_readA]; [@stdpp; @bitvector; @definitions; @bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @file_read_litA]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @length_readA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefReadLib; @len_word_Z]; [@stdpp; @tactics; @f_equal_help]; [@stdpp; @bitvector; @definitions; @bv_add_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @fds_ins3A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @hdr_appA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knRA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knRf0A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @rz_run_lz2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @FUELA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @STOPSA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @scr0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srRA0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @asegs_wx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @scripts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sym_exec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @carry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_log]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @no_bls]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @ahid_sbm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @sbm_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @content_block0]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@Stdlib; @Lists; @List; @firstn_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvNodesLazyK; @rz_close_lz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @ECALLW]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @is_ecall_ECALLW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @di_halt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @regupd]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @with_fds]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @with_fds_vm]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefNodes; @with_fds_halted']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @with_fds_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @with_fds_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @regs_set_a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @credA_exit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @close_kgA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @hdr_relayA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_48]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_70]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @regs_ok_by_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srGLA]; [@Corelib; @Lists; @ListDef; @Forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @kn_blkA_of_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relay_know6]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @knGbaseA_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knGA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @fds_remove3A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDrive; @v_addi_pc4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @s_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knRe0A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @block_nolog]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @amemcpy_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefPrintfLib; @alu_add_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @src_stage_aacc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @src_stage_app_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @keep_allocA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @model_rt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @model_rt_fds]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@Corelib; @Classes; @Morphisms; @trans_sym_co_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @firstn_len_firstnA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibTail; @rdn_app_Z]; [@Stdlib; @ZArith; @Znat; @Z2Nat; @id]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @firstn_app_skipnA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srRm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knRm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_38]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srLPA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @knLPA_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @rd_atA]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @know_LP_rangesA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srPa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knLPpA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @relayV_71]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymExec2; @SX2; @EMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @sc_ltu_wantA]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @sc_eq_70_38A]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @CAPk_lt10]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knLPgA]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @amalloc_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @cap2_x_valA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @acredit_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @adebit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @kn_blk2A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @keepalloc_G]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knGb0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @src_blk_aacc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @di_blksh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @src_blk_app_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @lb_remove_hdA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srGc0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knGc0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @afree_site]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @lb_remove_2A]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @srGd0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG_defs; @knGd0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @CAPk_S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @loop_stepA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @read_okA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @srC0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @knC0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvA; @fds1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvG; @FPX_1; @DrvG; @loop_okA]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvA; @file_kA]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Lemma relayV_38 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 38 = x38. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#4").
Qed.
Lemma relayV_48 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 48 = x48. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#3").
Qed.
Lemma relayV_70 : forall vals R x38 x48 x70 ext, vals_ev (relayV vals R x38 x48 x70 ext) 70 = x70. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$ext;R1!2,?0#2").
Qed.
Lemma relayV_71 : forall vals R x38 x48 x70 w ext, vals_ev (relayV vals R x38 x48 x70 (w :: ext)) 71 = w. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+1!1,2|600;!1+00$vals;R1$R;R!2'3!1,2|21;0$x38;R0$x48;R0$x70;R0$w;R0$ext;R1!2,?0#2").
Qed.
Lemma relayV_agree : forall ebs vals R x38 x48 x70 ext,
  env_agree 6 (Env (vals_ev vals) ebs) (Env (vals_ev (relayV vals R x38 x48 x70 ext)) ebs).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80|30;%~R+<!1+0!1+1!1,20!1+1!1,2|600;!1+02!2'B#1}6!6'D#8#7#6#5#4#3!3+C2!2'^?!2,^@!1'8#8#9#2!2'^?!2,^@!1'85#9#2!1'^A!2,^@!1'8!6'D#6#5#4#3#2#1#7$ebs;R1$vals;R3$R;R!2'3!1,2|21;2$x38;R2$x48;R2$x70;R2$ext;R3!4,^>%n;R+<%~R46!3+C1!1'^A!2,^@!1'8#6#77$n;R+<$Hn;R4vd!4'^B2!2'85#2!2'8#8#2!8'^C#8#7#6#5#4#3#2#16!2,?17").
Qed.
(* [comment removed for export] *)
Lemma relay_know6 : forall ebs vals R x38 x48 x70 ext M kn kn6,
  know_ok ASEGS (Env (vals_ev vals) ebs) M kn -> ksubl_b kn kn6 = true -> kn_vars_lt 6 kn6 = true ->
  know_ok ASEGS (Env (vals_ev (relayV vals R x38 x48 x70 ext)) ebs) M kn6.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S70|30;!1+1!1,20!1+1!1,2|600;!1+02!1+0+^E}6!2,^@!1'8#<#=$ebs;R%~R+<!1+01$vals;R3$R;R!2'3!1,2|21;2$x38;R2$x48;R2$x70;R2$ext;R3$M;R%~R2!1+^D1$kn;R4$kn6;R4$HK;R!4'^F'^G!2,^@!1'8#9#:#3#2$Hsub;R!3+C+^:!2'^H#3#2,^;$Hv;R!3+C+^:!2'^I5#3,^;!9'^J'^G56!2,^@!1'8!6'D#<#;#:#9#8#7#=#6#4!7'^K#=#<#;#:#9#8#7#1!7'^L'^G6#6#5#4#3#2").
Qed.

Lemma knLPA_split : knLPA = kn_blkA 48 65536 ++ knLP6A. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2,?!1+0+^E!3'6+^E!2'^M}^3!1,J|@0000;'^N").
Qed.
Lemma knGbaseA_sub : ksubl_b (kn_blkA 48 65536 ++ cellCA :: knLP6A) knGbaseA = true. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,?+^:,^;!3+C+^:!2'^H!3'6+^E!2'^M}^3!1,J|@0000;!3,7+^E'^O'^N'^P,^;").
Qed.
Lemma knLP6A_vars : kn_vars_lt 6 knLP6A = true. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,?+^:,^;!3+C+^:!2'^I}6'^N,^;").
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_of_decompZ : forall a b q r : Z, 0 < b -> 0 <= r < b -> a = b * q + r -> a mod b = r.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>0!2'R,5#2!1,:+S!1+0+S!1,^V+M!1+U+M!1+W+M!2,^2+M,K|10;!2,^2+M7!7,^W5'X+Y+Y,Z!7,[5'X+Y+Y,Z!4,\+M!2,^0+M,5,^16,^3!7,[5'X+Y+Y,Z!4,\+M6,^68,^3!1,^4+Y!2'^85,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!7,[5'X+Y+Y,Z!4,\+M6,_2!3,^5+M!3,_3+M8!2,^2+M|11;!2,^2+M|20;,^3$a;R+M$b;R+M$q;R+M$r;R+M$Hb;R!2'G,5#3$Hr;R!2+^Q0!2'G#2#4$He;R!3+C+M#6!2'H!2'^R#5#4#3!4'^B+M#4!2'^S#7#6!6'^T#7#6#5#4&__arith;R$__x2;R+M$__x1;R+M&__wit;R12&__varmap;R!4,^U+M!2,T+M#3#234&__ff;R!8,V5'X+Y+Y,Z9:9;<%__x2;R+M%__x1;R+M%~R!2+^Q!2'R,5#1!2'G#1#2!2+^Q0!2'G#2#3!3#1#7#5#3&__arith;R$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!3,^Z+M!2,^[+M!1,^\,K!2,_0+M}1!2,_0+M,9,_112&__varmap;R!4,^U+M!4,^U+M!2,T+M#5#33#2!2,T+M#44&__ff;R!8,V5'X+Y+Y,Z=:=;<%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!3+C+M#1!2'H!2'^R#2#3#4!3+C+M#2!2'H!2'^R#3#4#5!5#1#5#6#7#8#2").
Qed.
Lemma sub_as_addA : forall c l : Z, 0 <= l <= c -> c < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 c) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 l)) = Z_to_bv 64 (c - l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_70!2'R,5#1|10;!1,J1|600;!1,J3!2'_424!2'G#35!1+1#1!1+1#2%~R!3+C!1+1#3#2#1!3+C+M!2'_7#4#3!2'_7#4#2%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2!1,23!2'4;#5!1,^\,K!2'4;=!2'4;#4!4'_;;,_<>?!3'_9,_:<@!2'_=#5#4!2'4;B!1+1;!2'_?<@!2'_=#6#5!2'_7;!2'4;F!2'_7;>!2'_7;?!2'^S!2'^RHI5!2'_7;<!2'HKJ!2'_@;#5!2'_@;=!2'_@;#6!2'_@;#4!2'_@;!2'HO!2'^S!2'^RN#15!2'_@;B!2'_@;F!2'^S=5!1,J,K!2'_=5U!3+C+M#5,5!3+C+M#6,5!1'_DX!3+C+M#7,5!2'^S#15!2'^S,55!2'^S#:5!2'_=5#8!2'_=#:#9!2'^S^25!2'_=#9#8!2'_I24!2'G,55%~R!2'G,52%~R!2'R,54^6!2'R,52$Ha;R^8$~R+_J!3'_K24#2%Ha;R^8%~R+_J!2'R,55!1,:+S!1+0+S!1,^V+M!1+U+M!1+W+M!2,^0+M,5!3,_L+M!2,^0+M2;!2'^8^?,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2&__sat1;R^5^7&__sat0;R^9^:&__arith;R&__wit;R^;^<&__varmap;R^=^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M^@,^6^A,^3^B^C^6#1}3!2,_0+M^E!2,_0+M,9!4,^U+M!2,T+M#3#2^=!2,^2+M1!1,^4+Y!2,^2+M,K!7,[^?'X+Y+Y,Z!4,\+M^K,^6^A,^3!7,^W^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1^I,^3!7,[^?'X+Y+Y,Z!4,\+M^I,^1^K,^3!3,_N+M^K^I!2'G#25!2'_=#4#5&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!2,_0+M}4!3,^Y+M^F^G,_1^;^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z!6,_M^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^I,_2^@,^3^J!8,V^?'X+Y+Y,Z^L^J!8,V^?'X+Y+Y,Z^M^J!7,^W^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1^N,^3!7,[^?'X+Y+Y,Z!4,\+M^N,^6^A,^3^B^C%__x2;R+M%__x1;R+M%~R%~R!3+C+M#2,5+_O%~R^O%~R!2+^Q!2'R,5#4!2'R#4#3!2+^Q!2'R,5^P!2'G^P5!5#1#;#<#4#9#:!2'_=#1#2!2#1#;#<!2'H#9^1!2,^0+MU!2'^RV#8}1!3,^Y+M!2,_0+M^W^G!3,7+S!2,^X!3,^Y+M^F^X,_1^;!7,[^?'X+Y+Y,Z!4,\+M^I,^6^A,^3!7,[^?'X+Y+Y,Z!4,\+M^@,^1^K,^3!7,^W^?'X+Y+Y,Z^[!7,[^?'X+Y+Y,Z!4,\+M^K,^1^I,^3!3,_N+M^A^K!2'R,5#3!2'_=5#4}2!7,^W^?'X+Y+Y,Z^[^L!2+^Q_16!2'_7;C$c;R+M$l;R+M$Hl;R!2+^Q0!2'R#1#2$Hc;R6&H;R$n;R+_5$b1;R7$b2;R8!5'_69:%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2$~R9$~R%~R!3+C+M!2'_7#4#3!2'_7#4#2!3+C!1+1#5#4#3#1!3'_8#3#2#1%n;R+_5%b1;R7%b2;R8:!4#1;AC!6'_>DE$b;RD!3+C+M!2'_7;#1Gvd!6'_>+MJ$z;R+M!3+C+M!2'_7;!2'4;!2'H!2'_7;!2'4;#6#1G!6'_>+M!2'_@;L$z;R+M!3+C+M#1G!6'_>+MM$z;R+M!3+C+M!2'_@;!2'H#1!2'^S!2'^RHK5G!6'_>+MN$z;R+M!3+C+M!2'_@;!2'HO!2'^S!2'^R#1K5G!6'_>+MP$z;R+M!3+C+MQG!6'_>+MR$z;R+M!3+C+M!2'_@;!2'HO!2'^S!2'^RNM5#1!6'_>+M#4$z;R+M!3+C+MQS!6'_>+M#5$z;R+M!3+C+M!2'_@;!2'H#1!2'^S!2'^RN#55Svd&H;R!2,?+MT!3+C+MVT!6'_A+MV$z;R+M!3+C+M!2'^S!2'H#7!2'^S!2'^R#1#655!2'^S!2'_=#7#65&s;R!2'_B#5,5!2+_CW!1'_DW-_CRN$s;R!2+_CXY!3+C+M!2'^S!2'H#8!2'^S!2'^RV#755!2'^S!2'_=#8#75#12$e;RX!1$e;RZ!7'_>+M,5$l;R+M%Hl;R!2+^Q0!2'R#1#:!3+C+M!2'^S!2'H#;!2'^S!2'^RV#255!2'^S!2'_=#;#25$Hl;R!2+^Q!2'R,5,5!2'R,5#9!6'_>+M,5$z;R+M!3+C+M!2'^S!2'H#;[5!2'^S!2'_=#;,55!6'_>+M#:$z;R+M!3+C+M!2'^S!2'H#;\5[vd!6'_>+M#:$z;R+M!3+C+M[!2'^S#;5!2,?+M^0!2'H#:,5!1'_E#:!3+C+M!2'^S!2'H#:\5^0!2'_=#:,5!1'_F#:!2'^RV,5!1'_GV#8#1#7#1$n;RY!1$Hnz;R!1'_DZ!6'_>+M^1$z;R+M!3+C+M!2'^S!2'H#:#15^3!6'_>+M^4$z;R+M!3+C+M#1^3!6'_>+M^4$z;R+M!3+C+M^2#1!2,?+M^4!2'^S^45!7'_H^45,5^4^D^Q&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^;^<&__varmap;R^H^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M^N,_2!3,^5+M!3,_3+M^A^@^N,^3^B^C%__x2;R+M%__x1;R+M!3+C+M^R!2'H!2'^R5,5^R^S!2'^S^T5!7'_H^T5U^4^D^Q&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^;^<&__varmap;R^H^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M!3,^5+M^K!3,_N+M^A^I,_2!3,^5+M!3,_3+M^A^U^N,^3^B^C%__x2;R+M%__x1;R+M!3+C+M!2'H#1!2'_=5#2!2'H!2'^R5U^R^S!2'^S^V5!7'_H^V5!2'_=#8U^1^D&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^Y^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z!6,_M^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^K,_2^@,^3^J!8,V^?'X+Y+Y,Z^Z^J!8,V^?'X+Y+Y,Z^\^J!7,^W^?'X+Y+Y,Z!7,[^?'X+Y+Y,Z!4,\+M^@,^1_0,^3!7,[^?'X+Y+Y,Z!4,\+M_0,^6^A,^3^B^C%__x2;R+M%__x1;R+M%~R%~R!3+C+M#1,5+_O%~R6%~R!2+^Q_1!2'R#3#4!2+^Q!2'R,5_2!2'G_25!5#1#<#;#4#9#:&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x1;R+M&__wit;R^;^<&__varmap;R!2,T+M#2^>&__ff;R!7,[^?'X+Y+Y,Z!4,\+M!3,_3+M!3,_N+M^A^U^K,_2!3,^5+M!3,_3+M^A!3,_N+M^K^U_0,^3^B^C%__x1;R+M!3+C+M!2'^RV#1!2'H!2'^R5!2'_=#1U!2'_=5#1!1#1#;#1T#1!3+C+M!2'_@;!2'H#5!2'^S!2'^RN#45RM!3'_P;#5&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!2,_0+M_3^X,_1^;^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z^L^J!8,V^?'X+Y+Y,Z^M^J_4^B^C%__x2;R+M%__x1;R+M%~R!2'G#15%~R!2+^Q_1!2'R#3#2_5!4#1#7#8#5#6P!3'_P;#4&__sat1;R^5^7&__sat0;R^9^:&__arith;R$__x2;R+M$__x1;R+M&__wit;R^Y^<&__varmap;R^H^>&__ff;R!8,V^?'X+Y+Y,Z^Z^J!8,V^?'X+Y+Y,Z^\^J_4^B^C%__x2;R+M%__x1;R+M%~R^O%~R!2+^Q!2'R,5#2!2'R#2#3_5!4#1#8#7#5#6_6!2'_Q;BI!2'_Q;#4H!2'_Q;=K!2'_Q;#5!2'_7;!2'4;L!2'_Q;L!2'_7;@!2'_R>?!3+C+M!2'_7;E_6A!2'_S<@").
Qed.
Lemma mul2_litA : forall c : Z, 0 <= c -> 2 * c < 2 ^ 64 -> mul_div M_MUL (Z_to_bv 64 2) (Z_to_bv 64 c) = Z_to_bv 64 (2 * c).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^30|10;!1,J0|600;!1,J2!2'_413!1+1#1!1+1#2%~R!3+C!1+1#3#2#1!3+C+M!2'_7#4#3!2'_7#4#2%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2!1,22!2'491!2'49#4!4'_;9,_<:;!2'^R1#4!2'49=!2'_79:!2'_79;!2'^R1#5!2'_79!2'49A!2'^R1#1!2'_I13%~R!2'G,51%~R!2'R,53!2'G,54!2'R,51$Ha;RF$~R+_J!3'_K13#2%Ha;RF%~R+_J!2'R,54!2,_0+M,9!2,_0+M}2!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^0+M1!2,^2+M,K!3,_3+MPQ!3,_L+MP9!7,[O'X+Y+Y,Z!4,\+MR,^6S,^3!1,^4+Y!2,^0+M,5!7,[O'X+Y+Y,Z!4,\+MV,^1Q,^3!2'^8O,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'GC4!2'R,5#2!2'^R1#3!3#1#7#5#6&__sat3;RDE&__sat2;RGH&__arith;R$__x1;R+M&__wit;R!3,7+S!2,_UI!2,^X!3,^Y+MIJ,_1KL&__varmap;RMN&__ff;R!8,VO'X+Y+Y,ZTU!8,VO'X+Y+Y,ZWU!7,^WO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MV,^1R,^3TXY%__x1;R+M%~RZ%~R[!2+^Q!2'R,5\!2'G\4^0}1$c;R+M$H0;R!2'R,5#1$H1;R!2'G!2'^R1#24&H;R$n;R+_5$b1;R5$b2;R6!5'_678%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2$~R7$~R%~R!3+C+M!2'_7#4#3!2'_7#4#2!3+C!1+1#5#4#3#1!3'_8#3#2#1%n;R+_5%b1;R5%b2;R68!4#19<>!6'_>+M!2'^S!2'^R?@4$z;R+M!3+C+M#1B!6'_>+M1$z;R+M!3+C+M!2'^S!2'^R#1!2'_79!2'49#54B!6'_>+M#4$z;R+M!3+C+M!2'^SC4B!6'_>+M=$z;R+M!3+C+M!2'^SA4#1!6'_>+M=$z;R+M!3+C+M#1A!2,?+M=!2'^S=4!3'_T=4^1!2'_79>!2'_V=^1@!2'_V#4&__sat3;RDE&__sat2;RGH&__arith;R$__x1;R+M&__wit;R!3,7+S!2,_UJ!2,^X!3,^Y+MI!2,_0+M^2,_1KL&__varmap;RMN&__ff;R!8,VO'X+Y+Y,ZTU!8,VO'X+Y+Y,ZWU!7,^WO'X+Y+Y,ZW!7,[O'X+Y+Y,Z!4,\+MQ,^6S,^3XY%__x1;R+M%~RZ%~R[!2+^Q!2'R,5#3!2'G#34^0?!2'_V1&__sat3;RDE&__sat2;RGH&__arith;R&__wit;RKL&__varmap;R!1,^V+MN&__ff;R!7,^WO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MV,^1P,^3!7,[O'X+Y+Y,Z!4,\+MP,^6S,^3XY!2+^QF!2'G14#1!2'_79<!2'_R:;").
Qed.
Lemma firstn_app_skipnA : forall {X} (l : list X) (a b : nat), firstn a l ++ firstn b (skipn a l) = firstn (a + b) l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;5lcd;g_Wd;lcd;g6d;lcd;g_>d;lcd;g_Xd;<scd;%l;R!1+0#4%b;R+<!3+C!1+0#6!3'6#6!3'_X#6#3#2!3'_X#6#1!3'_Z#6#3#2!3'_X#6!2'@#3#1#2!1+0#5!1+0#8!1,E#5!1+0#7!1,:#7!1,E#4!1+0#;!3'_X#;!2'@#8#5#1!1,E#8!3,7#;#2#1$X;R{cd;$l;R!1+0#1$a;R+<!5'_Y$a;R+<0$l;R!1+0#3$b;R+<!2,?1!3'_X#5!2'@,9#1#2$a;R+<$IH;R0$l;R1$b;R+<-0RN$l;R!1+0#7!3+C2!3'6#8!3'_X#83#1!3'_X#8#2!3'_Z#83#1!3'_X#8!2'@3#2#1#22vd!6'_>45$l;R4!3+C2#1!1,:#8!2,?45!3'_X#7#15!2'_W#7#1!3+C4!3'6#7!3'_X#765!3'_X#7#1!3'_Z#765!3'_X#7!2'@6#15$x;R#7$l;R!1+0#8!2$x;R#9$l;R!1+0#:vd!6'_>78$l;R7!3+C!1+0#<!3,7#<#3#1!3,7#<#3!3'_X#<!2'@#9#6#2!2,?7!3,7#;#28!3'6#;!3'_X#;#8#1!3'_X#;#5!3'_Z#;#8#1!2#7#1#5!3+C7!3'6#;!3'_X#;9:!3'_X#;#5!3'_Z#;9:!3'_X#;!2'@9#5:#2#1#1#2").
Qed.
Lemma file_read_litA : forall data (off cnt : Z), 0 <= off < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0|30;!1+1!1,20!1+01|10;!1,J3|600;!1,J5!2'_446!2+^Q!2'R,5#2!2'G#27!1,25!2'49#3!1'_[:!2'49#4!1'_[<!1'_\#4!3'_X1>!3'_Z1!1'_\#5#6!1'_\#3!2'_I46%~R!2'G,54%~R!2'R,56!2'G,57!2'R,54$Ha;RC$~R+_J!3'_K46#2%Ha;RC%~R+_J!2'R,57!1+W+M!2,^2+M,K!7,^WF'X+Y+Y,Z!7,[F'X+Y+Y,Z!4,\+M!2,^0+M,5,^1G,^3!7,[F'X+Y+Y,Z!4,\+MG,^6!3,_L+M!2,^0+M49,^3$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,VF'X+Y+Y,ZH!1,^4+YH!2'^8F,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__x1;R+M%~R!2+^Q!2'R,5#1!2'G#178$data;R2$off;R+M$cnt;R+M$~R8$~R8!6'_>2!3'_X1;!3'_Z1=#5$l;R2!3+C2#1?!6'_>+<@$n;R+<!3+C2!3'_X1#1!3'_Z1!1'_[!2'49#5#6?!6'_>+<>$n;R+<!3+C2!3'_X1>!3'_Z1#1#6?!2,?2!3'_X1@!3'_Z1>#5=!2'`0#4&__sat2;RAB&__sat1;RDE&__arith;RIJ!2#1#7#5;!2'`0#3&__sat2;RAB&__sat1;RDE&__arith;RIJ!2#1#6#4!3'`1#5<:!3'`2#5<:").
Qed.
Lemma length_readA : forall (data : list byte) (off cnt : Z), 0 <= off -> off <= Z.of_nat (length data) -> 0 <= cnt ->
  Z.of_nat (length (firstn (Z.to_nat cnt) (skipn (Z.to_nat off) data))) = Z.min cnt (Z.of_nat (length data) - off).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_R0|30;!1+1!1,20!1'_\#4!1'_\#5!3'_Z13#6!2'A14!1'I#1!2'_=!1'I!2'A1#7#6!2'`4#57!2'A1#6!2'`593!2'`32:!1'I;!1'I9!2'`4#4!2'_==#5!2'`7,5#4!2'`7,5#5!2'`7,5!2'_==@!2'`4?A!1+C+M$x;R+M#1$x;R+M!2'`7,5#1!2'`7,5#8!2'_=!1'I!2'A1#;#1!2'`7,5G!2'`7,5#;!2'`4#1#3!2,^[+M!1,^\,K}=!2,_0+ML!3,^Z+MKM}:!2,_0+MO}9!2,_0+MQ!3,^Z+MKR}7!2,_0+MT}5!2,_0+MV}1!2,_0+MX!2,_0+M,9!3,^Y+MW!3,^Y+MYZ!3,^Y+MS!3,^Y+MU[!2,^X!3,^Y+MN!3,^Y+MP\,_1}8!2,_0+M^1!3,^Z+MKW}4!2,^X!3,^Y+MM!3,^Y+MR!3,^Y+M^2!3,^Y+M^3!3,^Y+M!2,_0+M^4Z,_1}3!3,^Y+M^3!3,^Y+M!2,_0+M^6Z!2,^X!3,^Y+MM!3,^Y+MR^7,_1}6!2,_0+M^9!3,^Y+MS!3,^Y+MU!3,^Y+M^:[!2,^X!3,^Y+MN!3,^Y+MP^;,_1}<!2,_0+M^=!3,^Z+MK^>!3,^Z+MK^2!3,^Y+MWZ!3,^Y+M^:^A!3,^Y+M^@!3,^Y+MU^B!2,^X!3,^Y+M^?!3,^Y+MR^C,_1!2,^X!3,^Y+M^>!3,^Y+M^2^7,_1}2!2,^X!3,^Y+M^>!3,^Y+M^2!3,^Y+M^3!3,^Y+M!2,_0+M^FZ,_1!3,^Y+M^@!3,^Y+MU^A!2,^X!3,^Y+M^?!3,^Y+MR^H,_1};!2,_0+M^J!3,^Z+MKU!3,^Y+M^L^:!2,^X!3,^Y+M^K!3,^Y+MR^M,_1!2,^X!3,^Y+MM!3,^Y+MP!3,^Y+MR^@,_1!2,_0+M}>!2,^X!3,^Y+M^P!3,^Y+M^K!3,^Y+MPS,_1!3,^Y+M^3Z!3,^Y+M^2!3,^Y+M^L^R!3,^Y+MM!3,^Y+MR^S!3,^Y+MM!3,^Y+M^K^R!3,^Y+M^>!3,^Y+MP^R!3,^Z+MK^K!3,^Y+M^WR!2,^X!3,^Y+M^P!3,^Y+M^>^X,_1!2,^X!3,^Y+M^>!3,^Y+MP!3,^Y+MU!3,^Y+M^:Y,_1!2,^X!3,^Y+M^K!3,^Y+MR!3,^Y+MU^:,_1!3,^Z+MKP!3,^Y+M^\^2!2,^X!3,^Y+MM!3,^Y+M^K_0,_1!2,^X!3,^Y+MM!3,^Y+M^\!3,^Y+M^2^M,_1!3,^Y+M^\^A!3,^Y+M^W^A!2,^X!3,^Y+M^P^T,_1!3,^Y+M^W^B!2,^X!3,^Y+MN!3,^Y+M^>_6,_1!2,^X!3,^Y+MM!3,^Y+M^K^7,_1!2,^X!3,^Y+MN!3,^Y+M^>_4,_1!2,^X!3,^Y+M^?!3,^Y+M^K_3,_1!2,^X!3,^Y+M^>!3,^Y+MP^7,_1!1+W+M!2,^2+M0!2,^2+M|23;!2,^2+M,K!1,^4+Y!2,^0+M,5!2,^2+M|21;|20;!2,^2+M_C!2,^2+M|22;!3,_N+M_D_E|11;!2,^2+M_G!3,_N+M_D_H|10;!2,^2+M_J!3+C+M#9#6!3+C+M#9,5!2+^Q!2'R#6,5_M!2'_=#6#8!2'_=#8#7!2'R,5#;$data;R!1+01$off;R+M$cnt;R+M$~R!2'R,5#2$~R!2'R#3!1'I!2'A1#4$~R!2'R,5#3!6'_>+<!2'`325$n;R+<!3+C+M68!6'_>+<:$n;R+<!3+C+M!1'I!2'`33#18!4'`6!3+C+M<>!3+C+MB>!<'L+M+MCDC$x;R+M$y;R+M!1'`8!3+C+M#2#1<B!<'O+<+M+M+M'I'IDD$x;R+<!2,?+M6;B!B'`9+<+<+<+M+M+M'`:'I'I'I'`4'`;2?!<'O+M+<+M+M'_\D'IE'`<#4#4!2,?+M#4:A!B'`9+<+<+<+M+M+M'`='I'I'I$n;R+M$m;R+M!2'`7,5!2'_=#2#1'`>9=!2,?+M=3@!<'O+M+<+M+M'_\D'IE'`<#5#5!2,?+M#5>>!2,?+M>&cstr;R!1'Q9!2'R,5=&H2;R!2'`?#57!2+`@!2+^Q!2'G#57!3+C+M8#5!2+^Q!2'R7#5!3+C+M87&z2;R!2'`4#6!2'_=!1'I!2'A1#8#7+M&H3;R!2'`A,5#8!2+`@!2+^Q!2'G,5#8!3+C+MF#8!2+^Q!2'R#8,5!3+C+MF,5&z3;R!2'`7,5#9+M&H4;R!2'`A,5G!2+`@!2+^Q!2'G,5G!3+C+MHG!2+^Q!2'RG,5!3+C+MH,5&z4;R!2'`7,5!2'_=!1'I!2'A1#<#2+M&H5;R!2'`A,5#;!2+`@!2+^Q!2'G,5#;!3+C+MI#;!2+^Q!2'R#;,5!3+C+MI,5&z5;R!2'`7,5#<+M&H6;R!2'`?#1#3!2+`@!2+^Q!2'G#1#3!3+C+MJ#1!2+^Q!2'R#3#1!3+C+MJ#3&z6;R!2'`4#2#4+M&__arith;R$__p1;Rw$__x8;R+M$__x7;R+M$__x6;R+M$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S^0!3,7+S^5!3,7+S^8!3,7+S^<!3,7+S^D!3,7+S^E!3,7+S^G!3,7+S^I!3,7+S^N!3,7+S^N!3,7+S^O!3,7+S^O!3,7+S^Q!3,7+S^Q!3,7+S^Q!3,7+S^Q!3,7+S!2,^X!3,^Y+MN\,_1!3,7+S!2,^X^T,_1!3,7+S!2,^X!3,^Y+M^P^U,_1!3,7+S!2,^X!3,^Y+MN^;,_1!3,7+S!2,^X!3,^Y+M^?^C,_1!3,7+S!2,^X!3,^Y+MM^V,_1!3,7+S!2,^X!3,^Y+M^>^S,_1!3,7+S!2,^X!3,^Y+M^?^H,_1!3,7+S^I!3,7+S^G!3,7+S^E!3,7+S^D!3,7+S^<!3,7+S^8!3,7+S^5!3,7+S^0!3,7+S^Y!3,7+S^Y!3,7+S^Z!3,7+S^Z!3,7+S^[!3,7+S^[!3,7+S_1!3,7+S_1!3,7+S_2!3,7+S_2!3,7+S!2,^X^V,_1!3,7+S!2,^X!3,^Y+M^?_3,_1!3,7+S!2,^X!3,^Y+MN_4,_1!3,7+S!2,^X^U,_1!3,7+S_5!3,7+S!2,^X!3,^Y+MN_6,_1!3,7+S_7!3,7+S_5!3,7+S_8!3,7+S_9!3,7+S_:!3,7+S_;!3,7+S^N!3,7+S^N!3,7+S!2,^X!3,^Y+M^?!3,^Y+M^K!3,^Y+M^\^B,_1!3,7+S!2,^X!3,^Y+MM_0,_1!3,7+S_;!3,7+S_:!3,7+S_9!3,7+S_8!3,7+S!2,^X!3,^Y+M^P^X,_1!3,7+S_7!1,:+S!1+0+S&__varmap;R!4,^U+M!4,^U+M!4,^U+M!2,T+M#9#5!1,^V+M#3!2,T+M#7#2!4,^U+M!2,T+M#6#4!2,T+M#8!1+U+M&__ff;R!8,V_<'X+Y+Y,Z!7,`B_<'X+Y+Y,Z!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_=,^6_>,^3!7,[_<'X+Y+Y,Z!4,\+M_?,_2_=,^3!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_>,^1_=,^3!7,[_<'X+Y+Y,Z!4,\+M_?,_2_>,^3_@!8,V_<'X+Y+Y,Z!7,`B_<'X+Y+Y,Z!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^6_B,^3!7,[_<'X+Y+Y,Z!4,\+M_=,_2_B,^3!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_B,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_=,_2_A,^3_@!8,V_<'X+Y+Y,Z!7,`B_<'X+Y+Y,Z!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^6_F,^3!7,[_<'X+Y+Y,Z!4,\+M_>,_2_F,^3!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_F,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_>,_2_A,^3_@!8,V_<'X+Y+Y,Z!7,`B_<'X+Y+Y,Z!7,^W_<'X+Y+Y,Z!6,^7_<'X+Y+Y,Z#;!7,[_<'X+Y+Y,Z!4,\+M_E,_2_H,^3!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_H,^1_A,^3!7,[_<'X+Y+Y,Z!4,\+M_E,_2_A,^3_@!8,V_<'X+Y+Y,Z!7,`B_<'X+Y+Y,Z!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_B,^6_I,^3!7,[_<'X+Y+Y,Z!4,\+M_K,_2_B,^3!7,^W_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_I,^1_B,^3!7,[_<'X+Y+Y,Z!4,\+M_K,_2_I,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_D,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_B,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_H,^1_D,^3_@!8,V_<'X+Y+Y,Z!7,[_<'X+Y+Y,Z!4,\+M_A,^1_H,^3_@!7,[_<'X+Y+Y,Z!4,\+M_?,_2_K,^3!2'^8_<,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p1;Rw%__x8;R+M%__x7;R+M%__x6;R+M%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+`@!2+^Q!2'G#8#7!3+C+M#1#8!2+^Q!2'R#7#8!3+C+M#1#7%~R!2+`@!2+^Q!2'G,5#6_L_N%~R!2+`@!2+^Q!2'G,5_O!3+C+M#9_O!2+^Q!2'R_O,5_M%~R!2+`@!2+^Q#<_L_N%~R!2+`@!2+^Q!2'G#9_P!3+C+M#6#9!2+^Q!2'R_P#9!3+C+M#6_P%~R!2'R,5#9%~R_Q%~R!2'R#:#;%~R_Q!3+C+M#:#;!B#1!2'G,5#A#4#6#8#@!1'I!2'A1#B#A#:#2#3#5#7#9#;#<#=#>#?5!3'`C13#6!2'A1!3'_X124!3'`D124").
Qed.
Lemma firstn_len_firstnA : forall {X} (l : list X) w, firstn (length (firstn w l)) l = firstn w l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>6lcd;g_Wd;lcd;gAd;lcd;g`Ed;lcd;g_>d;lcd;g_Xd;<scd;!1+0#4!3'_X#4#1#2!1+0#3!1,:#3!1,:#4!3'_X#3#13!2'A#35!3'_X#5#1#2!3,7#7#5#4!3'_X#7#18!1+0#8!3'_X#8#1#5!3,7#8#6#5!3'_X#8!1,E#1<$X;R{cd;$l;R!1+0#1!5'`E#2$l;R!1+0#2%w;R+<!3+C0!3'_X#4!2'A#41#21$w;R+<!6'_>23$l;R2!3+C0#1!3'_X#4#24!6'_>23$l;R2!3+C04#1!2,?235!2'_W#3#1!3'_X#363!2'_W#36$x;R#2$l;R2$IH;R%w;R+<!3+C!1+0#5!3'_X#5!2'A#57#27$w;R+<-<RN$n;R+<!3+C!1+0#7!3'_X#7!2'A#7989#12!2,?!1+0#6!3'_X#6,9!3,7#6#4#3$n;R+<!1$w;R+<vd!6'_>:;$l;R:!3+C!1+0#9!3,7#9#7#1!3,7#9#7!3'_X#9#2#6!2,?:!3,7#8#6;!3'_X#8!2'A#8;#5!1#4#1!3+C:!3'_X#8!2'A#8=<=#1#1").
Qed.
Lemma lb_remove_2A : forall A2 n2 A n, A2 <> A -> lb_remove A [(A2, n2); (A, n)] = [(A2, n2)].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S:0!2'`F#5#3%~R!3+C+^:!2'`F#2#1,`G!1'_D!3+C+M#3#2%~R!1'_D!3+C+M#2#1!3+C+^:!2'`F#3#2,`G!2+`I+M+M!1+03!4,`J+M+M#5#4!1,:3!3,7356!4,`J+M+M#7#6!3,7386$A2;R+M$n2;R+M$A;R+M$n;R+M$H;R!1'_D!3+C+M#4#2vd&H0;R!4'^B+^:0,`G&H0;R$x;R+M$y;R+M!5'_612%~R!1'_D!3+C+M#2#1!3+C+^:!2'`F#3#2,`G$~R1$~R%~R!1'_D!3+C+M#3#2!3+C+^:!2'`F#4#3,`G#1!2'`H#2#1%x;R+M%y;R+M2!3#1#6#4#2!3+C+^:,`G0!6'_A+^:,`G$b;R+^:!3+C4-^:RN$~R+^:4#127!3,738-^:RN$~R+^:4!2'`F#5#52679!6'_>+^:,^;$b;R+^:!3+C4!3,738-^:RN$~R+^:4#12679!2,?4!3,73!4,`J+M+M#6#56!2'`F#4#4!1'`K#4!2'`F#6#4#1!3+C4!2'`L#3!3,735!3,73!4,`J+M+M#3#267").
Qed.
Lemma regs_ok_by_nth : forall E sr R,
  (forall i, (0 < i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) -> regs_ok E sr R.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^:0!1,2|21;!1,2|600;!1+11}P!1'I#2!1,`R,5!1+10!3,`T0,5,`U!3'`S0#17!1'`V#5!4'`Q+`N9#85!3'`S0#37!1+1#1!1+1#2%~R!3+C!1+1#3#2#1!3+C+M!2'_7#4#3!2'_7#4#2%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2$n;R+_5$b1;R<$b2;R=!5'_6>?%~R!3+C+M!2'_7#3#2!2'_7#3#1!3+C!1+1#4#3#2$~R>$~R%~R!3+C+M!2'_7#4#3!2'_7#4#2!3+C!1+1#5#4#3#1!3'_8#3#2#1%n;R+_5%b1;R<%b2;R=?}1!1,:+S!1+0+S!1+U+M!1+W+M!2,^2+M,K|10;!4,\+MG,_2!2,^2+MH!1,^4+Y!2'^8F,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'_707!3,`T0,5vv,`U!2'`Z0,5!3'`S077!3+C+<!1'`V#4,9!2'40!1'I9!1'I#1!1'_DP!1'`V#6!2'B,9T!2'BT3!1'IT!2'G,5W|500;!1,JY!2'GWZ!2,?+M,5!2,?+MW!<'L+<+M'B'I'G'NTW^03Z!2,?+MZ!1'`V#7!3+C+<^2,9!1'I^2!3+C+M^4,5!1'_D^5!1'`V#8!2,^0+M,5!7,[F'X+Y+Y,Z!4,\+MG,^6!2,^0+MZ,^3$E;R+`M$sr;R!1+0+`N$R;R!2'302$H;R%i;R+<%~R!2+^Q!2'B,9#1!2'B#13!3+C2!2'`O#3!2'404!2'`P#5!4'`Q+`N#2#45vd$r;R6vd&b;R8+^:&Hr0;R!2,?+^:#1!3+C+^:!3'`S0#27#1!1-^:RN$b;R+^:%Hr0;R!3+C+^:!3'`S0#47#1!3+C2!2'`O#7#5!2'`P#9-^:RN$~R+^:+`N#225:#22$Hr0;R!3+C+^:;,^;&H0;R&H0;R@A!4#10#57&__arith;R$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!3,^Z+M!2,^[+M!1,^\,K!2,_0+MB!2,_0+M,9,_1CD&__varmap;R!4,^U+M!2,T+M#3#2!1,^V+ME&__ff;R!8,VF'X+Y+Y,Z!6,`WF'X+Y+Y!7,[F'X+Y+Y,`XI,^3!5,`YF'X+Y+Y,`XJ!7,[F'X+Y+Y,ZI,^3KL%__x2;R+M%__x1;R+M%~R!3+C+^:!2'`F#1#2,^;!3+C+M#2#3!3#1M!2'_70#6#3!3+C6#4N!7'_>67$r;R6%Hr0;R!3+C+^:8,^;!3+C2!2'`O#9#2!2'`P#;5$Hr0;R!3+C+^:O,^;vd!2,?2!2'41,5!3+C2!2'`O#87!2'`P#:5#5#1#2$Hr0;R!3+C+^:;,`G&Hnz;Rvd$Hc;RP&H0;R!6'_A6Q$r;R6!3+C6#17!6'_>+<,9$n;R+<!3+C6!2'40R7&H0;R@A!4#10!2'40!1'I,97!2,?+MM9#1#5!1'`[#5!3+C6#5N!8'_>67$r;R6%Hr0;R!3+C+^:8,`G%Hc;R!3+C+<!1'`V#2,9+_O$Hr0;R!3+C+^:O,`G$Hc;R!3+C+<!1'`V7,9&Hr0;R!6'_A+^:O$b;R+^:!3+C+^:#1,`G#2,^;!2'`\07!3+C+^:,^;,`G&H0;R!6'_A+^:,^;$e;R+^:-^:RN$b;R+^:w#12+_J+_O,`U,`G#1+_O!2'a0+_O#1#6#1#3#2SS&Hx;R!2#69&H0;R!1'a1#5!2'B93!4'`6!2+^QUV!2+^QX[!6'a2UVX[!<'L+<+M'B'I'G'N,9,5\TW^0^1&H1;R!4'FV[^1#1[&Hnz0;R!4'F!1'_D^3^6!3'a3^3^5!<'L+<+M!1+C+<'I!1+C+M$x;R+<$y;R+<!3'a4!3+C+M4R!3+C+<#2#1!2'a5#2#1^2^4!2,?+M^4,9,5\#3^6&cstr;R!1'Q^7!2'R,5!1'I^7&__arith;R$__x1;R+M&__wit;RCD&__varmap;R!2,T+M#2E&__ff;R!8,VF'X+Y+Y,Z!7,[F'X+Y+Y,Z!4,\+M^8,^1G,^3J!8,VF'X+Y+Y,Z!6,_MF'X+Y+Y,Z!7,[F'X+Y+Y,Z!4,\+MG,_2^8,^3J!8,VF'X+Y+Y,Z^9J!7,^WF'X+Y+Y,Z!7,[F'X+Y+Y,Z!4,\+M^8,^6G,^3^9KL%__x1;R+M%~R!2'R,5#1%~R%~R!3+C+M#2,5+_O%~R!2'G#3Z!2+^Q!2'G,5#4!2'G#4Z!4#1!1'I!1'`V#:#2#3#4!3+C2!2'`O#7Q!2'`P#9:&Hx;R!6'_A6!2'40W$b;R6!3+C2!2'`O#9#1!2'`P#;!4'`Q+`N^2#:5#1#6!1'`[#6!3+C2!2'`O#8#6!2'`P#:!4'`Q+`NT#95#1#1!3+C2!2'`O#3#1!2'`P#5!2'a6#4#1!3'a7#4#3#2").
Qed.
Lemma lb_remove_hdA : forall A n l, lb_remove A ((A, n) :: l) = l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+`I+M+M!1+00$A;R+M$n;R+M$l;R1vd!6'_>+^:,^;$b;R+^:!3+C1-^:RN$~R+^:1#12#2!3,70!4,`J+M+M#4#3!2'`L#4#2#2!2,?1#1!2'`F#3#3!1'`K#3!3+C1!2'`L#3!3,70!4,`J+M+M#3#2#1#1").
Qed.
Lemma lb_remove_1A : forall A n, lb_remove A [(A, n)] = [].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S30!2+`I+M+M!1+00!1,:0$A;R+M$n;R+Mvd!6'_>+^:,^;$b;R+^:!3+C1-^:RN$~R+^:1#122!3,70!4,`J+M+M#3#222!2,?12!2'`F#2#2!1'`K#2!3+C1!2'`L#2!3,70!4,`J+M+M#2#122").
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section DrvG.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hcells : incl RD_CELLS (asc_cells C).
  Hypothesis HCOST : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L.
  (* [comment removed for export] *)
  Variables a0s path : list byte.
  Variable fs0 : Fs.Fs.
  Variable fdata : list byte.
  Variables p0 p1 can : word.
  Variable M0 : word -> option byte.                    (* [comment removed for export] *)
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Variable LK0 : list fframe.
  Variable A0 : list (Z * Z).

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation ENVG := (ENVA fdata).
  Let LEN : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Definition hdr_valsA (vals : list word) : Prop :=
    vals_ev vals 0 = sp0 /\ vals_ev vals 1 = p0 /\ vals_ev vals 2 = p1 /\ vals_ev vals 3 = can.
  Lemma hdr_relayA : forall vals R x38 x48 x70 ext, hdr_valsA vals -> hdr_valsA (relayV vals R x38 x48 x70 ext).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^70!1,2|600;!1+10!1+01|21;!6'D#8#7#6#5#4#3}1}2}3!3+C1!2'847/can;!2+^Q!3+C1!2'846/p1;8!3+C1!2'8#8,9/sp0;!3+C1!2'8#85/p0;!6'D#7#6#5#4#3#2|30;!2'A!1+1!1,2=/fdata;!1'I>!3+C+M/LEN;?vd!2,?+M?@}6|11;!1,JC!1,J|22;!2'GDE!2,?+ME!1'Q>!2'R,5?|10;!1,JJ!1,J|50f;!2'_IKL!2'_4KL%~R!2'G,5K%~R!2'R,5L!2'G,5N!2'R,5K$Ha;RP$~R+_J!3'_KKL#2%Ha;RP%~R+_J!2'R,5N!2'_70/sp0;|40;!1,JT!2'a9SU%~R!2'R,5S%~R!2'R,5U!2'R,5!2'^SSU!1,:+S!1+0+S!1,^V+M!1+U+M!1+W+M!2,^0+ME!2'^8\,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'GKE!1,J,K!2'G^4E!2'G,5E$vals;R2$R;R!2'3!1,231$x38;R1$x48;R1$x70;R1$ext;R2$H;R!1'a8#6vd!6'_>1!2'8#7,9$b;R1!2+^Q!3+C1#1/sp0;!2+^Q!3+C1!2'845/p0;9!6'_>1!2'8#75$b;R1!2+^Q:!2+^Q!3+C1#1/p0;9!6'_>1!2'8#76$b;R1!2+^Q:!2+^Q;!2+^Q!3+C1#1/p1;8!6'_>1!2'8#77$b;R1!2+^Q:!2+^Q;!2+^Q!3+C1!2'8#86/p1;!3+C1#1/can;#1!2'8<7!8'^C#7#6#5#4#3#27&heq_LEN;RA@!4'`6!2'B7BF!<'L+<+M'B'I'G'N7D!2,?+MDBEG&cstr;RHI&__sat73;RMO&__sat72;RQR&__sat71;RVW&__arith;R&__wit;RXY&__varmap;RZ[&__ff;R!7,[\'X+Y+Y,Z!4,\+M!2,^0+MD,^6^0,^3^1^2F#1!2'8<6!8'^C#7#6#5#4#3#26&heq_LEN;RA@!4'`6!2'B6B^3!<'L+<+M'B'I'G'N6K!2,?+MKBEG&cstr;RHI&__sat73;RMO&__sat72;RQR&__sat71;RVW&__arith;R&__wit;RXY&__varmap;RZ[&__ff;R!7,[\'X+Y+Y,Z!4,\+M!2,^0+MK,^6^0,^3^1^2^3#1!2'8<5!8'^C#7#6#5#4#3#25&heq_LEN;RA@!4'`6!2'B5B^5!<'L+<+M'B'I'G'N5^4!2,?+M^4BEG&cstr;RHI&__sat73;RMO&__sat72;RQR&__sat71;RVW&__arith;R&__wit;RXY&__varmap;RZ[&__ff;R!7,[\'X+Y+Y,Z!4,\+M!2,^0+M^4,^6^0,^3^1^2^5#1!2'8<,9!8'^C#7#6#5#4#3#2,9&heq_LEN;RA@!4'`6!2'B,9B^6!<'L+<+M'B'I'G'N,9,5!2,?+M,5BEG&cstr;RHI&__sat73;RMO&__sat72;RQR&__sat71;RVW&__arith;R&__wit;RXY&__varmap;RZ[&__ff;R!7,[\'X+Y+Y,Z!4,\+M!2,^0+M,5,^6^0,^3^1^2^6#1!1'a8<").
Qed.
  Lemma hdr_appA : forall vals ext, hdr_valsA vals -> (6 <= length vals)%nat -> hdr_valsA (vals ++ ext).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^=0!1,2|600;!1+10!1+01}6!3'61#5#4}1}2}3!3+C1!2'847/can;!2+^Q!3+C1!2'846/p1;8!3+C1!2'8#5,9/sp0;!3+C1!2'8#55/p0;!3'61#4#3|30;!2'A!1+1!1,2=/fdata;!1'I>!3+C+M/LEN;?vd!2,?+M?@!2'A1#5|11;!1,JC!1'IB!2,?+ME!1,J|22;!2'RGE!4'F!2+a:3BH!<'L+<+M+a:'I'R'a<3G!2,?+MGBEF#2!2'A1#6!1'QJ!2'R,5!1'IJ!1'Q>!2'R,5?|10;!1,JO!1,J|50f;!2'_IPQ!2'_4PQ%~R!2'G,5P%~R!2'R,5Q!2'G,5S!2'R,5P$Ha;RU$~R+_J!3'_KPQ#2%Ha;RU%~R+_J!2'R,5S!2'_70/sp0;|40;!1,JY!2'a9XZ%~R!2'R,5X%~R!2'R,5Z!2'R,5!2'^SXZ!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^2+M,K!7,[^4'X+Y+Y,Z!4,\+M!2,^0+MG,^1^5,^3!1,^4+Y!2'^8^4,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'RG#1!2#1!1'I!2'A1#<#7!1,J,K$vals;R2$ext;R2$H;R!1'a8#2$HL;R!2+a:3!2'A1#3vd!6'_>1!2'8#4,9$b;R1!2+^Q!3+C1#1/sp0;!2+^Q!3+C1!2'845/p0;9!6'_>1!2'8#45$b;R1!2+^Q:!2+^Q!3+C1#1/p0;9!6'_>1!2'8#46$b;R1!2+^Q:!2+^Q;!2+^Q!3+C1#1/p1;8!6'_>1!2'8#47$b;R1!2+^Q:!2+^Q;!2+^Q!3+C1!2'8#56/p1;!3+C1#1/can;#2!2'8<7!4'a;#4#37&heq_LEN;RA@!4'`6!2'B7B!2'GDE!<'L+<+M'B'I'G'N7D!2,?+MDBEF&HL0;RIH&cstr;RKL&cstr0;RMN&__sat4;RRT&__sat3;RVW&__sat2;R[\&__arith;R$__x1;R+M&__wit;R^0^1&__varmap;R^2^3&__ff;R!8,V^4'X+Y+Y,Z^6^7!7,[^4'X+Y+Y,Z!4,\+M!2,^0+MD,^6^5,^3^8^9%__x1;R+M%~R^:!2'GD#2^;!2'8<6!4'a;#4#36&heq_LEN;RA@!4'`6!2'B6B!2'GPE!<'L+<+M'B'I'G'N6P!2,?+MPBEF&HL0;RIH&cstr;RKL&cstr0;RMN&__sat4;RRT&__sat3;RVW&__sat2;R[\&__arith;R$__x1;R+M&__wit;R^0^1&__varmap;R^2^3&__ff;R!8,V^4'X+Y+Y,Z^6^7!7,[^4'X+Y+Y,Z!4,\+M!2,^0+MP,^6^5,^3^8^9%__x1;R+M%~R^:!2'GP#2^;!2'8<5!4'a;#4#35&heq_LEN;RA@!4'`6!2'B5B!2'G^<E!<'L+<+M'B'I'G'N5^<!2,?+M^<BEF&HL0;RIH&cstr;RKL&cstr0;RMN&__sat4;RRT&__sat3;RVW&__sat2;R[\&__arith;R$__x1;R+M&__wit;R^0^1&__varmap;R^2^3&__ff;R!8,V^4'X+Y+Y,Z^6^7!7,[^4'X+Y+Y,Z!4,\+M!2,^0+M^<,^6^5,^3^8^9%__x1;R+M%~R^:!2'G^<#2^;!2'8<,9!4'a;#4#3,9&heq_LEN;RA@!4'`6!2'B,9B!2'G,5E!<'L+<+M'B'I'G'N,9,5!2,?+M,5BEF&HL0;RIH&cstr;RKL&cstr0;RMN&__sat4;RRT&__sat3;RVW&__sat2;R[\&__arith;R$__x1;R+M&__wit;R^0^1&__varmap;R^2^3&__ff;R!8,V^4'X+Y+Y,Z^6^7!7,[^4'X+Y+Y,Z!4,\+M!2,^0+M,5,^6^5,^3^8^9%__x1;R+M%~R^:!2'G,5#2^;!1'a8<").
Qed.

  (* [comment removed for export] *)
  Definition mdl3 (model : Model) (off : Z) : Prop :=
    m_fds model = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 off)) /\ m_fs model = fs0.
  Lemma fds_lookup3A : forall e, fd_lookup (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) = Some e.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$e;R+a=!2,?!1+^D+a=!2,a>+a=#1").
Qed.
  Lemma fds_remove3A : forall e, fd_remove (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) = fds0.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$e;R+a=!2,?!1+0!2+`I!1+1!1,2|600;+a='a?").
Qed.
  Lemma fds_ins3A : forall e e', fd_insert (fd_insert fds0 (Z_to_bv 64 3) e) (Z_to_bv 64 3) e' = fd_insert fds0 (Z_to_bv 64 3) e'.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!1,2|600;$e;R+a=$e';R+a=!2,?!1+0!2+`I!1+10+a=!3'a@'a?!2'40!1,J|11;#1").
Qed.

  (* [comment removed for export] *)
  Definition CAPk (k : Z) : Z := 65536 * 2 ^ k.
  Variables Kc Bc : Z.
  Hypothesis HKc : 0 <= Kc. Hypothesis HBc : 0 <= Bc.
  Definition credA (k : Z) (cr : credit) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'_=!1,J|32;#2|10;!1,J1$k;R+M$cr;R'aA!2+^Q!2'R!2'H!2'^R0!1'aB/L;/Kc;!3'aC+M+M#1!2'R!2'H!2'H!2'^R!1'aD/L;!2'_=!2'_42!1,J|4b;!2'^R2!1'aE#2!2'^R0!1'aF/L;/Bc;!3'aG+M+M#1").

  Lemma CAPk_S : forall k, 0 <= k -> CAPk (k + 1) = 2 * CAPk k.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S\0!2'R,5#1|10;!1,J1!1,J,K!2'_423!1,J|@0000;!2'^R5#1!2'_42#3!2'^R2!2'^R57|30;!2'A!1+1!1,29/fdata;!1'I:!3+C+M/LEN;;vd!2,?+M;<!1'Q:!2'R,5;!1,J|50f;!2'_I2@!2'G,52!2'_42@%~RB%~R!2'R,5@!2'G,5C!2'R,52$Ha;RE$~R+_J!3'_K2@#2%Ha;RE%~R+_J!2'R,5C|600;!2'_7!1,2H/sp0;|40;!1,JJ!2'a9IK%~R!2'R,5I%~R!2'R,5K!2'R,5!2'^SIK!2'_42#:!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^0+M5!2,^2+M,K!2,^0+M2!2'^8S,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'H#23!2,^0+M,5!7,[S'X+Y+Y,Z!4,\+MZ,^1U,^3$k;R+M$Hk;R0vd!6'_>+M!2'^R!2'_42#24$z;R+M!3+C+M68!6'_>+M2$z;R+M!3+C+M!2'^R5!2'^R7#18&heq_LEN;R=<&cstr;R>?&__sat6;RAD&__sat5;RFG&__sat4;RLM&__sat3;R!2'_I2#7%~RB%~R!2'R,5#8!2'G,5!2'_42#9&__sat2;R$Ha;RE$~R+_J!3'_K2#:#2%Ha;RE%~R+_J!2'R,5N&__arith;R$__x1;R+M&__wit;ROP&__varmap;RQR&__ff;R!7,[S'X+Y+Y,Z!4,\+M!3,_3+MT!3,_3+MUV,_2!3,_3+MV!3,_3+MTU,^3WX%__x1;R+M!3+C+M!2'^R5!2'^R#12!2'^R26!1#1N4!1'aH2!2'_42Y!5'aI2#23&heq_LEN;R=<&cstr;R>?&__sat4;RAD&__sat3;RFG&__sat2;RLM&__arith;R$__x1;R+M&__wit;ROP&__varmap;RQR&__ff;R!8,VS'X+Y+Y,Z[!1,^4+Y[WX%__x1;R+M%~R0!2'R,5#2!2#1#8#7&heq_LEN;R=<&cstr;R>?&__sat4;RAD&__sat3;RFG&__sat2;RLM&__arith;R&__wit;ROP&__varmap;R!1,^V+MR&__ff;R!7,[S'X+Y+Y,Z!4,\+MZ,^1!2,^0+M3,^3WX!2'R,53#1!3+C+M!1'aEY!2'^R2!1'aE#2").
Qed.
  Lemma CAPk_range : forall k, 0 <= k <= 10 -> 65536 <= CAPk k <= 67108864.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^J0!1,J|32;!2'R#10|@0000;!1,J2|10;!1,J4!2'_45#2!2'^R36!1,J|J0000000;!2'G,55!2'R,5#3!2'_45,5|30;!2'A!1+1!1,2</fdata;!1'I=!3+C+M/LEN;>vd!2,?+M>?!1'Q=!2'R,5>!1,J|50f;!2'_I5C!2'_45C%~R9%~R!2'R,5C!2'G,5E!2'R,55$Ha;RG$~R+_J!3'_K5C#2%Ha;RG%~R+_J!2'R,5E|600;!2'_7!1,2J/sp0;|40;!1,JL!2'a9KM%~R!2'R,5K%~R!2'R,5M!2'R,5!2'^SKM!2'_45#=!1,:+S!1+0+S!1,^V+M!2,T+M#3!1+U+M!1+W+M!2,^0+M,5!2,^0+M5!7,[V'X+Y+Y,Z!4,\+MW,^6X,^3!1,^4+Y!7,[V'X+Y+Y,Z!4,\+MW,^1!2,^2+M|31;,^3!2,^2+M,K!1,J,K!2'^8V,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'_I5#8%~R9%~R!2'R,5#9!2'G,5!2'_45#:$Ha;RG$~R+_J!3'_K5#;#2!2'_45#;%Ha;RG%~R+_J!2'R,5^6!2,_0+M,9!3,7+S!2,_U^8!2,^X!3,^Y+M^8!2,_0+M}4,_1Q!4,^U+MT#2!4,^U+M!4,^U+M!2,T+M#4#4S#4S!7,^WV'X+Y+Y,Z[!6,^7V'X+Y+Y,Z#6!1,J|^13fff80000000;!7,^WV'X+Y+Y,Z!7,[V'X+Y+Y,Z!4,\+M!2,^0+M^<,^1!2,^2+M4,^3!6,^7V'X+Y+Y,Z#7!2,^0+M3!3,_3+M^>\!2'R,5#4!2+^Q^@#5!2+^Q!2'R^<#4#7!2'^R3#4!2'RKE!2'R#;0!7,[V'X+Y+Y,Z!4,\+M\,^1!2,^0+M0,^3|:000;!1,J^G!1'aE#2$k;R+M$Hk;R!2+^Q!2'R,5#11vd!4,^>!2'R37!2'R78&H;R&H;R!3'aJ5,5#2%~R9%~R:!2'R;!2'_45#4vd&heq_LEN;R@?&cstr;RAB&__sat8;RDF&__sat7;RHI&__sat6;R!2'_I5,5%~R9%~R!2'R,5,5!2'G,5;&__sat5;R$Ha;RG$~R+_J!3'_K5,5#2%Ha;RG%~R+_J!2'R,5;&__sat4;RNO&__sat3;R!2'_I5#:%~R9%~R!2'R,5#;!2'G,5!2'_45#<&__sat2;R$Ha;RG$~R+_J!3'_K5#=#2%Ha;RG%~R+_J!2'R,5P&__arith;R$__p1;Rw$__x2;R+M$__x1;R+M&__wit;RQR&__varmap;R!4,^U+MS#2!4,^U+M!4,^U+MT#3S#3SU&__ff;R!8,VV'X+Y+Y,Z!8,VV'X+Y+Y,ZYZ!8,VV'X+Y+Y,Z[Z!7,[V'X+Y+Y,Z!4,\+M!3,_L+MX,aK,^1\,^3Z!8,VV'X+Y+Y,Z!7,^WV'X+Y+Y,Z[!6,^7V'X+Y+Y,Z#5Z!7,[V'X+Y+Y,Z!4,\+M!2,^0+M^0,^1\,^3^1^2%__p1;Rw%__x2;R+M%__x1;R+M%~R%~R9%~R:!2'R;#3%~R!2+^Q:#4!2'R^0#3!5#1!2'R#=0#=P#;#<!2'R^0!2'_45#3!2'R^06&heq_LEN;R@?&cstr;RAB&__sat6;RDF&__sat5;RHI&__sat4;RNO&__sat3;R^3^4&__sat2;R^5^7&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R^9R&__varmap;R^:U&__ff;R!8,VV'X+Y+Y,Z!8,VV'X+Y+Y,ZYZ!8,VV'X+Y+Y,Z[Z!7,[V'X+Y+Y,Z!4,\+MW,^6\,^3Z!8,VV'X+Y+Y,Z^;Z!8,VV'X+Y+Y,Z^=Z!7,[V'X+Y+Y,Z!4,\+M^>,^1^?,^3^1^2%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R%~R9%~R^@!2'G,5#3%~R^A%~R^B!2'R3^C!8#1^D^E#;K^6#3#:/Hsp;&H;R!5'aJ5#20&heq_LEN;R@?&cstr;RAB&__sat4;RDF&__sat3;RHI&__sat2;RNO&__arith;R&__wit;RQR&__varmap;RSU&__ff;RY^1^29#1&heq_LEN;R@?&cstr;RAB&__sat4;RDF&__sat3;RHI&__sat2;RNO&__arith;R$__p1;Rw$__x1;R+M&__wit;RQR&__varmap;R!2,T+M#2U&__ff;R!8,VV'X+Y+Y,Z!7,^WV'X+Y+Y,Z!6,^7V'X+Y+Y,Z#4^FZ^F^1^2%__p1;Rw%__x1;R+M%~R!2+^Q#21!2'R#20!3#1!2'R,5#8#8#7!2'R6!2'_450&heq_LEN;R@?&cstr;RAB&__sat6;RDF&__sat5;RHI&__sat4;RNO&__sat3;R^3^4&__sat2;R^5^7&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R^9R&__varmap;R^:U&__ff;R!8,VV'X+Y+Y,Z!7,[V'X+Y+Y,Z!4,\+M\,^1!2,^0+M^H,^3Z!8,VV'X+Y+Y,Z^;Z!8,VV'X+Y+Y,Z^=Z!7,[V'X+Y+Y,Z!4,\+M^?,^1!2,^0+M8,^3^1^2%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R#1^H%~R^A%~R^B!2'R^C8!8#1^D^E#;K^6#9#:/Hsp;!2+^Q!2'R3^I!2'R^I8").
Qed.
  Lemma CAPk_lt10 : forall k, 0 <= k < 10 -> CAPk k <= 33554432.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^00!1,J|32;!2'G#10|10;!1,J2|31;!1,J4|30;!2'A!1+1!1,26/fdata;!1'I7!3+C+M/LEN;8vd!2,?+M89!1'Q7!2'R,58!1,J|50f;!2'_I3=!2'G,53!2'_43=%~R?%~R!2'R,5=!2'G,5@!2'R,53$Ha;RB$~R+_J!3'_K3=#2%Ha;RB%~R+_J!2'R,5@|600;!2'_7!1,2E/sp0;|40;!1,JG!2'a9FH%~R!2'R,5F%~R!2'R,5H!2'R,5!2'^SFH!1,:+S!1+0+S!1,^V+M!1+U+M!1+W+M!2,^0+M,5!2'^8O,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2,^2+M,K!1,^4+Y!2'_43#;!2,_0+M,9|9000;!1,JW!1,J|^13fff80000000;|@0000;!1,JZ!1,J|I0000000;$k;R+M$Hk;R!2+^Q!2'R,5#11vd&H;R!5'aJ3#25&heq_LEN;R:9&cstr;R;<&__sat4;R>A&__sat3;RCD&__sat2;RIJ&__arith;R&__wit;RKL&__varmap;RMN&__ff;R!7,[O'X+Y+Y,Z!4,\+MP,^6!2,^0+M3,^3QR?#1&heq_LEN;R:9&cstr;R;<&__sat4;R>A&__sat3;RCD&__sat2;RIJ&__arith;R$__p1;Rw$__x1;R+M&__wit;RKL&__varmap;R!2,T+M#2N&__ff;R!8,VO'X+Y+Y,Z!7,^WO'X+Y+Y,Z!6,^7O'X+Y+Y,Z#4!7,[O'X+Y+Y,Z!4,\+MS,^6!2,^0+M0,^3T!7,[O'X+Y+Y,Z!4,\+MS,^1!2,^0+M5,^3QR%__p1;Rw%__x1;R+M%~R!2+^Q#21!2'R#25!3#1!2'R,5#8#8#7!2'R!2'_43#2!2'_435&heq_LEN;R:9&cstr;R;<&__sat6;R>A&__sat5;RCD&__sat4;RIJ&__sat3;R!2'_I3#8%~R?%~R!2'R,5#9!2'G,5!2'_43#:&__sat2;R$Ha;RB$~R+_J!3'_K3#;#2%Ha;RB%~R+_J!2'R,5U&__arith;R$__p2;Rw$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,_UV!2,^X!3,^Y+MV!2,_0+M}4,_1KL&__varmap;R!4,^U+M!2,T+M#3#2!4,^U+M!4,^U+M!2,T+M#4#4M#4MN&__ff;R!8,VO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MS,^1!2,^0+MX,^3T!8,VO'X+Y+Y,Z!7,^WO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+MP,^1!2,^2+M4,^3!6,^7O'X+Y+Y,Z#6T!8,VO'X+Y+Y,Z!7,^WO'X+Y+Y,Z!7,[O'X+Y+Y,Z!4,\+M!2,^0+MY,^1!2,^2+M2,^3!6,^7O'X+Y+Y,Z#7T!7,[O'X+Y+Y,Z!4,\+M!3,_3+M!2,^0+M[S,^1!2,^0+M\,^3QR%__p2;Rw%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R#1X%~R!2+^Q!2'R,5#4#5%~R!2+^Q!2'RY#4#7!2'R!2'^R[#4\!8#1!2'RF@!2'G#;0#;FU#9#:/Hsp;!2'R!1'aE#2\").
Qed.
  Lemma credA_exit : forall k cr, 0 <= k <= 10 -> credA k cr -> Kc <= fst cr /\ Bc <= snd cr.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^J0|32;!1,J0!2'_=1#4!1'aB/L;!2'R!2'H!2'^R23/Kc;!3'aC+M+M#3!1'aD/L;|10;!1,J6|4b;!1,J8!2'_479!1'aF/L;|@0000;!1,J<!1'aE#8|J0000000;!1,J?!2'R,53!2'R,55!2'R,5;!2+^QBC|30;!2'A!1+1!1,2E/fdata;!1'IF!3+C+M/LEN;G|50f;!1,JI!2'G,57!2'_47J!2'R,57%~R+_J!2'R,5L|600;!2'_7!1,2O/sp0;|40;!1,JQ!2,_0+M}9}5!3,aN+MS!2,_0+M,9|^2000000000000;!2,aO+M!1,JV}8}3!2,_0+MY}7}6}4}2!1,^V+M!1+W+M!2,^0+M,5!2,^0+M7!1,^4+Y!2,^2+M|31;!2,^2+ME|33;!2,^2+M^9!2,^0+M1!2,^2+M0!3,_N+M^;^<|11;!2,^2+M^>|20;!2,^2+M^@|23;!2,^2+M^B!2,^2+M,K!2,^2+M6!1,J|^13fff80000000;|21;!2'R,5#9!1'aE#J$k;R+M$cr;R'aA$Hk;R!2+^Q!2'R,5#2!2'R#21$H;R!2'aL#3#2!5'_64!2'R!2'H!2'H!2'^R5!2'_=:!2'^R7!1'aE#4!2'^R2;/Bc;!3'aG+M+M#3!2+^Q!2'R/Kc;!3'aC+M+M#3!2'R/Bc;!3'aG+M+M#3$~R4$~R!2'R!2'H!2'H!2'^R5!2'_=:!2'^R7!1'aE#5!2'^R!2'_=1#5;/Bc;!3'aG+M+M#4!2$C1;R!2'R!2'H!2'^R!2'_=1#63/Kc;!3'aC+M+M#5$C2;R!2'R!2'H!2'H!2'^R5!2'_=:!2'^R7!1'aE#7!2'^R!2'_=1#7;/Bc;!3'aG+M+M#6&H;R!2'aM#8#6!2+^Q!2'R=>!2'R>@&a;R/HCOST;!2+^QAD!5'_6AD!2+^Q!2'R/Kc;!3'aC+M+M#9!2'R/Bc;!3'aG+M+M#9$~RA$~RD!2$H1;RA$H0;RD!5'_6BC!2+^Q!2'R/Kc;!3'aC+M+M#=!2'R/Bc;!3'aG+M+M#=$~RB$~RC!2$H2;RB$H3;RC&heq_LEN;Rvd!2,?+MGHH&cstr;R!1'QF!2'R,5G&__sat8;R!2'_I7J%~RK%~R!2'R,5J!2'G,5L&__sat7;R$Ha;RM$~R+_J!3'_K7J#2%Ha;RMN&__sat6;R!2'_I79%~RK%~R!2'R,59!2'G,5:&__sat5;R$Ha;RM$~R+_J!3'_K79#2%Ha;RM%~R+_J!2'R,5:&__sat4;R!2'a9PR%~R!2'R,5P%~R!2'R,5R!2'R,5!2'^SPR&__arith;R$__p4;Rw$__p3;Rw$__p2;Rw$__p1;Rw$__x10;R+M$__x9;R+M$__x8;R+M$__x7;R+M$__x6;R+M$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!3,aN+MS!2,_0+MT!3,^Y+MU!3,^Y+M!3,aN+MW!3,aN+M!2,_0+MXZ!3,aN+M!2,aO+M!1,J|^3000000000000;!3,aN+M!2,_0+M[!2,_0+M\,_1!3,7+S!2,^X!3,^Y+M!3,aN+MS!2,_0+M^0!3,^Y+MU!3,aN+MW!3,aN+M!2,_0+M^1Z,_1!1,:+S!1+0+S&__varmap;R!4,^U+M!4,^U+M!4,^U+M!2,T+M#8#5^2#3!4,^U+M!2,T+M#:#;^2#2!4,^U+M!4,^U+M!2,T+M#9#6^2#4!4,^U+M!2,T+M#;#7^2!1+U+M&__ff;R!8,V^3'X+Y+Y,Z!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^4,^1^5,^3^6!8,V^3'X+Y+Y,Z!5,`Y^3'X+Y+Y,Z^6!7,[^3'X+Y+Y,Z!4,\+M^4,^1!3,_L+M^5!1,2I,^3^6!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^4,^1^7,^3^6!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^4,^1^8,^3^6!8,V^3'X+Y+Y,Z!7,^W^3'X+Y+Y,Z!6,^7^3'X+Y+Y,Z#=!7,[^3'X+Y+Y,Z!4,\+M^:,^1!2,^0+M@,^3^6!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M!3,^5+M!3,^5+M!3,_3+M^8!3,_N+M!3,_L+M^5!1,28!3,_3+M^5^:!3,_3+M^=^7^?,^1^A,^3^6!8,V^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M!3,^5+M!3,_3+M^=^C^D,^1^E,^3^6!8,V^3'X+Y+Y,Z!7,^W^3'X+Y+Y,Z!6,^7^3'X+Y+Y,Z#>!7,[^3'X+Y+Y,Z!4,\+M^<,^1^;,^3^6!8,V^3'X+Y+Y,Z!7,^W^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^4,^1^C,^3!6,^7^3'X+Y+Y,Z#?^6!8,V^3'X+Y+Y,Z!7,^W^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M!2,^0+M^F,^1!2,^2+M^G,^3!6,^7^3'X+Y+Y,Z#@^6!7,^W^3'X+Y+Y,Z!7,[^3'X+Y+Y,Z!4,\+M^D,^1^E,^3!7,[^3'X+Y+Y,Z!4,\+M^?,^1^A,^3!2'^8^3,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__p4;Rw%__p3;Rw%__p2;Rw%__p1;Rw%__x10;R+M%__x9;R+M%__x8;R+M%__x7;R+M%__x6;R+M%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R%~RMN%~R^H%~R^H%~R!2+^Q#>!2'R#=@%~R!2'R!2'H!2'H!2'^R#;!2'_=:!2'^R7#>!2'^R!2'_=1#=#<#7#8%~R!2'R!2'H!2'^R!2'_=1#>#;#6#7%~R!2+^Q#B!2'R#?1%~R!2+^Q!2'R,5#=#D%~R!2+^Q!2'R^F#=#F!2+^Q!2'R#:#;!2'R#<#=!G#1!2'RPLD!2'R,5#J!2'R=^I^I#J;53P!3'aG+M+M#I/Bc;!3'aC+M+M#I/Kc;#5#9#:#B#C#D#H/HCOST;/Hsp;#2#1#1#2#1#1#2#1#1").
Qed.

  (* [comment removed for export] *)
  Lemma inv_block1 : forall LB LK cr A M model u n, dinvA LB LK cr A M model -> In (u, n) LB ->
    ablock_range L ar u n /\ defined M u n /\ hzA sp0 u n.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^@0!2+`I+M+M!1+00|600;|30;!1,:'aP!3'aC+M+M#2!3'aG+M+M#2!4'aW/L;/ar;56!1'b0/ar;!2'H8'b1!2+`@!2'R!2'H568!2'R95!3'aS'aP#14!1'b2#2!2'R8<!1'b4#2!1'b3>!2'R!2'H<?9!3+C+M!2'^S<?,5!3'aS+M>'b5!2'b6<4!2'b78'b1!1'b8/ar;!1,J|G000000;!2'_=EF!2'R9G!2+`@!2'R9!1'b9/L;!2'R!1'b:/L;8!2'_=EG!1'b;/ar;|<000;!1,JL!2+^Q!2'RG!2'HKM!2'RK!2'HGM!1'b</ar;|10;!2'_4!1,JP!1,J|50f;|40;!2+^Q!3+C+M!2'^SKM,5!2+^Q!3+C+MO!2'HKF!2+^Q!2+^Q!2'R!1,J|^13fff80000000;E!2'REQ!3+C+M!2'^SE!1,JR,5!2'ROQ!2'aC+M+M%b;R0%~R!3'aS0#1#<!2+^Q7!2+^Q!3'aX#956!2+^Q!3'aY#956!2+^Q!3'aZ#:56!2+^Q!3'a[56!2'`L5#=!2+^Q!3'a\56!3'6'aP4#<:!3'6'aP4#>!4,`J+M+M#9#8!3'aC+M+MX!3'aG+M+MX!4,`J+M+M#:#9!3'aC+M+M[!3'aG+M+M[!4'aW/L;/ar;\^0!4,`J+M+M#<#;!4,`J+M+M#=#<!3'aC+M+M^3!3'aG+M+M^3!4,`J+M+M#>#=!3'aC+M+M^6!3'aG+M+M^6!3'aX#@^7^8!4,`J+M+M#@#?!4,`J+M+M#A#@!3'aC+M+M^;!3'aG+M+M^;!3'aX#D#B#A!3'b>/sp0;#B#A$LB;R1$LK;R!1+0'aP$cr;R'aA$A;R1$M;R%~R!1+1!1,22!1+^D!1+1!1,23$model;R+aQ$u;R+M$n;R+M$D;R!:+aR/ar;/HI;/sp0;/M0;#8#7#6#5#4#3$Hin;R!3'aS0!4,`J+M+M#3#2#9&a;R!>'aT/L;/ar;/C;/scfg;/HI;/HIok;#:4#9#8#7#6!1'aU#5!;'aV/ar;/HI;/sp0;/M0;#:#9#8#7#6#5#2!2+^Q%b;R0%~R!3'aS0#1#;!2+^Q7!2+^Q!3'aX#856!2+^Q!3'aY#856!2+^Q!3'aZ#956!2+^Q!3'a[56!2'`L5#<!2+^Q!3'a\56!3'6'aP4#;:!2+^Q%f;R'aP%~R;!2+^Q=!2+^Q@!2+^QA!2+^QB!2+^Q!3'aX#8<?!3'a\<?!3'6'aPC#;!2+^QD!2+^QH!2+^QI!2+^Q!3'aZ#78'b1!2+^Q!3'aZ#7GJ!2+^QN!2+^QS!2+^QT!2+^Q!2+b=+M!4';0+MU#:!2+^Q!2+b=+M!4';'aP+M'b2!3'6'aP4#9!2+^Q!2'R,5!3'aC+M+M#8!2+^Q!2'R,5!3'aG+M+M#8!3'aX#68'b1!5'_6V!2+^Q%f;R'aP%~R;!2+^Q=!2+^Q@!2+^QA!2+^QB!2+^Q!3'aX#9<?!3'a\<?!3'6'aPC#<!2+^QD!2+^QH!2+^QI!2+^Q!3'aZ#88'b1!2+^Q!3'aZ#8GJ!2+^QN!2+^QS!2+^QT!2+^Q!2+b=+M!4';0+MU#;!2+^Q!2+b=+M!4';'aP+M'b2!3'6'aP4#:!2+^Q!2'R,5!3'aC+M+M#9!2+^Q!2'R,5!3'aG+M+M#9!3'aX#78'b1!2+^Q!4'aW/L;/ar;#5#4!2+^Q!3'aX#7#5#4!3'b>/sp0;#5#4$~RV$~R!2+^Q%f;R'aP%~R;!2+^Q=!2+^Q@!2+^QA!2+^QB!2+^Q!3'aX#:<?!3'a\<?!3'6'aPC#=!2+^QD!2+^QH!2+^QI!2+^Q!3'aZ#98'b1!2+^Q!3'aZ#9GJ!2+^QN!2+^QS!2+^QT!2+^Q!2+b=+M!4';0+MU#<!2+^Q!2+b=+M!4';'aP+M'b2!3'6'aP4#;!2+^Q!2'R,5!3'aC+M+M#:!2+^Q!2'R,5!3'aG+M+M#:!3'aX#88'b1!2$WF;R%b;R0%~R!3'aS0#1#>!2+^Q7!2+^Q!3'aX#;56!2+^Q!3'aY#;56!2+^Q!3'aZ#<56!2+^Q!3'a[56!2'`L5#?!2+^Q!3'a\56W:$_H;R!2+^Q%f;R'aP%~R;!2+^Q=!2+^Q@!2+^QA!2+^QB!2+^Q!3'aX#<<?!3'a\<?!3'6'aPC#?!2+^QD!2+^QH!2+^QI!2+^Q!3'aZ#;8'b1!2+^Q!3'aZ#;GJ!2+^QN!2+^QS!2+^QT!2+^Q!2+b=+M!4';0+MU#>!2+^Q!2+b=+M!4';'aP+M'b2!3'6'aP4#=!2+^Q!2'R,5!3'aC+M+M#<!2+^Q!2'R,5!3'aG+M+M#<!3'aX#:8'b1&a;R!2#2X#6!2+^Q!4'aW/L;/ar;YZ!2+^Q!3'aX#;YZ!2+^Q!3'aY#;YZ!2+^Q!3'aZ#<YZ!2+^Q!3'a[YZ!2'`LY#?!2+^Q!3'a\YZW!2+`@!2'R!2'HYZ8!2'R9Y!5'_6^1!2+^Q!3'aX#<\^0!2+^Q!3'aY#<\^0!2+^Q!3'aZ#=\^0!2+^Q!3'a[\^0!2'`L\#@!2+^Q!3'a\\^0!3'6'aP4#?!2+`@!2'R!2'H\^08!2'R9\!2+^Q!4'aW/L;/ar;#:#9!2+^Q!3'aX#<#:#9!3'b>/sp0;#:#9$~R^1$~R!2+^Q!3'aX#=!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:!2+^Q!3'aY#=!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:!2+^Q!3'aZ#>!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:!2+^Q!3'a[!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:!2'`L!3'aC+M+M!4,`J+M+M#;#:#A!2+^Q!3'a\!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:!3'6'aP4#@!2+`@!2'R!2'H!3'aC+M+M!4,`J+M+M#;#:!3'aG+M+M!4,`J+M+M#;#:8!2'R9!3'aC+M+M!4,`J+M+M#;#:!2$B;R!4'aW/L;/ar;!3'aC+M+M^2!3'aG+M+M^2$H;R!2+^Q!3'aX#?^4^5!2+^Q!3'aY#?^4^5!2+^Q!3'aZ#@^4^5!2+^Q!3'a[^4^5!2'`L^4#C!2+^Q!3'a\^4^5!3'6'aP4#B!2+`@!2'R!2'H^4^58!2'R9^4!5'_6^9!2+^Q!3'aY#@^7^8!2+^Q!3'aZ#A^7^8!2+^Q!3'a[^7^8!2'`L^7#D!2+^Q!3'a\^7^8!3'6'aP4#C!2+`@!2'R!2'H^7^88!2'R9^7!2+^Q!4'aW/L;/ar;#>#=!2+^Q!3'aX#@#>#=!3'b>/sp0;#>#=$~R^9$~R!2+^Q!3'aY#A!3'aC+M+M!4,`J+M+M#?#>!3'aG+M+M!4,`J+M+M#?#>!2+^Q!3'aZ#B!3'aC+M+M!4,`J+M+M#?#>!3'aG+M+M!4,`J+M+M#?#>!2+^Q!3'a[!3'aC+M+M!4,`J+M+M#?#>!3'aG+M+M!4,`J+M+M#?#>!2'`L!3'aC+M+M!4,`J+M+M#?#>#E!2+^Q!3'a\!3'aC+M+M!4,`J+M+M#?#>!3'aG+M+M!4,`J+M+M#?#>!3'6'aP4#D!2+`@!2'R!2'H!3'aC+M+M!4,`J+M+M#?#>!3'aG+M+M!4,`J+M+M#?#>8!2'R9!3'aC+M+M!4,`J+M+M#?#>!2$Df;R!3'aX#B!3'aC+M+M^:!3'aG+M+M^:$_H;R!2+^Q!3'aY#C^<^=!2+^Q!3'aZ#D^<^=!2+^Q!3'a[^<^=!2'`L^<#G!2+^Q!3'a\^<^=!3'6'aP4#F!2+`@!2'R!2'H^<^=8!2'R9^<!4,^>!4'aW/L;/ar;#B#A!2+^Q^>^?#6!4,^>^>^?#2!8'b?/L;/ar;/IL;/sp0;/DL;#B#A#6#2#1#1#2#1#1#2#1#1").
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable K : TSet.
  Hypothesis HK0 : K [].

  (* [comment removed for export] *)
  Definition close_kgA (CAP : Z) (crC : credit) (KC : TSet) : Prop :=
    forall vals R M (model : Model) A (A1 : Z),
      length vals = 71%nat -> hdr_valsA vals -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 LEN ->
      regs_ok (ENVG vals) srGLA R ->
      (forall lo hi, lo <= LEN <= hi -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) (knGA lo hi)) ->
      rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata ->
      dinvA [(A1, CAP)] LK0 crC A M model -> incl A0 A ->
      m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x153a7c) M (seg_rom ASEGS)) model) KC.

  (* [comment removed for export] *)
  Definition lp_atA (z : Z) : Prop := forall (k len A1 : Z) vals R M (model : Model) A cr,
      0 <= k <= 10 -> 0 <= len <= CAPk k -> len <= LEN -> LEN - len <= z ->
      length vals = 71%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
      regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb0138) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition rd_atA (z : Z) : Prop := forall (k len want A1 : Z) vals R M (model : Model) A cr,
      0 <= k <= 10 -> 0 <= len < CAPk k -> len <= LEN -> LEN - len <= z ->
      want = Z.min (CAPk k - len) 65536 ->
      length vals = 72%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 (CAPk k) -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 len ->
      vals_ev vals 71 = Z_to_bv 64 want ->
      regs_ok (ENVG vals) srRDA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata) ->
      dinvA [(A1, CAPk k)] LK0 cr A M model -> incl A0 A -> mdl3 model len -> credA k cr ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6b93c) M (seg_rom ASEGS)) model) K.

  (* [comment removed for export] *)
  Definition refuse_kA (KR : TSet) : Prop := forall (A1 : Z) vals R M (model : Model) A cr,
      length vals = 71%nat -> hdr_valsA vals ->
      vals_ev vals 38 = Z_to_bv 64 67108864 -> vals_ev vals 48 = Z_to_bv 64 A1 -> vals_ev vals 70 = Z_to_bv 64 67108864 ->
      regs_ok (ENVG vals) srLPA R -> know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) knLPA ->
      dinvA [(A1, 67108864)] LK0 cr A M model -> incl A0 A -> mdl3 model 67108864 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb0138) M (seg_rom ASEGS)) model) KR.

  (* [comment removed for export] *)
  Hypothesis HKC : LEN < 67108864 -> forall CAP crC,
      65536 <= CAP <= 67108864 -> LEN < CAP -> Kc <= fst crC -> Bc <= snd crC -> close_kgA CAP crC K.
  Hypothesis HREF : 67108864 <= LEN -> refuse_kA K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac norm_srget := repeat match goal with |- context [sr_get ?sr ?r] =>
                      let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end.
  Ltac norm_nth := repeat match goal with |- context [nth ?i ?l (ELit 0)] =>
                      let x := eval vm_compute in (nth i l (ELit 0)) in change (nth i l (ELit 0)) with x end.
  Ltac relay1 HR :=
    norm_nth;
    first [ lia
          | reflexivity
          | rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA]; reflexivity
          | idtac ].
  Ltac relay_loop HR i :=
    first [ lia | let j := fresh "i" in destruct i as [|j]; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; relay1 HR | relay_loop HR j ] ].
  Ltac relay_regs HR := apply regs_ok_by_nth; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; relay_loop HR i.
  Ltac relay2 HR :=
    rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA];
    rewrite ?relayV_38, ?relayV_48, ?relayV_70, ?relayV_71; unfold gr;
    rewrite ?(reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].
  Ltac regv1 HR := rewrite (reg_val _ _ _ _ HR); norm_srget; cbn [edenot ev ENVA].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma sc_eq_70_38A : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap ->
    0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> Z.eqb len cap = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_EQ (EVar 70) (EVar 38)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S\0|600;!1,20!1+11|30;!1+1!1,23}^I!2'41#3}V|10;!1,J8!1,J0!2'_49:!2+^Q!2'R,5#5!2'G#5;!2'41#8!2'41#7!2'_71=!2'A4/fdata;!1'I@!3+C+M/LEN;Avd!2,?+MAB!1'Q@!2'R,5A!1,J|50f;!2'_I9F!2'G,59!2'_49F%~RH%~R!2'R,5F!2'G,5I!2'R,59$Ha;RK$~R+_J!3'_K9F#2%Ha;RK%~R+_J!2'R,5I!2'_I9:%~RH%~R!2'R,5:!2'G,5;$Ha;RK$~R+_J!3'_K9:#2%Ha;RK%~R+_J!2'R,5;!2'_71/sp0;|40;!1,JS!2'a9RT%~R!2'R,5R%~R!2'R,5T!2'R,5!2'^SRT!1+W+M!2,^2+M,K!7,^WW'X+Y+Y,Z!7,[W'X+Y+Y,Z!4,\+M!2,^0+M,5,^1X,^3!7,[W'X+Y+Y,Z!4,\+MX,^6!3,_L+M!2,^0+M91,^3$__x1;R+M&__wit;R!1,:+S!1+0+S&__varmap;R!2,T+M#2!1+U+M&__ff;R!8,VW'X+Y+Y,ZY!1,^4+YY!2'^8W,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2%__x1;R+M%~R!2+^Q!2'R,5#1!2'G#1;!2+^Q!2'R,5#2!2'G#2;$vals;R!1+02$M;R%~R2!1+^D4$len;R+M$cap;R+M$t;R+^:$P70;R!3+C2!2'8#556$P38;R!3+C2!2'8#676$Hl;R<$Hc;R<$Ht;R!3+C+^:!2'`F#7#6#5vd!6'_>2=$b;R2!3+C+^:!3'`S1#1!2'8#;7#7!6'_>2>$b;R2!3+C+^:!3'`S1!2'41#9#1#7vd!6'_>+M#8$z;R+M!3+C+^:!2'`F#1?#7!6'_>+M#7$z;R+M!3+C+^:!2'`F#9#1#7#1!2'_71>!2'_V#7&heq_LEN;RCB&cstr;RDE&__sat75;RGJ&__sat74;RLM&__sat73;RNO&__sat72;RPQ&__sat71;RUV&__arith;RZ[!2#1#?#:?!2'_V#8&heq_LEN;RCB&cstr;RDE&__sat75;RGJ&__sat74;RLM&__sat73;RNO&__sat72;RPQ&__sat71;RUV&__arith;RZ[!2#1#@#;!3+C+^:!3'`S1=>#6!2'8#:7#4!2'8#:5#5!4'b@'^G#9!2'bA/fdata;#:!4,bB#6,bC!1,bD5!1,bD7").
Qed.
  Lemma want_x_valA : forall vals (len cap : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    edenot (ENVG vals) want_xA = Z_to_bv 64 (cap - len).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^10|600;!1,20!1+11}^I!2'41#2}V|10;!1,J6!1,J0!2'_478!2'41!1,^\,K!2'41!2'_=#6#7|30;!2'A!1+1!1,2</fdata;!1'I=!3+C+M/LEN;>vd!2,?+M>?!1'Q=!2'R,5>!1,J|50f;!2'_I7C!2'G,57!2'_47C%~RE%~R!2'R,5C!2'G,5F!2'R,57$Ha;RH$~R+_J!3'_K7C#2%Ha;RH%~R+_J!2'R,5F!2'_I78%~RE%~R!2'R,58!2'G,59$Ha;RH$~R+_J!3'_K78#2%Ha;RH%~R+_J!2'R,59!2'_71/sp0;|40;!1,JP!2'a9OQ%~R!2'R,5O%~R!2'R,5Q!2'R,5!2'^SOQ!1,:+S!1+0+S!1+U+M!1+W+M!2,^2+M,K!7,^WW'X+Y+Y,Z!7,[W'X+Y+Y,Z!4,\+M!2,^0+M,5,^1X,^3!7,[W'X+Y+Y,Z!4,\+MX,^1!2,^2+M6,^3!1,^4+Y!2'^8W,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!7,[W'X+Y+Y,Z!4,\+MX,^6!3,_L+M!2,^0+M71,^3$vals;R!1+02$len;R+M$cap;R+M$P70;R!3+C2!2'8#334$P38;R!3+C2!2'8#454$H1;R!2+^Q!2'R,5#4!2'R#4#3$H2;R!2'G#49vd!6'_>2!2'41#6$b;R2!3+C2!3'_9,_:!2'8#85!4'_;1,_<:#1;!6'_>2!2'41#5$b;R2!3+C2!3'_9,_:#1!4'_;1,_<:!2'41#7;!4'bE#5#6&heq_LEN;R@?&cstr;RAB&__sat75;RDG&__sat74;RIJ&__sat73;RKL&__sat72;RMN&__sat71;RRS&__arith;R$__x2;R+M$__x1;R+M&__wit;RTU&__varmap;R!4,^U+M!2,T+M#3#2!1,^V+MV&__ff;R!8,VW'X+Y+Y,ZYZY[\%__x2;R+M%__x1;R+M%~R!2+^Q!2'R,5#1!2'R#1#2!2+^Q!2'R,5#2!2'R#2#3!3#1#=#>#:&heq_LEN;R@?&cstr;RAB&__sat75;RDG&__sat74;RIJ&__sat73;RKL&__sat72;RMN&__sat71;RRS&__arith;R$__x1;R+M&__wit;RTU&__varmap;R!2,T+M#2V&__ff;R!8,VW'X+Y+Y,Z^0Z^0[\%__x1;R+M%~R!2'G#19!2'G#29!2#1#=#9!2'8#75#3!2'8#73#4!3+C2!2'`P!2'bA/fdata;#7'bF!2'41!2'_=#5#6").
Qed.
  Lemma sc_ltu_wantA : forall vals M (len cap : Z) t,
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len <= cap -> cap < 2 ^ 64 ->
    Z.ltb (cap - len) 65536 = t ->
    sc_denot ASEGS M (ENVG vals) (SCBr t BC_LTU want_xA (ELit 65536)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^>0|600;!1,20!1+11|30;!1+1!1,23!2'41#3}V|10;!1,J7!1,J0!2'_489!1,J|@0000;!2'_=#7#8!2'41<!1,`R;!2'41;!2'_71?!2'A4/fdata;!1'IA!3+C+M/LEN;Bvd!2,?+MBC!1'QA!2'R,5B!1,J|50f;!2'_I8G!2'G,58!2'_48G%~RI%~R!2'R,5G!2'G,5J!2'R,58$Ha;RL$~R+_J!3'_K8G#2%Ha;RL%~R+_J!2'R,5J!2'_I89%~RI%~R!2'R,59!2'G,5:$Ha;RL$~R+_J!3'_K89#2%Ha;RL%~R+_J!2'R,5:!2'_71/sp0;|40;!1,JT!2'a9SU%~R!2'R,5S%~R!2'R,5U!2'R,5!2'^SSU!1,:+S!1+0+S!1+U+M!1+W+M!2,^0+M,5!2,^0+M;!3,_L+M!2,^0+M81!2'^8[,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2}4}3!2,^2+M,K!1,^4+Y!2,^2+M7!1,J|^13fff80000000;|11;!3,_N+M^6^8!2'_=#4#5!2'bA/fdata;#:$vals;R!1+02$M;R%~R2!1+^D4$len;R+M$cap;R+M$t;R+^:$P70;R!3+C2!2'8#5}^I5$P38;R!3+C2!2'8#665$H1;R!2+^Q!2'R,5#5!2'R#5#4$H2;R!2'G#5:$Ht;R!3+C+^:!2'bG!2'_=#6#7;#5vd!6'_>2=$b;R2!3+C+^:!3'bH1#1!2'`P!2'bA/fdata;#;>#7vdvd!6'_>+M<$z;R+M!3+C+^:!2'bG#1@#7!6'_>+M;$z;R+M!3+C+^:!2'bG!2'_=#8#9#1#7#1@!2'_V;&heq_LEN;RDC&cstr;REF&__sat75;RHK&__sat74;RMN&__sat73;ROP&__sat72;RQR&__sat71;RVW&__arith;R&__wit;RXY&__varmap;R!1,^V+MZ&__ff;R!7,^W['X+Y+Y,Z!7,[['X+Y+Y,Z!4,\+M\,^1^0,^3!7,[['X+Y+Y,Z!4,\+M^0,^6^1,^3^2^3!2+^Q!2'R,5;!2'G;:#1!2'_71=!2'_V<&heq_LEN;RDC&cstr;REF&__sat75;RHK&__sat74;RMN&__sat73;ROP&__sat72;RQR&__sat71;RVW&__arith;R$__p1;Rw$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M!2,_0+M^4!3,^Y+M!2,_0+M^5!2,_0+M,9,_1XY&__varmap;R!4,^U+M!2,T+M#3#2!2,T+M#4Z&__ff;R!8,V['X+Y+Y,Z!7,[['X+Y+Y,Z!4,\+M^6,^6^1,^3^7!8,V['X+Y+Y,Z!7,^W['X+Y+Y,Z!7,[['X+Y+Y,Z!4,\+M\,^1^8,^3!7,[['X+Y+Y,Z!4,\+M^8,^1^6,^3^7!8,V['X+Y+Y,Z!7,^W['X+Y+Y,Z!7,[['X+Y+Y,Z!4,\+M!2,^0+M^9,^1!2,^2+M^:,^3!6,^7['X+Y+Y,Z#6^7!7,^W['X+Y+Y,Z!7,[['X+Y+Y,Z!4,\+M\,^1^;,^3!7,[['X+Y+Y,Z!4,\+M^;,^6^1,^3^2^3%__p1;Rw%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'G#1:%~R!2+^Q!2'R,5#3!2'R#3#2%~R!2+^Q!2'R^9#5#6!2+^Q!2'R,5^<!2'G^<:!7#1!2'RSJS#@#?#:#;/Hsp;!3+C+^:!3'bH1=?#6!3+C+^:!3'bH1=!2'`P^=>#6!2'`P^='bF!7'bI#:#8#7#5#4#3#2!4'b@'^G#9^=!4,bB#6,bJ'bF>").
Qed.
  Lemma cap2_x_valA : forall vals (cap : Z),
    vals_ev vals 70 = Z_to_bv 64 cap -> 0 <= cap -> 2 * cap < 2 ^ 64 ->
    edenot (ENVG vals) cap2_xA = Z_to_bv 64 (2 * cap).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^00|600;!1,20!1+11}^I!2'R,5#2|10;!1,J5!1,J0!2'_467|30;!2'A!1+1!1,29/fdata;!1'I:!3+C+M/LEN;;vd!2,?+M;<!1'Q:!2'R,5;!1,J|50f;!2'_I6@!2'G,56!2'_46@%~RB%~R!2'R,5@!2'G,5C!2'R,56$Ha;RE$~R+_J!3'_K6@#2%Ha;RE%~R+_J!2'R,5C!2'_I67%~RB%~R!2'R,57!2'G,58$Ha;RE$~R+_J!3'_K67#2%Ha;RE%~R+_J!2'R,58!2'_71/sp0;|40;!1,JM!2'a9LN%~R!2'R,5L%~R!2'R,5N!2'R,5!2'^SLN!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^2+M,K!7,[U'X+Y+Y,Z!4,\+M!2,^0+M,5,^1V,^3!1,^4+Y!2'^8U,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2,^0+M6!7,[U'X+Y+Y,Z!4,\+M!3,_3+M[V,^6!3,_L+M[1,^3$vals;R!1+02$cap;R+M$P70;R!3+C2!2'8#23!2'41#1$H1;R4$H2;R!2'G!2'^R6#38vd!6'_>2!2'41#4$b;R2!3+C2!4'_;1,_<!2'416#1!2'41!2'^R6#5!3'bK#4&heq_LEN;R=<&cstr;R>?&__sat75;RAD&__sat74;RFG&__sat73;RHI&__sat72;RJK&__sat71;ROP&__arith;R$__x1;R+M&__wit;RQR&__varmap;RST&__ff;R!8,VU'X+Y+Y,ZWXWYZ%__x1;R+M%~R!2'R,5#14!2#1#<#:&heq_LEN;R=<&cstr;R>?&__sat75;RAD&__sat74;RFG&__sat73;RHI&__sat72;RJK&__sat71;ROP&__arith;R$__x1;R+M&__wit;RQR&__varmap;RST&__ff;R!8,VU'X+Y+Y,Z\X\YZ%__x1;R+M%~R!2'G!2'^R6#18!2'G!2'^R6#28!2#1#<#9!2'8#53#3!3+C2!2'`P!2'bA/fdata;#5'bL!2'41!2'^R6#4").
Qed.

  Lemma know_LP_rangesA : forall vals M (len cap lo70 hi70 lo38 hi38 : Z),
    vals_ev vals 70 = Z_to_bv 64 len -> vals_ev vals 38 = Z_to_bv 64 cap -> 0 <= len < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
    lo70 <= len <= hi70 -> lo38 <= cap <= hi38 ->
    know_ok ASEGS (ENVG vals) M knLPA ->
    know_ok ASEGS (ENVG vals) M (KRange (EVar 70) lo70 hi70 :: KRange (EVar 38) lo38 hi38 :: knLPA).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^>0|600;!1,20!1+11|30;!1+1!1,23}^I!2'41#6}V|10;!1,J8!1,J0!2'_49:!2+^Q!2'R,5#8!2'G#8;!2'bA/fdata;#?!3'bO'^G=#>!3,bP!1,bD5#;#:!3,bP!1,bD7#9#8!2'41#=!2'_71#1!2'A4/fdata;!1'IC!3+C+M/LEN;Dvd!2,?+MDE!1'QC!2'R,5D!1,J|50f;!2'_I9I!2'G,59!2'_49I%~RK%~R!2'R,5I!2'G,5L!2'R,59$Ha;RN$~R+_J!3'_K9I#2%Ha;RN%~R+_J!2'R,5L!2'_I9:%~RK%~R!2'R,5:!2'G,5;$Ha;RN$~R+_J!3'_K9:#2%Ha;RN%~R+_J!2'R,5;!2'_71/sp0;|40;!1,JV!2'a9UW%~R!2'R,5U%~R!2'R,5W!2'R,5!2'^SUW!1,:+S!1+0+S!1+U+M!1+W+M!2,^2+M,K!2,^2+M8!7,^W^0'X+Y+Y,Z!7,[^0'X+Y+Y,Z!4,\+M^1,^1^2,^3!7,[^0'X+Y+Y,Z!4,\+M^2,^1!2,^2+M|11;,^3!1,^4+Y!2'^8^0,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2$__x3;R+M$__x2;R+M$__x1;R+M&__wit;RZ[&__varmap;R!4,^U+M!2,T+M#3#2!2,T+M#4\&__ff;R!8,V^0'X+Y+Y,Z^3^4^3^5^6!2'R#2#3%__x3;R+M%__x2;R+M%__x1;R+M%~R!2+^Q!2'R#1#2^8!2+^Q^8!2'R#3#4!7,^W^0'X+Y+Y,Z!7,[^0'X+Y+Y,Z!4,\+M!2,^0+M,5,^1^1,^3!7,[^0'X+Y+Y,Z!4,\+M^1,^6!3,_L+M!2,^0+M91,^3$__x1;R+M&__wit;RZ[&__varmap;R!2,T+M#2\&__ff;R!8,V^0'X+Y+Y,Z^:^4^:^5^6%__x1;R+M%~R!2+^Q!2'R,5#1!2'G#1;!2+^Q!2'R,5#2!2'G#2;!2'41#<$vals;R!1+02$M;R%~R2!1+^D4$len;R+M$cap;R+M$lo70;R+M$hi70;R+M$lo38;R+M$hi38;R+M$P70;R!3+C2!2'8#856$P38;R!3+C2!2'8#976$Hl;R<$Hc;R<$H70;R!2+^Q!2'R#8#:!2'R#:#7$H38;R!2+^Q!2'R#7#:!2'R#:#6$HK;R!4'^F'^G!2'bA/fdata;#>#='bM!6,bN+^E>?!3,7+^E@'bMvd!6'_>2A$b;R2!2+^Q!2'R#<B!2'RB#;!6'_>+M#=$z;R+M!2+^Q!2'R#<#1!2'R#1#;&heq_LEN;RFE&cstr;RGH&__sat75;RJM&__sat74;ROP&__sat73;RQR&__sat72;RST&__sat71;RXY&__arith;R^7^9!4#1#B#E#C#;!2'_71A!2'_V#=&heq_LEN;RFE&cstr;RGH&__sat75;RJM&__sat74;ROP&__sat73;RQR&__sat72;RST&__sat71;RXY&__arith;R^;^<!2#1#E#=!2'8#?5#7!4'bO'^G=#>?!6,bN+^E>@'bMvd!6'_>2^=$b;R2!2+^Q!2'R#:B!2'RB#9!6'_>+M#<$z;R+M!2+^Q!2'R#:#1!2'R#1#9&heq_LEN;RFE&cstr;RGH&__sat75;RJM&__sat74;ROP&__sat73;RQR&__sat72;RST&__sat71;RXY&__arith;R^7^9!4#1#@#D#A#:!2'_71^=!2'_V#<&heq_LEN;RFE&cstr;RGH&__sat75;RJM&__sat74;ROP&__sat73;RQR&__sat72;RST&__sat71;RXY&__arith;R^;^<!2#1#D#<!2'8#?7#6!4'bO'^G=#>@#1").
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CW0 (a : Z) : Prop :=
    bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 \/ (exists lo hi, In (lo, hi) IMG_W_A /\ lo <= a < hi).
  Lemma regions_write0 : forall vals ebs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    regions_ok ASEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_W_A [] E CW0 (fun _ => True).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_K0|600;!1,20!1+11|30;!1+1!1,23!1,J|^13fff80000000;!2'_71/sp0;|10;!1,J7|50f;!1,J9!2'_48:|508;!1,J<!2'_48=!1,:!2+`I+<+M!1,:+<!2+`I+M+M!1,:A!2'_71#1!2'A4/fdata;!1'ID!3+C+M/LEN;Evd!2,?+MEF!1'QD!2'R,5E!2'_I8:!2'G,58%~RK%~R!2'R,5:!2'G,5;!2'R,58$Ha;RM$~R+_J!3'_K8:#2%Ha;RM%~R+_J!2'R,5;|40;!1,JP!2'a96Q%~R!2'R,56%~R!2'R,5Q!2'R,5!2'^S6Q!1,:+S!1+0+S!2,T+M#2!1+U+M!1+W+M!2,^2+M,K!2,^0+M8!7,^WX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M!2,^0+M5,^1Y,^3!7,[X'X+Y+Y,Z!4,\+MY,^1!3,_L+MZ!1,29,^3!1,^4+Y!2'^8X,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'8#5,9!2'_71!2'^?#3,9!2'_I8=%~RK%~R!2'R,5=!2'G,5>$Ha;RM$~R+_J!3'_K8=#2!2'R,5>%Ha;RM%~R+_J^7|47;!1,J^9!2'_I8^:!2'_48^:%~RK%~R!2'R,5^:!2'G,5^<$Ha;RM$~R+_J!3'_K8^:#2%Ha;RM%~R+_J!2'R,5^<!1,^V+M!2,bT+M!3,_L+MZ!1,2^9!3,_L+MZ!1,2<!2,^0+M,5!1'bU^<!2'_=>>!2+^Q!2'R^D^E^7!2+^Q!2'R^D#1!2'G#1,5!1'_D!2+^Q!2'R^E#2!2'G#2>!1,J|G000000;!2'_=6^I!2'H6#3!4,`J+M+M#2#1!3'aSA^L'bR!2'H6#5!2,^2+M7!3,^5+MY^O!2'H#2#3!2+^Q!2'R^E#1!2'G#1>!2'_71#3!2'_71!2'^?#5,9!1+^D+M!3+C^U!2'bY#2?!2,a>+M#1$e;R^U-^DRN$o;R!1+^D+Mw#12$~R+M+_O+_J!1,J0!2'_48^X!2'R,5#1!2'_71!2'^?#6#3!2'G#1#3!2'_71!2'8#8#3!3'aS+<#1@!2'_71!2'8#8#2|44;!2'_48!1,J_3!2+^Q^Z!2'G#1_4!2'_71!2'^?#5#2!3'aSA^L'c1!2'R#4#1|@0000;!1,J_9!1,J|F2c0000;!1'bS#2!3'aSA!4,`J+M+M#6#2'c1!2'R#:#@!2'R#C#:!2'R_:#H!2'R#K^Y!2+^Q!2'R#M#1!2'G#1#L%a;R+M%~R_B_<!2'R#2^Y$lo;R+M!2+bW+M$hi;R+M!2+^Q^M!2+^Q!2'R#2#4!2'G#4#1!2'R,5#3!3'aSA^LB%~R2!1+^D4!2'H#3!1'I#2!3+C+^:!4'c4'^G#5!2'41#4#3,^;$vals;R!1+02$ebs;R%~R+<!1+04&E;R!2,^@!1'8#2#1+`M$P0;R!3+C2!2'8#3,9/sp0;&Hsp';R/Hsp;!2+^Q!2'R56!2'R6;!E,bQ'^G,9>>??@'bRB#3'bS$~R+M+_Jvd!6'_>2/sp0;$b;R2!2+^Q!2'R5C!2'RC;&heq_LEN;RGF&cstr;RHI&__sat4;RJL&__sat3;RNO&__sat2;RRS&__arith;R$__x1;R+M&__wit;RTU&__varmap;RVW&__ff;R!8,VX'X+Y+Y,Z[\[^0^1%__x1;R+M%~R!2+^Q!2'R5#1!2'R#1;!2+^Q!2'R5#2!2'R#2;!2#16/Hsp;^2#2!2+^Q!2'R5^3!2'R^3;vd&heq_LEN;RGF&cstr;RHI&__sat8;RJL&__sat7;RNO&__sat6;R^4^5&__sat5;R^6^8&__sat4;R^;^=&__sat3;R^>^?&__sat2;RRS&__arith;R&__wit;RTU&__varmap;R^@W&__ff;R!7,^WX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M^A,^1!3,_N+M^B^B,^3!7,[X'X+Y+Y,Z!4,\+M^C,^1^B,^3^0^1^F#1^Fvd!6'_>2/sp0;$b;R2%z;R+M%~R^G%~R^H!1'bS!2'H!2'_71#4#3$z;R+M$Hz;R^G$Hnot;R^Hvd!3,bV!2+^Q!2'R^J^K!2'G^K6!2+bW+M$lo;R+M!2+bW+M$hi;R+M!2+^Q^M!2+^Q!2'R#2^N!2'G^N#1&heq_LEN;RGF&cstr;RHI&__sat8;RJL&__sat7;RNO&__sat6;R^4^5&__sat5;R^6^8&__sat4;R^;^=&__sat3;R^>^?&__sat2;RRS&__arith;R$__x2;R+M$__x1;R+M&__wit;RTU&__varmap;R!4,^U+M!2,T+M#3#2^@W&__ff;R!8,VX'X+Y+Y,Z!7,^WX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M^A,^1^O,^3!7,[X'X+Y+Y,Z!4,\+M^O,^6^C,^3\!7,^WX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M!3,_N+MY!2,^0+M^I,^1^P,^3!7,[X'X+Y+Y,Z!4,\+M^P,^6Y,^3^0^1%__x2;R+M%__x1;R+M%~R!2+^Q!2'R^D#2!2'G#2,5!2+^Q!2'R!2'_=#2^I^Q!2'G^Q#2!3#1#=6#<!1'bS^K^2#2%z;R+M%~R^G%~R^H!1'bS!2'H!2'_71!2'^?#6,9#3vd!6'_>2/sp0;$b;R2%z;R+M%~R^R!2+`@!1'bS!2'H^S#2+_J$z;R+M$Hz;R^R!3,bX!1'bS!2'H6#2+_J,`U^2#2%z;R+M%~R^R!2+`@!1'bS!2'H^T#2+_Jvd$i;R+<$nb;R+M$Hf;R^V&H;R!6'_A^U!2'bY#3?^W,`U!2,a>+M#2#1+_O!2'a0!2+^Q!2'R!2'H!2'_71!2'8#9#4#3^Y%z;R+M%~R!2+^Q^Z!2'G#1#4!1'bS!2'H!2'_71!2'8#;#6#2#1%i;R+<%nb;R+M%~R^V!2+^Q!2'R!2'H^[#2^Y%z;R+M%~R!2+^Q^Z^\!1'bS!2'H!2'_71!2'^?#8#5#2vd$v;R+<$b;R+M$Hf;R^Vvd$H;R!3+C+bZ!2'b[_0#2,b\&H0;R!6'_A^U!2'bY#4?^W,`U!2,a>+M#3#2+_O!2'a0+_O#1!2'R_0#2%v;R+<%b;R+M%~R^V!2'R^[#2vd!6'_>2/sp0;$b;R2%i;R+<%~R_1!2+^Q!2'R^S_2!2+^Q!2'R!2'H_2_4^Y%z;R+M%~R_5!1'bS!2'H!2'_71!2'8#:#4#2$i;R+<$H;R_1!2'a0!2+^Q!2'R6!2'_71!2'8#7#2!2+^Q!2'R!2'H!2'_71!2'8#7#2_4^Y%z;R+M%~R_5!1'bS!2'H!2'_71!2'8#9#4#2#1^2#2%i;R+<%~R_1!2+^Q!2'R^T_6!2+^Q!2'R!2'H_6_4^Y%z;R+M%~R_5!1'bS!2'H!2'_71!2'^?#7#4#2vd$lo;R+M$hi;R+M$Hin;R^M&e;R!4'c0/sp0;#3#2#1!2+bW+M$lo';R+M!2+bW+M$hi';R+M!2+^Q_7!2+^Q!2'R#2#5!2+^Q_8!2+^Q!2'R_:#5!2'R#4_;!5'c2+M$lo';R+M!2+bW+M$hi';R+M!2+^Q_7!2+^Q!2'R#2#6!2+^Q!2'R#5#1!2+^Q!2'R_:#6!2'R#5_;!2+^Q!2'R,5#4!2+^Q!2'R#3^Y%a;R+M%~R!2+^Q!2'R#5#1!2'G#1#4_<$x;R+M$~R!1$lo';R+M!2+bW+M$hi';R+M!2+^Q_7!2+^Q!2'R#2#7!2+^Q!2'R#6#1!2+^Q!2'R_:#7!2'R#6_;#1!2$_H;R+M$H;R!2+bW+M$hi';R+M!2+^Q_7!2+^Q!2'R#2#8!2+^Q!2'R#7#1!2+^Q!2'R_:#8!2'R#7_;!5'c2+M$hi';R+M!2+^Q!3'aSA!4,`J+M+M#3#1'c1!2+^Q!2'R#3#9!2+^Q!2'R#8#1!2+^Q!2'R_:#9!2'R#8_;!2+^Q!2'R,5#8!2+^Q!2'R#7^Y%a;R+M%~R!2+^Q!2'R#9#1!2'G#1#8_<$x;R+M$~R!1$hi';R+M!2+^Q!3'aSA!4,`J+M+M#4#1'c1!2+^Q!2'R#4#:!2+^Q!2'R#9#1!2+^Q!2'R_:#:!2'R#9_;#1!2$_H0;R+M$H;R!2+^Q!3'aSA!4,`J+M+M#5#1'c1!2+^Q!2'R#5#;!2+^Q!2'R#:#1!2+^Q!2'R_:#;!2'R#:_;!5'_6_=!2+^Q!2'R#6#<!2+^Q!2'R#;#2!2+^Q!2'R_:#<!2'R#;_;!2+^Q!2'R,5#<!2+^Q!2'R#;^Y%a;R+M%~R!2+^Q!2'R#=#1!2'G#1#<_<$~R_=$~R!2+^Q!2'R#7#=!2+^Q!2'R#<#3!2+^Q!2'R_:#=!2'R#<_;!2$_H1;R!3'aSA!4,`J+M+M#8#4'c1$H;R!2+^Q!2'R#9#?!2+^Q!2'R#>#5!2+^Q!2'R_:#?!2'R#>_;!5'_6_>!2+^Q!2'R#?#6!2+^Q!2'R_:#@!2'R#?_;!2+^Q!2'R,5#@!2+^Q!2'R#?^Y%a;R+M%~R!2+^Q!2'R#A#1!2'G#1#@_<$~R_>$~R!2+^Q!2'R#@#7!2+^Q!2'R_:#A!2'R#@_;!2$_H2;R!2'R#<#B$H;R!2+^Q!2'R#B#9!2+^Q!2'R_:#C!2'R#B_;!5'_6_?!2+^Q!2'R_:#D!2'R#C_;!2+^Q!2'R,5#D!2+^Q!2'R#C^Y%a;R+M%~R!2+^Q!2'R#E#1!2'G#1#D_<$~R_?$~R!2+^Q!2'R_:#E!2'R#D_;!2$_H3;R!2'R#E#<$H;R!2+^Q!2'R_:#G!2'R#F_;!5'_6_@!2'R#G_;!2+^Q!2'R,5#H!2+^Q!2'R#G^Y%a;R+M%~R!2+^Q!2'R#I#1!2'G#1#H_<$~R_@$~R!2'R#H_;!2$H3;R!2'R_:#J$H4;R!2'R#J_;!4,^>!2'R,5#L!2+^Q_A_C&heq_LEN;RGF&cstr;RHI&__sat7;RJL&__sat6;RNO&__sat5;RRS&__arith;R$__x1;R+M&__wit;RTU&__varmap;RVW&__ff;R!8,VX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+M!2,^0+M_:,^1Y,^3\!7,[X'X+Y+Y,Z!4,\+M^C,^1Y,^3^0^1%__x1;R+M%~R!2'R_:#1!2'R,5#2!2#1#R#8!4,^>_A_C&heq_LEN;RGF&cstr;RHI&__sat9;RJL&__sat8;RNO&__sat7;R!2'_I8^X%~RK%~R!2'R,5^X!2'G,5^Y&__sat6;R$Ha;RM$~R+_J!3'_K8^X#2%Ha;RM%~R+_J!2'R,5^Y&__sat5;RRS&__arith;R$__x1;R+M&__wit;RTU&__varmap;RVW&__ff;R!8,VX'X+Y+Y,Z!7,[X'X+Y+Y,Z!4,\+MY,^1!2,^0+M_;,^3\!7,[X'X+Y+Y,Z!4,\+MY,^1!3,_L+MZ1,^3^0^1%__x1;R+M%~R!2'R#1_;_D!2#1#S#9$a;R+M$Ha;R_Bvd!3,bX!2+^Q!2'R^J#2!2'G#26!2+bW+M_E!4,c3+M_E#N!4,c3+M$hi;R+M!2+^Q!3'aSA!4,`J+M+M#O#1'bR!2+^Q!2'R#O#3!2'G#3#1#M!4,^>!3'aSA!4,`J+M+M#N#M'bR!2+^Q!2'R#N#2!2'G#2#M#L#1_<#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1%lo;R+M%hi;R+M%~R^M!2+^Q_F!2+^Q_D%a;R+M%~R!2+^Q_8^\_<vd$lo;R+M$hi;R+M$H;R_G!2'a0!2+^Q!2'R,5#3!2+^Q!2'R#2^Y%Mx;R_H%d;R+M%m;R+<%~R!2'R#6#2%~R!2'R_I#6_J#1%lo;R+M%hi;R+M%~R_G!2+^Q_F!2+^Q_D%Mx;R_H%d;R+M%m;R+<%~R!2'R#6#2%~R!2'R_I#6_J").
Qed.
  Lemma block_frame0 : forall vals ebs A M M' (model : Model) log,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ CW0 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SP0|600;!1,20!1+11|30;!1+1!1,23!2+`I+M+M!1+^D4%~R26|10;!1,J8!2'_49!1,J|508;!1,:!2+`I+<+M!1,:+<!2'c8#8#5!1,:5$~R+M+_J!2'41#7!3'c8#A#>@!2'41#8!1#@B!1#AB!3'c8#@#=!2'41#6!1,^44!1#?@!3+C6G!3'c7!2'c8#A#>#?@!2'c8#B#?!2'41#9!1#BJ$o;R6!3+C6#1K!2'c7I#A!3'c7I#AB!2,^@!1'8#D#C$vals;R!1+02$ebs;R%~R+<!1+04$A;R!1+05$M;R7$M';R7$model;R+aQ$log;R!1+0+c5&E;R!2,^@!1'8#7#6+`M$P0;R!3+C2!2'8#8,9/sp0;$Hlog;R!3+C+^:!7'c6,9::;<'bR#3,^;$EQM;R!3+C7!2'c7=#6!3'c9#3!2'c7=#7#4$EQH;R%a;R2%~R!3+C+^:!3'c8#:#7#1,^;!3+C6!1#9#2!1#:#2$a;R+M$Ha;R!2+^Q!2'R,5#1!2'G#1!2'_49!1,J0$HC;R!1'_D!1'bS#2&RG;R!3'c:#?#>#7!<+c;'^G,9::;;<'bR>!2,^@!1'8#?#>'bS?&b;R!3'c8#>#;!2'41#4+^:&Hh;R!2,?+^:#1!3+C+^:!3'c8#?#<!2'41#5#1!1-^:RN$b;R+^:%Hh;R!3+C+^:A#1!3+C6CD#22$Hh;R!3+C+^:E,^;!2#8@#1$Hh;R!3+C+^:E,`G&E1;Rvd!6'_>+^:,`G$b;R+^:!3+C6C-^:RN$~R+^:6#12FC!2,?6GA#1HH!6'_>6!3'c7I#@BL!6'_>7!3'c9#=M#>$o;R7!3+C6!1#1JK!6'_>6NLvd!6'_>+^:,`G$b;R+^:!3+C6-^:RN$~R+^:6#12FKK!2,?6D!3'c8#B#?B#2!3+C6ND!4'c9OM#>B!C'c<'^G,9::;;<'bRO'bS?>#5M#>#8#;#7#6!2'c7I#@#:C#1#1").
Qed.
  (* [comment removed for export] *)
  Lemma block_nolog : forall (E : env) A M M' (model : Model),
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) [] ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    forall a : word, M' a = M a.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>0!1+1!1,2|600;|30;!1+1!1,21!1+^D2%~R03!2'c8#4#1!3+C3!1#9#5!1#:#5!3'c8#9#6#3%x;R03$f;R8!1#1#5!2'c8#:#7!2'c7:#8!2'c7:#9!1,^42$E;R+`M$A;R!1+0!2+`I+M+M$M;R4$M';R4$model;R+aQ$EQM;R!3+C4!2'c75#2!3'c9#5!2'c75#3!1,:+c5$EQH;R%a;R0%~R!3+C+^:!3'c8#6#3#1,^;!3+C3!1#5#2!1#6#2$a;R0&b;R!3'c8#7#4#1+^:&Hh;R!2,?+^:#1!3+C+^:!3'c8#8#5#2#1!1-^:RN$b;R+^:%Hh;R!3+C+^:!3'c8#:#7#4#16#22$Hh;R!3+C+^:7,^;!2#5#4#1$Hh;R!3+C+^:7,`G&X;R!6'c=839;<#6!3+C3!19;!19<&X;R!6'_A+^:!3'c8#;#8#5$b;R+^:!3+C3-^:RN$~R+^:3#12=!1#:#6-^:RN$~R+^:3#12=!1#;#6#1,`G#26#1#1").
Qed.
  (* [comment removed for export] *)
  Lemma content_block0 : forall vals ebs A M M' (model : Model) log (u n : Z) (m : nat) bs,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_W_A log = true ->
    mrestrict (ahid A model) M' = mem_denot E (mrestrict (ahid A model) M) log ->
    (forall a, ahid A model a = true -> M' a = M a) ->
    hzA sp0 u n -> Z.of_nat m <= n ->
    rdn ASEGS M (Z_to_bv 64 u) m = Some bs -> rdn ASEGS M' (Z_to_bv 64 u) m = Some bs.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "Sa10|600;!1,20!1+11|30;!1+1!1,23!1+04!2+`I+M+M!1+^D4%~R27|10;!1,J9!1,J|508;!2'_4:;!2'c8#<#9|<000;!1,J>!2'R?#:!2'H#:#9|@0000;!1,JB!1,J|F2c0000;!2'_71/sp0;!1,J|G000000;!2'_=EF!1+^D5!2'H#=#<!2'H#>#=!2+`@!2'RJC!2'RD#>!1'I#@!1,J|^13fff80000000;!2'RME|50f;!1,JO!2'_4:P!2'REQ!2'41#E!1'I#3!2'41!2'H#1T!2'H#G!1'I#2!2'A4/fdata;!1'IW!3+C+M/LEN;Xvd!2,?+MXY!1'I#F!2'GT[!4'F!2'B#3#F\!<'L+<+M'B'I'G'N#3T!2,?+MT#F[!2,?+M[#2!1'Q#4!1'I#4!2'R,5^2!1'Q#H!2'R,5!1'I#H!1'QW!2'R,5X!2'_I:P!2'G,5:%~R^9%~R!2'R,5P!2'G,5Q!2'R,5:$Ha;R^;$~R+_J!3'_K:P#2%Ha;R^;%~R+_J!2'R,5Q!2'_I:;%~R^9%~R!2'R,5;!2'G,5<$Ha;R^;$~R+_J!3'_K:;#2%Ha;R^;%~R+_J!2'R,5<!1,J0!2'_I:^B!2'_4:^B%~R^9%~R!2'R,5^B!2'G,5^D$Ha;R^;$~R+_J!3'_K:^B#2%Ha;R^;%~R+_J!2'R,5^D|40;!1,J^H!2'a9E^I%~R!2'R,5E%~R!2'R,5^I!2'R,5!2'^SE^I!2,_0+M}8}2!2,_0+M^M!2,_0+M,9}7!2,_0+M^P}6!2,_0+M^R}5!2,_0+M^T}4!2,_0+M^V!2,^X!3,^Y+M^Q!3,^Y+M^S!3,^Y+M^U!3,^Y+M^W^O,_1}3!2,_0+M^Y!3,^Y+M^Z^O!1,:+S!1+0+S!1,^V+M!2,T+M#6!4,^U+M_1#6_2!2,T+M#5!4,^U+M_4#6_1!1+U+M!1+W+M!2,^0+M,5!2,^2+M9!1,^4+Y!2,^2+M|34;!6,^7_7'X+Y+Y,Z#8|11;!2,^2+M_=!2,^0+M:!3,_L+M_?!1,2O|33;!2,^2+M_A!2,^2+M,K!3,^5+M_C_B!2,^0+MF!2,^0+MC!2,^0+MD!7,[_7'X+Y+Y,Z!4,\+M!2,^0+M?,^1_C,^3!2,^0+MM!6,^7_7'X+Y+Y,Z#9!3,^5+M_C_9!3,_L+M_?1!2'^8_7,Z!4'^9#1#3vv!2,?+^:,^;!3+C+^:!2'^<#1#3,^;!3'^=+M,5#2!2'H#9#:!1'I#R!1'I#?!1'bSV!2'H#HT!2+^Q!2'RG_S!2'G_SE!4,`J+M+M#2#1!3'aS6_U'bR!2'H#J!1'I#5!2+bW+M$lo;R+M!2+bW+M$hi;R+M!2+^Q_V!2+^Q!2'R#2_W!2'G_W#1!2'H#I^2!1'I#6!1'I#I!2'G_Z_[!1'I#7}1!2,_0+M`1!3,^Y+M^U!3,^Y+M^W!3,^Y+M^N`2!2,T+M#4!4,^U+M`4#6_1!2,T+M#3!3,_N+M_C_E!2,^2+M|31;!7,[_7'X+Y+Y,Z!4,\+M_I,^1_C,^3!7,^W_7'X+Y+Y,Z`9_J|32;!2,^2+M`;!7,[_7'X+Y+Y,Z!4,\+M_B,^1`<,^3!3,^5+M`8`<!6,^7_7'X+Y+Y,Z#:!2'R#7#6!2'H#UL!2'H#K_Z!2'H#L`0!2'H#N!1'I#9!4,`J+M+M#3#1!2'H#O!1'I#:!4,`J+M+M#5#1!2'H#Q!1'I#<!4,`J+M+M#6#2!3'aS6`I'bR!2'H#R!1'I#=!4,`J+M+M#8#4!3'aS6_U'c1!2'R#9D!3'aS6`I'c1!2'R#:#G!2'R#G#:!2'RC#O!1'I#[!1'I#^A!2'G`S`T|35;!2,^2+M`V!7,[_7'X+Y+Y,Z!4,\+M_8,^1`W,^3!7,[_7'X+Y+Y,Z!4,\+M`W,^6_B,^3!2,^2+M|36;!3,^5+M`8`W!2'H#6#:!2'RM#8$vals;R!1+02$ebs;R%~R+<5$A;R!1+06$M;R8$M';R8$model;R+aQ$log;R!1+0+c5$u;R+M$n;R+M$m;R+<$bs;R5&E;R!2,^@!1'8#;#:+`M$P0;R!3+C2!2'8#<,9/sp0;$Hlog;R!3+C+^:!7'c6,9<<!1,:!2+`I+<+M!1,:+<'bR#7,^;$EQM;R!3+C8!2'c7=#:!3'c9#3!2'c7=#;#8$EQH;R%a;R2%~R!3+C+^:!3'c8#>#;#1,^;!3+C7!1#=#2!1#>#2$H;R!3'b>/sp0;#9#8!5'_6@!2+^Q!2+`@!2'RAC!2'RD#:!2'RAG%~R!2'R!1'I#8#9%~R!3+CH!4'c>'^G#?!2'41#;#9!2,a>5#8!3+CH!4'c>'^G#?!2'41#<#:!2,a>5#9$~R@$~R!2+^Q!2+`@!2'R!2'H#;#:C!2'RD#;!2'R!2'H#;#:G!2$Z1;R!2'R?#<$H;R!2+^Q!2+`@!2'RIC!2'RD#=!2'RIG!5'_6K!2'RJG%~R!2'R!1'I#<#=%~R!3+CH!4'c>'^G#C!2'41#?#=!2,a>5#<!3+CH!4'c>'^G#C!2'41#@#>!2,a>5#=$~RK$~R!2'R!2'H#?#>G!2$Z2;R!2+`@!2'R!2'H#@#?C!2'RD#@$Z3;R!2'R!2'H#A#@G$Hm;R!2'RL#A$HC;R!3+CH!4'c>'^G#G!2'41#C#A!2,a>5#@&Hsp';R/Hsp;!2+^QNR!6'_AH!4'c>'^G#IS#C$o;RH!3+CH!4'c>'^G#I!2'41#F#D#1!6'c?'^G#H#I#CS$j;R+<$Hj;R!2'B#1#D!6'_>+M#G$z;R+M!3+C7!1#KU!1#LU!>'c@#N#M#L#K#J#I#H#B#A#@#?V&heq_LEN;RZY&Hj0;R^0\&cstr;R^1^3&cstr0;R^4^5&cstr1;R^6^7&__sat10;R^8^:&__sat9;R^<^=&__sat8;R^>^?&__sat7;R^@^A&__sat6;R^C^E&__sat5;R^F^G&__sat4;R^J^K&__arith;R$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M^L!3,^Y+M^N^O,_1!3,7+S^X!3,7+S^X!3,7+S!2,^X!3,^Y+M^L^[,_1^\_0&__varmap;R!4,^U+M!4,^U+M_3#3_1#2!4,^U+M_1#4_5_6&__ff;R!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_8,^1_9,^3_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_9,^6_;,^3_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z_<!7,[_7'X+Y+Y,Z!4,\+M_>,^1_@,^3_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_;,^1_B,^3_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_D,^1!3,_N+M_>_E,^3_:!8,V_7'X+Y+Y,Z!7,`B_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_D,^1_F,^3!7,[_7'X+Y+Y,Z!4,\+M_G,^1_C,^3_:!8,V_7'X+Y+Y,Z_H_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_I,^1_>,^3_J_:!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_8,^1_K,^3!7,[_7'X+Y+Y,Z!4,\+M_K,^6_L,^3_M_N%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R,5#2%~R!2'G#3#6%~R!2+^Q#8!2'R#5Q%~R!2'R#8#7%~R!2'R!2'H#5#8!2'_=#7F%~R!2+`@!2'R!2'H#6#9C!2'RD#6%~R!2'R?#7%~R!2+^Q!2'RM#:#>!2+^Q!2'R,5_O!2'G_O^D!?#1RN_P#SE_Q#T#;#<#@#B#C#D#H/Hsp;vd$H;R_R!6'cA_T_X+_O$~R_T!1$HS;R!2+^Q!2'RG_Y!2'G_YE&heq_LEN;RZY&Hj0;R!4'F!2'B#6#I_\!<'L+<+M'B'I'G'N#6_Z!2,?+M_Z#I_[!2,?+M_[#5_\&cstr;R!1'Q#7!2'R,5`0&cstr0;R!1'Q#K!2'R,5!1'I#K&cstr1;R^6^7&__sat8;R^8^:&__sat7;R^<^=&__sat6;R^>^?&__sat5;R^@^A&__sat4;R^J^K&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X`3,_1^\_0&__varmap;R!4,^U+M!4,^U+M_3#6`5#2!4,^U+M!4,^U+M`6#6_1#6_5_6&__ff;R!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_;,^6_B,^3_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M`7,^1!3,^5+M`8_;,^3_<_:!8,V_7'X+Y+Y,Z`:_:!8,V_7'X+Y+Y,Z`=_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M`>,^1`7,^3_:!8,V_7'X+Y+Y,Z`:_:`?_M_N%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'G#5#4%~R!2+^Q!2'R!2'_=#2F!2'H#3#6#7%~R!2+^Q!2'RM#3#9%~R`@%~R!2'R!2'H#6#7!2'_=#5F%~R!2+^Q!2'RM#6#<#>!>#1+_OR!2'G`AEL!1'I#S#T#UE#:#<#A#C#D/Hsp;#1$~R_X!1$H;R!2+bW+M$lo;R+M!2+bW+M$hi;R+M!2+^Q_V!2+^Q!2'R#2`B!2'G`B#1!5'c2+M$lo;R+M!2+bW+M$hi;R+M!2+^Q_V!2+^Q!2'R#2`C!2'G`C#1+_O$x;R+M$~R!1$lo;R+M!2+bW+M$hi;R+M!2+^Q_V!2+^Q!2'R#2!2'H#M!1'I#8!2'G!2'H#M!1'I#8#1#1!2$lo;R+M$H;R!2+bW+M$hi;R+M!2+^Q_V!2+^Q!2'R#2`D!2'G`D#1!5'c2+M$hi;R+M!2+^Q!3'aS6`E'bR!2+^Q!2'R#3`F!2'G`F#1+_O$x;R+M$~R!1$hi;R+M!2+^Q!3'aS6!4,`J+M+M#4#1'bR!2+^Q!2'R#4!2'H#P!1'I#;!2'G!2'H#P!1'I#;#1#1!2$hi;R+M$H;R!2+^Q!3'aS6`G'bR!2+^Q!2'R#5`H!2'G`H#1!5'_6`J!2+^Q!2'R#6`K!2'G`K#2+_O$~R`J$~R!2+^Q!2'R#7!2'H#S!1'I#>!2'G!2'H#S!1'I#>#3!2$Hin;R!3'aS6`L'bR$Hr;R!2+^Q!2'R#9`A!2'G`A#5&e;R!4'c0/sp0;#:#6#2!2+bW+M$lo';R+M!2+bW+M$hi';R+M!2+^Q`M!2+^Q!2'R#2#<!2+^Q!2'R#8#1!2+^Q!2'RC#<!2'R#8D!5'c2+M$lo';R+M!2+bW+M$hi';R+M!2+^Q`M!2+^Q!2'R#2#=!2+^Q!2'R#9#1!2+^Q!2'RC#=`N+_O$x;R+M$~R!1$lo';R+M!2+bW+M$hi';R+M!2+^Q`M!2+^Q!2'R#2#>!2+^Q!2'R#:#1!2+^Q!2'RC#>!2'R#:D#1!2$_H;R+M$H;R!2+bW+M$hi';R+M!2+^Q`M!2+^Q!2'R#2#?!2+^Q!2'R#;#1!2+^Q!2'RC#?!2'R#;D!5'c2+M$hi';R+M!2+^Q!3'aS6`E'c1!2+^Q!2'R#3#@!2+^Q!2'R#<#1!2+^Q!2'RC#@!2'R#<D+_O$x;R+M$~R!1$hi';R+M!2+^Q!3'aS6!4,`J+M+M#4#1'c1!2+^Q!2'R#4#A!2+^Q!2'R#=#1!2+^Q!2'RC#A!2'R#=D#1!2$_H0;R+M$H;R!2+^Q!3'aS6`G'c1!2+^Q!2'R#5#B!2+^Q!2'R#>#1!2+^Q!2'RC#B!2'R#>D!5'_6`O!2+^Q!2'R#6#C!2+^Q!2'R#?#2!2+^Q!2'RC#C!2'R#?D+_O$~R`O$~R!2+^Q!2'R#7#D!2+^Q!2'R#@#3!2+^Q!2'RC#D!2'R#@D!2$_H1;R!3'aS6`L'c1$H;R!2+^Q!2'R#9#F!2+^Q!2'R#B#5!2+^Q!2'RC#F!2'R#BD!5'_6`P!2+^Q!2'R#C#6!2+^Q!2'RC#G!2'R#CD+_O$~R`P$~R!2+^Q!2'R#D#7!2+^Q!2'RC#H!2'R#DD!2$_H2;R!2'R#<#I$H;R!2+^Q!2'R#F#9!2+^Q!2'RC#J!2'R#FD!5'_6`Q!2+^Q!2'RC#K!2'R#GD+_O$~R`Q$~R!2+^Q!2'RC#L!2'R#HD!2$_H3;R!2'R#I#<$H;R!2+^Q!2'RC#N!2'R#JD!5'_6`R!2'R#KD+_O$~R`R$~R!2'R#LD!2$H3;R!2'RC#Q$H4;R!2'R#ND&heq_LEN;RZY&Hj0;R!4'F!2'B#[#^A`U!<'L+<+M'B'I'G'N#[`S!2,?+M`S#^A`T!2,?+M`T#Z`U&cstr;R!1'Q#\!2'R,5!1'I#\&cstr0;R!1'Q#^C!2'R,5!1'I#^C&cstr1;R^6^7&__sat9;R^8^:&__sat8;R^<^=&__sat7;R^>^?&__sat6;R^@^A&__sat5;R^J^K&__arith;R$__p2;Rw$__p1;Rw$__x7;R+M$__x6;R+M$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M^L!3,^Y+M^S!3,^Y+M^Z`2,_1!3,7+S!2,^X!3,^Y+M^Q`3,_1^\_0&__varmap;R!4,^U+M!4,^U+M!4,^U+M_1#8_2#8!4,^U+M`4#8!2,T+M#8#2!4,^U+M!4,^U+M`6#8!2,T+M#7#8!4,^U+M_4#8_1_6&__ff;R!8,V_7'X+Y+Y,Z`X_:!8,V_7'X+Y+Y,Z`Y_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M`Z,^1_G,^3_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_F,^1_;,^3_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_;,^1`[,^3!7,[_7'X+Y+Y,Z!4,\+M`[,^6`Z,^3_:!8,V_7'X+Y+Y,Z`=_:!8,V_7'X+Y+Y,Z!7,`B_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M`>,^1_F,^3!7,[_7'X+Y+Y,Z!4,\+M_G,^1`8,^3_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z`9`?_:!6,^7_7'X+Y+Y,Z#;_M_N%__p2;Rw%__p1;Rw%__x7;R+M%__x6;R+M%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R,5#6%~R!2'G#7#5%~R`N%~R!2'RC#8%~R!2+^Q!2'R#9`\!2'G`\#;%~R!2'R#9#8%~R!2+`@!2'R!2'H#8#9C!2'RD#8%~R!2+^Qa0#?#A!A#1+_OR#Z!1'I#^8#^1!1'I#^K#^L#^ME#9#:#<#=#U#^;#^=/Hsp;#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#1#1!1'_D_R!2'_71!2'41#G!2'_V#G&heq_LEN;RZY&Hj0;R^0\&cstr;R^1^3&cstr0;R^4^5&cstr1;R^6^7&__sat10;R^8^:&__sat9;R^<^=&__sat8;R^>^?&__sat7;R^@^A&__sat6;R^C^E&__sat5;R^F^G&__sat4;R^J^K&__arith;R$__p2;Rw$__p1;Rw$__x5;R+M$__x4;R+M$__x3;R+M$__x2;R+M$__x1;R+M&__wit;R!3,7+S!2,^X!3,^Y+M^Q!3,^Y+M^S!3,^Y+M^U!3,^Y+M^W^[,_1^\_0&__varmap;R!4,^U+M!4,^U+M_1#3`5#2!4,^U+M_3#6_5_6&__ff;R!8,V_7'X+Y+Y,Z`X_:!8,V_7'X+Y+Y,Z`Y_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z_<!7,[_7'X+Y+Y,Z!4,\+M_9,^1_@,^3_:!8,V_7'X+Y+Y,Z`=_:!8,V_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M!3,^5+M_C`<,^1!3,_N+M_9_E,^3_:!8,V_7'X+Y+Y,Z_H_:!8,V_7'X+Y+Y,Z!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_I,^1_9,^3_J_:!7,^W_7'X+Y+Y,Z!7,[_7'X+Y+Y,Z!4,\+M_8,^1_C,^3!7,[_7'X+Y+Y,Z!4,\+M_C,^6_L,^3_M_N%__p2;Rw%__p1;Rw%__x5;R+M%__x4;R+M%__x3;R+M%__x2;R+M%__x1;R+M%~R!2'R,5#5%~R!2'G#6#5%~R!2+^Q#8!2'R#4Q%~R`@%~R!2'R!2'H#5#7!2'_=#6F%~R!2'R?#6%~R!2+^Qa0#=!2+^Q!2'R,5#8!2'G#8^D!>#1RN_Q_P#SE#T#;#<#@#B#C#H/Hsp;!2,a>5#B#2#2#1#1#2#1#1").
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma read_okA : forall z, lp_atA (z - 1) -> rd_atA z.
  Proof.
    intros z IH. unfold rd_atA.
    intros k len want A1 vals R M model A cr Hk Hlen HlL Hz Hwant HL HV P38 P48 P70 P71 HR HK HC DI HINC (MF & MS) Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    assert (Hw : 1 <= want <= 65536 /\ want <= CAPk k - len) by lia.

    eapply (aread_site scfg L ar C IL HI HIok ICok ILY sp0 Hsp DL Hcells M0 vals _ srRDA knLPA R M model [(A1, CAPk k)] LK0 cr A want path (Z_to_bv 64 len) fdata
              MSO [(48%nat, 65536)] [] 0xb0198 K);
      [ exact HR | exact HK
      | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
      | exact P0 | vm_compute; reflexivity
      | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
      | unfold MSO; lia | reflexivity
      | regv HR (10%bv : reg); reflexivity
      | regv HR (11%bv : reg); reflexivity
      | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact P71
      | lia
      | regv HR (1%bv : reg); reflexivity
      | lia | reflexivity
      | exact DI
      | rewrite MF; apply fds_lookup3A
      | rewrite MS; exact Hfile
      | intros i nb Hf; cbn in Hf;
        destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                         rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
      | intros v b Hf; discriminate
      | ].
    intros R' M' model' bs vals' E' HL' HA' HR' HK' DI' HFD' HFS' HSRC HFRM. subst vals' E'.
    rewrite HL in HL', HA', HR'. change (72 + 10)%nat with 82%nat in HA'.
    change (sr_after_call_j srRDA (map ridx c_kept) 72) with srRA0 in HR'.
    change (keep_readA MSO [(48%nat, 65536)] [] knLPA) with knRA in HK'.
    assert (Ebs : bs = firstn (Z.to_nat want) (skipn (Z.to_nat len) fdata)) by (subst bs; apply file_read_litA; lia).
    assert (Hnb : Z.of_nat (length bs) = Z.min want (LEN - len)) by (rewrite Ebs; unfold LEN; apply length_readA; lia).
    clearbody bs. set (nb := Z.of_nat (length bs)) in *.
    rewrite len_word_Z in HA', HFD'. fold nb in HA', HFD'.
    assert (MF' : m_fds model' = fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 (len + nb)))).
    { rewrite HFD', MF, fds_ins3A. f_equal. f_equal. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
    assert (MS' : m_fs model' = fs0) by (rewrite HFS'; exact MS).
    assert (HC1 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
    { rewrite <- HC. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HFRM; unfold MSO, STAGE; lia. }
    set (vals2 := vals ++ junk_vals R') in *.
    change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
    assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
    assert (X38 : vals_ev vals2 38 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P38).
    assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
    assert (X70 : vals_ev vals2 70 = Z_to_bv 64 len) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P70).
    clear HR HK DI HC MF MS HFD' HFS' HFRM HDEF. clear M model.
    destruct (Z.eq_dec nb 0) as [Hz0 | Hnz].
    -
      assert (HlenL : len = LEN) by lia.
      assert (HKf : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRf0A).
      { constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
      clear HK'.
      drv_block0 HIok Hsp DL HR' HKf DI' X0 scr0 104%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
      assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (length fdata) = Some fdata).
      { lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
          apply (content_block0 vals2 _ A M' M model' lg A1 (CAPk k) (length fdata) fdata X0 ltac:(vm_compute; reflexivity) EQM EQH HZ) end; [unfold LEN in *; lia|].
        rewrite HlenL in HC1. unfold LEN in HC1. rewrite Nat2Z.id, firstn_all in HC1. exact HC1. }
      clear EQM EQH SBM HR' HKf DI' HC1 MF' MS' HSRC. clear M' model'.

      eapply (rz_close_lz ASEGS scfg _ _ M model ECALLW (Z_to_bv 64 3)); try apply is_ecall_ECALLW.
      + vm_compute. reflexivity.
      + exact (di_halt _ _ _ _ _ _ _ _ _ _ DI).
      + regv HR (17%bv : reg). reflexivity.
      + regv HR (10%bv : reg). reflexivity.
      + rewrite u_small by lia. lia.
      + rewrite F1. apply fds_lookup3A.
      + rewrite v_addi_pc4 by lia. change (0x153a78 + 4) with 0x153a7c.
        rewrite F1, fds_remove3A.
        set (model2 := with_fds fds0 model).
        assert (DI2 : dinvA [(A1, CAPk k)] LK0 cr A M model2).
        { apply (dinv_model scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ model model2 DI); [apply with_fds_vm| |apply with_fds_rdr].
          unfold model2. rewrite with_fds_halted'. exact (di_halt _ _ _ _ _ _ _ _ _ _ DI). }
        assert (HK2 : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model2) M) (cellCA :: knRf0A)) by exact HK.
        assert (G1 : m_fds model2 = fds0) by (unfold model2; apply with_fds_fds).
        assert (G2 : m_fs model2 = fs0) by (unfold model2; rewrite with_fds_fs; exact F2).
        pose proof (regs_set_a0 (ENVG vals2) _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR3.
        clearbody model2. clear HR HK DI F1 F2. clear model.
        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          set (valsG := relayV vals2 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
          pose proof (credA_exit k cr Hk Hcr) as [HX1 HX2];
          pose proof (HKC ltac:(lia) (CAPk k) cr ltac:(lia) ltac:(lia) HX1 HX2) as CL;
          unfold close_kgA in CL;
          apply (CL valsG Rc M model2 A A1)
        end.
        * reflexivity.
        * unfold valsG. apply hdr_relayA. exact XV.
        * unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
        * unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70. f_equal. lia.
        * unfold valsG, ENVA. relay_regs HR3.
        * intros lo hi Hlh. unfold knGA. constructor.
          -- cbn [kentry_ok edenot ev ENVA]. unfold valsG. rewrite relayV_70. unfold gr. regv1 HR3. rewrite X70, u_small by lia. lia.
          -- eapply ksubl_sound; [| exact knGbaseA_sub]. apply Forall_app. split.
             ++ apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsG _ [(A1, CAPk k)] LK0 cr A M model2 48%nat A1 (CAPk k) 65536 DI2);
                  [left; reflexivity | lia | | unfold valsG; rewrite relayV_lo by lia; exact X0].
                unfold valsG. rewrite relayV_48. unfold gr. regv1 HR3. exact X48.
             ++ unfold valsG, ENVA. eapply relay_know6; [exact HK2 | vm_compute; reflexivity | vm_compute; reflexivity].
        * exact HC2.
        * exact DI2.
        * exact HINC.
        * exact G1.
        * exact G2.
    -
      assert (HKe : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A model') M') knRe0A).
      { constructor; [|exact HK']. cbn [kentry_ok edenot ev ENVA]. rewrite HA', u_small by lia. lia. }
      clear HK'.
      drv_block0 HIok Hsp DL HR' HKe DI' X0 scr0 104%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF' in F1. rewrite MS' in F2.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (HC2 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
      { rewrite <- HC1. apply rdn_agree. intros j Hj. apply EQA. }
      assert (HSRC2 : rdn ASEGS M (Z_to_bv 64 STAGE) (Z.to_nat nb) = Some bs).
      { unfold nb. rewrite Nat2Z.id. rewrite <- HSRC. apply rdn_agree. intros j Hj. apply EQA. }
      clear EQM EQH EQA SBM HR' HKe DI' HC1 MF' MS' HSRC. clear M' model'.

      lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
      eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R0 M model [(A1, CAPk k)] LK0 cr A A1 (CAPk k) (A1 + len) STAGE nb bs
                MSO [] [] 0xb0130 K) end end;
        [ exact HR | exact HK
        | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
        | exact X0 | vm_compute; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
        | unfold MSO; lia | reflexivity
        | regv HR (10%bv : reg); cbn [edenot ev ENVA]; rewrite X48, X70, alu_add_Z; reflexivity
        | regv HR (11%bv : reg); reflexivity
        | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact HA'
        | lia
        | regv HR (4%bv : reg); reflexivity
        | regv HR (1%bv : reg); reflexivity
        | lia | reflexivity
        | exact DI
        | left; reflexivity | lia | lia
        | apply (src_stage_aacc scfg L ar IL HI sp0 Hsp DL ICok ILY _ _ _ _ _ _ _ STAGE nb (di_inv _ _ _ _ _ _ _ _ _ _ DI)); unfold STAGE; lia
        | unfold STAGE; lia | unfold STAGE; lia
        | apply (src_stage_app_rng L ar IL sp0 Hsp DL); unfold STAGE; lia
        | intros i Hi; left; unfold STAGE; lia
        | exact HSRC2
        | unfold STAGE; lia
        | intros i nb0 Hf; discriminate
        | intros v b Hf; discriminate
        | exact HK0
        | ].
      intros R2 M2 model2 vals' E' HL2 HR2 HK2 DI2 HRT2 HDST HBLK HIMG. subst vals' E'.
      rewrite HL' in HL2, HR2. change (72 + 32 + 32)%nat with 136%nat in HL2.
      change (sr_after_call_j _ (map ridx c_kept) (72 + 32)) with srRm0 in HR2.
      change (keep_allocA MSO 4096 [] [] _) with knRm0 in HK2.
      destruct (model_rt_fds _ _ HRT2) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
      assert (HC3 : rdn ASEGS M2 (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
      { replace (Z.to_nat (len + nb)) with (Z.to_nat len + length bs)%nat by lia.
        rewrite <- firstn_app_skipnA.
        replace (firstn (length bs) (skipn (Z.to_nat len) fdata)) with bs by (rewrite Ebs at 1; rewrite Ebs at 1; symmetry; apply firstn_len_firstnA).
        apply rdn_app_Z; [ | | lia | lia].
        - rewrite <- HC2. apply rdn_agree. intros j Hj. rewrite u_small by lia.
          apply HBLK; [lia | exists (A1, CAPk k); split; [left; reflexivity | cbn [fst snd]; lia] | lia].
        - rewrite Z2Nat.id by lia. unfold nb in HDST. rewrite Nat2Z.id in HDST. exact HDST. }
      set (vals3 := vals2 ++ junk_vals R2) in *.
      change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR2, HK2.
      assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
      assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
      assert (Y38 : vals_ev vals3 38 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X38).
      assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
      assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 len) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
      assert (Y82 : vals_ev vals3 82 = Z_to_bv 64 nb) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA').
      clear HR HK DI HC2 HSRC2 HDST HBLK HIMG F1 F2 HRT2. clear M model R0.

      drv_block0 HIok Hsp DL HR2 HK2 DI2 Y0 scr0 136%nat.
      destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
      pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
      assert (HC4 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (len + nb)) = Some (firstn (Z.to_nat (len + nb)) fdata)).
      { rewrite <- HC3. apply rdn_agree. intros j Hj. apply EQA. }
      lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        set (valsL := relayV vals3 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) []);
        apply (IH k (len + nb) A1 valsL Rc M model A cr)
      end.
      + lia.
      + lia.
      + lia.
      + lia.
      + reflexivity.
      + unfold valsL. apply hdr_relayA. exact YV.
      + unfold valsL. rewrite relayV_38. unfold gr. regv1 HR. exact Y38.
      + unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
      + unfold valsL. rewrite relayV_70. unfold gr. regv1 HR. rewrite Y70, Y82, alu_add_Z. reflexivity.
      + unfold valsL, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
      + rewrite knLPA_split. apply Forall_app. split.
        * apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsL _ [(A1, CAPk k)] LK0 cr A M model 48%nat A1 (CAPk k) 65536 DI);
            [left; reflexivity | lia | | unfold valsL; rewrite relayV_lo by lia; exact Y0].
          unfold valsL. rewrite relayV_48. unfold gr. regv1 HR. exact Y48.
        * unfold valsL, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
      + exact HC4.
      + exact DI.
      + exact HINC.
      + split; [exact F1 | exact F2].
      + exact Hcr.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_stepA : forall z, rd_atA z -> lp_atA z.
  Proof.
    intros z HRD. unfold lp_atA.
    intros k len A1 vals R M model A cr Hk Hlen HlL Hz HL HV P38 P48 P70 HR HK HC DI HINC HMD Hcr.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (CAPk_range k Hk) as HCk.
    destruct (inv_block1 _ _ _ _ _ _ _ _ DI (or_introl eq_refl)) as (HBR & HDEF & HZ). pose proof HZ as (Z1 & Z2 & Z3).
    pose proof HV as (P0 & P1 & P2 & P3).
    destruct HCOST as (Hkpm & Hlin & Hovh).
    destruct (Z_lt_le_dec len (CAPk k)) as [Hlt | Hge].
    -
      pose proof (know_LP_rangesA vals _ len (CAPk k) 0 67108863 65536 67108864 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
      change (KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLPA) with knLPpA in HK1.
      clear HK. rename HK1 into HK.
      assert (TAIL : forall want R1 M1 (model1 : Model) (sc12 : expr),
                 want = Z.min (CAPk k - len) 65536 ->
                 regs_ok (ENVG vals) (sr_upd srPa (ridx 12) sc12) R1 -> edenot (ENVG vals) sc12 = Z_to_bv 64 want ->
                 know_ok ASEGS (ENVG vals) (mrestrict (ahid A model1) M1) knLPpA ->
                 (forall a : word, M1 a = M a) -> dinvA [(A1, CAPk k)] LK0 cr A M1 model1 -> mdl3 model1 len ->
                 srealizes ASEGS scfg (mkCfg (mkst R1 (Z_to_bv 64 0x6b93c) M1 (seg_rom ASEGS)) model1) K).
      { intros want R1 M1 model1 sc12 Hwant HR1 H12 HK1 EQA DI1 HMD1.
        assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
        { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
        set (valsR := relayV vals R1 (gr R1 21) (gr R1 9) (gr R1 19) [gr R1 12]).
        apply (HRD k len want A1 valsR R1 M1 model1 A cr); [lia | lia | lia | lia | exact Hwant | reflexivity | | | | | | | | exact HC1 | exact DI1 | exact HINC | exact HMD1 | exact Hcr].
        + unfold valsR. apply hdr_relayA. exact HV.
        + unfold valsR. rewrite relayV_38. unfold gr. regv1 HR1. exact P38.
        + unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
        + unfold valsR. rewrite relayV_70. unfold gr. regv1 HR1. exact P70.
        + unfold valsR. rewrite relayV_71. unfold gr. regv1 HR1. exact H12.
        + unfold valsR, ENVA. relay_regs HR1; try (relay2 HR1; reflexivity).
        + rewrite knLPA_split. apply Forall_app. split.
          * apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, CAPk k)] LK0 cr A M1 model1 48%nat A1 (CAPk k) 65536 DI1);
              [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
            unfold valsR. rewrite relayV_48. unfold gr. regv1 HR1. exact P48.
          * unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity]. }
      destruct (Z_lt_le_dec (CAPk k - len) 65536) as [Hsmall | Hbig].
      +
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; true] [] []) 71%nat.
        { apply (sc_ltu_wantA vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.ltb_lt; lia]. }
        { apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL (CAPk k - len) R0 M1 model0 want_xA); [lia | exact HR0 | apply (want_x_valA vals len (CAPk k) P70 P38); lia | exact HK1
                                                         | exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
      +
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [false; false] [] []) 71%nat.
        { apply (sc_ltu_wantA vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.ltb_ge; lia]. }
        { apply (sc_eq_70_38A vals _ len (CAPk k) false P70 P38); [lia | lia | apply Z.eqb_neq; lia]. }
        apply (TAIL 65536 R0 M1 model0 (ELit 65536)); [lia | exact HR0 | reflexivity | exact HK1
                                                         | exact (block_nolog _ _ _ _ _ EQM EQH) | exact DI0 |].
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). split; [rewrite F1; exact MF | rewrite F2; exact MS].
    -
      assert (Heq : len = CAPk k) by lia.
      destruct (Z.eq_dec k 10) as [Hk10 | Hk10].
      +
        assert (HC10 : CAPk k = 67108864) by (rewrite Hk10; reflexivity).
        assert (Hl10 : len = 67108864) by lia.
        rewrite Hl10 in P70, HMD. rewrite HC10 in P38, DI.
        apply (HREF ltac:(lia) A1 vals R M model A cr); assumption.
      +
        pose proof (CAPk_lt10 k ltac:(lia)) as HC25.
        pose proof (know_LP_rangesA vals _ len (CAPk k) 65536 33554432 65536 33554432 P70 P38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK) as HK1.
        change (KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLPA) with knLPgA in HK1.
        clear HK. rename HK1 into HK.
        drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 71%nat.
        { apply (sc_eq_70_38A vals _ len (CAPk k) true P70 P38); [lia | lia | apply Z.eqb_eq; lia]. }
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). destruct HMD as (MF & MS). rewrite MF in F1. rewrite MS in F2.
        assert (HC1 : rdn ASEGS M1 (Z_to_bv 64 A1) (Z.to_nat len) = Some (firstn (Z.to_nat len) fdata)).
        { rewrite <- HC. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR HK DI HC MF MS HDEF. clear M model R.

        lazymatch type of HR0 with regs_ok _ ?sr _ => lazymatch type of HK1 with know_ok _ _ _ ?kn =>
        eapply (amalloc_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals _ sr kn R0 M1 model0 [(A1, CAPk k)] LK0 cr A (2 * CAPk k) MSO
                  [(48%nat, 65536)] [] 0xb0158 K) end end;
          [ exact HR0 | exact HK1
          | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
          | exact P0 | vm_compute; reflexivity
          | regv HR0 (2%bv : reg); cbn [edenot ev ENVA]; rewrite P0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | regv HR0 (10%bv : reg); rewrite Heq in P70; apply (cap2_x_valA vals (CAPk k) P70); lia
          | lia
          | destruct Hcr as [Hc1 Hc2]; unfold acredit_ok; split; nia
          | regv HR0 (4%bv : reg); reflexivity
          | regv HR0 (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI0
          | intros i nb Hf; cbn in Hf;
            destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                             rewrite P48, u_small by lia; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
          | intros v b Hf; discriminate
          | exact HK0 | ].
        intros R' M' model' A' u vals' E' HL' HA2 HR' HK' DI' HRT HINC' HBR2 HAP HSHB HAB HBLK HIMG. subst vals' E'.
        set (vals2 := vals ++ junk_vals R') in *.
        change (Env (vals_ev vals2) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals2) in HR', HK'.
        rewrite HL in HL', HA2, HR', HK'. change (71 + 10)%nat with 81%nat in HA2, HK'. change (71 + 32)%nat with 103%nat in HL'.
        destruct (model_rt_fds _ _ HRT) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U3). pose proof HBR2 as (_ & _ & U4 & _ & _).
        assert (NEQ : u <> A1).
        { specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)). cbn [fst snd] in HAP. lia. }
        assert (X0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (XV : hdr_valsA vals2) by (subst vals2; apply hdr_appA; [exact HV | rewrite HL; lia]).
        assert (X48 : vals_ev vals2 48 = Z_to_bv 64 A1) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P48).
        assert (X70 : vals_ev vals2 70 = Z_to_bv 64 (CAPk k)) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); rewrite <- Heq; exact P70).

        apply Forall_app in HK' as [HKB HK'].
        assert (HKU : know_ok ASEGS (ENVG vals2) (mrestrict (ahid A' model') M') knGb0).
        { change knGb0 with (kn_blk2A 81 ++ keepalloc_G knLPgA). apply Forall_app. split.
          - unfold kn_blk2A. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [kentry_ok edenot ev ENVA]; rewrite HA2, u_small by lia; lia.
          - exact HK'. }
        clear HK' HKB HK1 HR0.
        assert (HC2 : rdn ASEGS M' (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- Heq, <- HC1. symmetry. apply rdn_agree. intros j Hj. rewrite u_small by lia. symmetry. apply HBLK; [lia|].
          exists (A1, CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        clear HC1 DI0 HBLK HIMG HAB F1 F2 HRT. clear M1 model0 R0.

        drv_block0 HIok Hsp DL HR' HKU DI' X0 scr0 103%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC3 : rdn ASEGS M (Z_to_bv 64 A1) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC2. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR' HKU DI' HC2 G1 G2 HSHB. clear M' model'.
        assert (HFL : length (firstn (Z.to_nat (CAPk k)) fdata) = Z.to_nat (CAPk k)) by (rewrite length_firstn; unfold LEN in HlL; lia).

        lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (amemcpy_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def ICok vals2 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
                  (adebit L cr (2 * CAPk k)) A' u (2 * CAPk k) u A1 (CAPk k) (firstn (Z.to_nat (CAPk k)) fdata) MSO [(48%nat, 65536)] [] 0xb0174 K) end end;
          [ exact HR | exact HK
          | rewrite HL'; vm_compute; reflexivity | rewrite HL'; vm_compute; reflexivity | rewrite HL'; lia
          | exact X0 | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite X0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact HA2
          | regv HR (11%bv : reg); cbn [edenot ev ENVA]; exact X48
          | regv HR (12%bv : reg); cbn [edenot ev ENVA]; exact X70
          | lia
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI
          | left; reflexivity | lia | lia
          | apply (src_blk_aacc scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI));
              [right; left; reflexivity | lia | lia | exact (di_blksh _ _ _ _ _ _ _ _ _ _ DI (A1, CAPk k) ltac:(right; left; reflexivity))]
          | lia | lia
          | apply (src_blk_app_rng scfg L ar C HI HIok sp0 Hsp _ _ _ _ _ _ _ A1 (CAPk k) A1 (CAPk k) (di_inv _ _ _ _ _ _ _ _ _ _ DI)); [right; left; reflexivity | lia | lia]
          | intros i Hi; right; exists (A1, CAPk k); split; [right; left; reflexivity | cbn [fst snd]; lia]
          | exact HC3
          | specialize (HAP (A1, CAPk k) ltac:(left; reflexivity)); cbn [fst snd] in HAP; lia
          | intros i nb Hf; cbn in Hf;
            destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL'; lia|];
                                             rewrite X48, u_small by lia; rewrite lb_remove_hdA; exists (CAPk k); split; [lia|]; split; [left; reflexivity | exact HBR] | discriminate]
          | intros v b Hf; discriminate
          | exact HK0
          | ].
        intros R3 M3 model3 vals' E' HL3 HR3 HK3 DI3 HRT3 HDST HBLK3 HIMG3. subst vals' E'.
        rewrite HL' in HL3, HR3. change (103 + 32)%nat with 135%nat in HL3.
        change (sr_after_call_j _ (map ridx c_kept) 103) with srGc0 in HR3.
        change (keep_allocA MSO 4096 [(48%nat, 65536)] [] _) with knGc0 in HK3.
        destruct (model_rt_fds _ _ HRT3) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        set (vals3 := vals2 ++ junk_vals R3) in *.
        change (Env (vals_ev vals3) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals3) in HR3, HK3.
        assert (Y0 : vals_ev vals3 0 = sp0) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X0).
        assert (YV : hdr_valsA vals3) by (subst vals3; apply hdr_appA; [exact XV | rewrite HL'; lia]).
        assert (Y48 : vals_ev vals3 48 = Z_to_bv 64 A1) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X48).
        assert (Y70 : vals_ev vals3 70 = Z_to_bv 64 (CAPk k)) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact X70).
        assert (Y81 : vals_ev vals3 81 = Z_to_bv 64 u) by (subst vals3; rewrite vals_ev_app_l by (rewrite HL'; lia); exact HA2).
        clear HR HK DI HC3 HBLK3 HIMG3 F1 F2 HRT3. clear M model R.

        drv_block0 HIok Hsp DL HR3 HK3 DI3 Y0 scr0 135%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC4 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HDST. apply rdn_agree. intros j Hj. apply EQA. }
        clear EQM EQH EQA SBM HR3 HK3 DI3 HDST G1 G2. clear M3 model3.

        lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
        eapply (afree_site scfg L ar C IL HI HIok sp0 Hsp Hal DL M0 M0_def vals3 _ sr kn R M model [(u, 2 * CAPk k); (A1, CAPk k)] LK0
                  (adebit L cr (2 * CAPk k)) A' A1 (CAPk k) MSO [] [] 0xb017c K) end end;
          [ exact HR | exact HK
          | rewrite HL3; vm_compute; reflexivity | rewrite HL3; vm_compute; reflexivity | rewrite HL3; lia
          | exact Y0 | vm_compute; reflexivity
          | regv HR (2%bv : reg); cbn [edenot ev ENVA]; rewrite Y0; apply alu_add_w_litA
          | unfold MSO; lia | reflexivity
          | right; left; reflexivity
          | regv HR (10%bv : reg); cbn [edenot ev ENVA]; exact Y48
          | regv HR (4%bv : reg); reflexivity
          | regv HR (1%bv : reg); reflexivity
          | lia | reflexivity
          | exact DI
          | intros i nb Hf; discriminate
          | intros v b Hf; discriminate
          | exact HK0 | ].
        intros R4 M4 model4 A4 vals' E' HL4 HR4 HK4 DI4 HRT4 HINC4 HAB4 HBLK4 HIMG4. subst vals' E'.
        rewrite (lb_remove_2A u (2 * CAPk k) A1 (CAPk k) NEQ) in DI4, HBLK4.
        rewrite HL3 in HL4, HR4. change (135 + 32)%nat with 167%nat in HL4.
        change (sr_after_call_j _ (map ridx c_kept) 135) with srGd0 in HR4.
        change (keep_allocA MSO 4096 [] [] _) with knGd0 in HK4.
        destruct (model_rt_fds _ _ HRT4) as (G1 & G2). rewrite F1 in G1. rewrite F2 in G2.
        set (vals4 := vals3 ++ junk_vals R4) in *.
        change (Env (vals_ev vals4) (blobs_ev [[]; []; []; []; fdata])) with (ENVG vals4) in HR4, HK4.
        assert (W0 : vals_ev vals4 0 = sp0) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y0).
        assert (WV : hdr_valsA vals4) by (subst vals4; apply hdr_appA; [exact YV | rewrite HL3; lia]).
        assert (W70 : vals_ev vals4 70 = Z_to_bv 64 (CAPk k)) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y70).
        assert (W81 : vals_ev vals4 81 = Z_to_bv 64 u) by (subst vals4; rewrite vals_ev_app_l by (rewrite HL3; lia); exact Y81).
        assert (HC5 : rdn ASEGS M4 (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC4. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply HBLK4; [lia|].
          exists (u, 2 * CAPk k). split; [left; reflexivity|]. cbn [fst snd]. lia. }
        clear HR HK DI HC4 HBLK4 HIMG4 HAB4 F1 F2 HRT4. clear M model R.

        drv_block0 HIok Hsp DL HR4 HK4 DI4 W0 scr0 167%nat.
        pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
        destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite G1 in F1. rewrite G2 in F2.
        assert (HC6 : rdn ASEGS M (Z_to_bv 64 u) (Z.to_nat (CAPk k)) = Some (firstn (Z.to_nat (CAPk k)) fdata)).
        { rewrite <- HC5. apply rdn_agree. intros j Hj. apply EQA. }

        lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
          set (valsR := relayV vals4 Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
          apply (HRD (k + 1) len 65536 u valsR Rc M model A4 (adebit L cr (2 * CAPk k)))
        end.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * lia.
        * lia.
        * rewrite CAPk_S by lia. lia.
        * reflexivity.
        * unfold valsR. apply hdr_relayA. exact WV.
        * unfold valsR. rewrite relayV_38. unfold gr. regv1 HR. change (nth 21 srGd (ELit 0)) with cap2_xA.
          rewrite CAPk_S by lia. apply (cap2_x_valA vals4 (CAPk k) W70); lia.
        * unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
        * unfold valsR. rewrite relayV_70. unfold gr. regv1 HR. rewrite Heq. exact W70.
        * unfold valsR. rewrite relayV_71. unfold gr. regv1 HR. reflexivity.
        * unfold valsR, ENVA. relay_regs HR; try (relay2 HR; reflexivity).
        * rewrite knLPA_split. apply Forall_app. split.
          -- apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(u, 2 * CAPk k)] LK0 (adebit L cr (2 * CAPk k)) A4 M model 48%nat u (2 * CAPk k) 65536 DI);
               [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact W0].
             unfold valsR. rewrite relayV_48. unfold gr. regv1 HR. exact W81.
          -- unfold valsR, ENVA. eapply relay_know6; [exact HK | vm_compute; reflexivity | vm_compute; reflexivity].
        * rewrite Heq. exact HC6.
        * rewrite CAPk_S by lia. exact DI.
        * intros x Hx. apply HINC4. apply HINC'. apply HINC. exact Hx.
        * split; [exact F1 | exact F2].
        * destruct Hcr as [Hc1 Hc2]. unfold credA, adebit. cbn [fst snd]. rewrite CAPk_S by lia. split; nia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_okA : forall n : nat, lp_atA (Z.of_nat n).
  Proof.
    induction n as [|n IH].
    - apply loop_stepA. apply read_okA. unfold lp_atA. intros. exfalso. lia.
    - apply loop_stepA. apply read_okA. replace (Z.of_nat (Datatypes.S n) - 1) with (Z.of_nat n) by lia. exact IH.
  Qed.

  (* [comment removed for export] *)
  Variable cr0 : credit.
  Hypothesis Hcr0 : credA 0 (adebit L cr0 65536).

  Theorem drv_fileA : file_kA scfg L ar HI sp0 path fs0 fdata p0 p1 can M0 LK0 cr0 A0 K.
  Proof.
    unfold file_kA.
    intros vals R M model A A1 HL P0 P1 P2 P3 P48 HR HK DI HINC MF MS HBR.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    assert (HV : hdr_valsA vals) by (unfold hdr_valsA; repeat split; assumption).
    change (Pm4DrvA.ENVA fdata vals) with (ENVG vals) in HR, HK.

    drv_block0 HIok Hsp DL HR HK DI P0 scr0 70%nat.
    pose proof (block_nolog _ _ _ _ _ EQM EQH) as EQA.
    destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite MF in F1. rewrite MS in F2.
    pose proof (read_okA (LEN + 1) ltac:(replace (LEN + 1 - 1) with (Z.of_nat (length fdata)) by (unfold LEN; lia); apply loop_okA)) as RD.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      set (valsR := relayV vals Rc (gr Rc 21) (gr Rc 9) (gr Rc 19) [gr Rc 12]);
      apply (RD 0 0 65536 A1 valsR Rc M1 model0 A (adebit L cr0 65536))
    end.
    - lia.
    - unfold CAPk. rewrite Z.pow_0_r. lia.
    - unfold LEN. lia.
    - unfold LEN. lia.
    - unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - reflexivity.
    - unfold valsR. apply hdr_relayA. exact HV.
    - unfold valsR. rewrite relayV_38. unfold gr. regv1 HR0. unfold CAPk. rewrite Z.pow_0_r. reflexivity.
    - unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
    - unfold valsR. rewrite relayV_70. unfold gr. regv1 HR0. reflexivity.
    - unfold valsR. rewrite relayV_71. unfold gr. regv1 HR0. reflexivity.
    - unfold valsR, ENVA. relay_regs HR0; try (relay2 HR0; reflexivity).
    - rewrite knLPA_split. apply Forall_app. split.
      + apply (kn_blkA_of_inv scfg L ar C IL HI HIok sp0 Hsp DL M0 valsR _ [(A1, 65536)] LK0 (adebit L cr0 65536) A M1 model0 48%nat A1 65536 65536 DI0);
          [left; reflexivity | lia | | unfold valsR; rewrite relayV_lo by lia; exact P0].
        unfold valsR. rewrite relayV_48. unfold gr. regv1 HR0. exact P48.
      + unfold valsR, ENVA. eapply relay_know6; [exact HK1 | vm_compute; reflexivity | vm_compute; reflexivity].
    - reflexivity.
    - unfold CAPk. rewrite Z.pow_0_r. exact DI0.
    - exact HINC.
    - split; [exact F1 | exact F2].
    - exact Hcr0.
  Qed.
End DrvG.
End FPX_1.
