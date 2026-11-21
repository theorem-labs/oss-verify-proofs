(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, the 6144513-byte zero-filled stack window): changed XC_CELLS_L, XC_CELLS_T, XC_REST and 31 more; added vmc_refl; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8DrvExit.v, 2172 lines within its lines 18-3136. *)
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
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm4IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm4DrvEntry Pm4Drv_defs Pm4DrvLib Pm4DrvRead Pm4DrvPiece Pm4DiagLoopK Pm4DrvStdio Pm4DrvPrintfK Pm4DrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require L5Defs L5KnA L5Core ArtMem Pm4ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4DrvP_dpX Pm4DrvP_dpX2_pre Pm4DrvP_dpX3_pre Pm4DrvP_dpX4_pre Pm4DrvP_dpXd_2 Pm4DrvP_dpXd_3 Pm4DrvP_dpXd_4 Pm4DrvP_dpXe Pm4DrvP_dpXL Pm4DrvP_dpXL2_pre Pm4DrvP_dpXL3_pre Pm4DrvP_dpXL4_pre.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @nil]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Lists; @ListDef; @Forall]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @M; @loaded_segments]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Datatypes; @fst]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Datatypes; @snd]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cells_at]; [@Stdlib; @Lists; @List; @nth_error]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @In]; [@Stdlib; @Lists; @List; @Forall_forall]; [@Stdlib; @Lists; @List; @nth_error_In]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @XC_CELLS_T]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @XC_CELLS_L]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @XC_REST]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @exitR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @ATX]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @exitT]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cells_at_sub]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @true]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @exitL]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SeqExec; @rdn_app]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @nat_to_word]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_add_unsigned]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @ECALLW]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @SpuriousCfg]; [@Corelib; @Init; @Datatypes; @bool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @H_off_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @lazy_cover]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @A_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @MInv]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @mrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcctShape; @srz_msteps_restricted_T]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @asegs_wx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @hclean]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @munrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @mrestrict_munrestrict]; [@Stdlib; @Lists; @List; @existsb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cell_eqb]; [@Corelib; @Init; @Logic; @ex]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StreamSim; @wseg_ok]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @writable]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_window]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AgentLib; @u64_lit]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @art_bytes1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @EX_CELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @di_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ri_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @cell_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ahid]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dla_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @rdn_mrestrict_eq]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @f_equal]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @vis_low]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @woff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @range_avoids]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @SHW_WINS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @shchk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmIcptDrvA; @aic_shadow_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @LOWSH_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @LOWSH_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @HIGHSH_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @HIGHSH_HI]; [@Stdlib; @Bool; @Bool; @andb_false_intro2]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_in_ranges]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @page_allowedb]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmIcptDrvA; @aic_img_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dla_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dla_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_POISON]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @icl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4IcptLayout; @aicl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @in_shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @byte_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_allowed]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_size]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @writable_of_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @exit_preT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPrintfK; @stdoutA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPrintf1; @stdoutXA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_exit]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPrintfK; @SOBUF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX; @AS0DRVP_dpX; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @store_ok_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @wsg_writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @sh_writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @ex_cell_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cell_in_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cells_at_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cells_at_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @img_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX; @AS0DRVP_dpX; @dpX_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @img_clear]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @wsg_writableZ0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u32_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @cell1_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u8_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX; @AS0DRVP_dpX; @KS_dpX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @msteps_vis_fx]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @Fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvNodesLazyK; @rz_exit_at_lit_lz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @fetch_exitA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @is_ecall_ECALLW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @sbm_halted_eq]; [@Corelib; @Init; @Logic; @eq_trans]; [@Corelib; @Init; @Logic; @proj2]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @sbm_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @exit_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @exitA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @stdoutPA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @XC_CELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXe; @AS0DRVP_dpXe; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXe; @AS0DRVP_dpXe; @dpXe_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXe; @AS0DRVP_dpXe; @KS_dpXe]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @zero_lines]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @dpX2_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @KS_dpX2_pre]; [@Corelib; @Init; @Datatypes; @orb]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Bool; @Bool; @orb_true_iff]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @or_iff_morphism]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @rdn_tr]; [@Corelib; @Init; @Nat; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @rdn_cons1]; [@Corelib; @Init; @Nat; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPrintf1; @nl_pt]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_mono]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @map]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeLaws; @t_exit_has_nil]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @sbm_lazy_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @sbm_fds']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_iov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_buf]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Corelib; @Numbers; @BinNums; @positive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @WV_KEEP]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Init; @Logic; @eq_sym]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_2; @AS0DRVP_dpXd_2; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_2; @AS0DRVP_dpXd_2; @dpXd_2_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_2; @AS0DRVP_dpXd_2; @KS_dpXd_2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv_sbm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_done]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @dpX3_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @KS_dpX3_pre]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_3; @AS0DRVP_dpXd_3; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_3; @AS0DRVP_dpXd_3; @dpXd_3_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_3; @AS0DRVP_dpXd_3; @KS_dpXd_3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @dpX4_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @KS_dpX4_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_4; @AS0DRVP_dpXd_4; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_4; @AS0DRVP_dpXd_4; @dpXd_4_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXd_4; @AS0DRVP_dpXd_4; @KS_dpXd_4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @FPX_1; @Exit; @exit_preL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL; @AS0DRVP_dpXL; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL; @AS0DRVP_dpXL; @dpXL_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL; @AS0DRVP_dpXL; @KS_dpXL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @dpXL2_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @KS_dpXL2_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @dpXL3_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @KS_dpXL3_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @dpXL4_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @KS_dpXL4_pre]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition XC_CELLS : list (Z * Z * Z) :=
  [(7070272, 4, 0); (7070307, 1, 0); (7069744, 8, 7069752); (7069736, 4, 1); (7069760, 8, 1317312); (7070016, 8, 654096); (7069732, 4, 0); (7069752, 8, 0); (7071704, 8, 0); (1464080, 8, 1463848); (1463988, 4, 4294967295); (1463888, 8, 0); (1463904, 8, 0); (1463856, 8, 0); (1463864, 8, 0); (1463840, 8, 1463608); (1463600, 8, 1463368); (1463508, 4, 4294967295); (1463408, 8, 0); (1463424, 8, 0); (1463376, 8, 0); (1463384, 8, 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATX (ls2 : bool) : list (Z * Z * Z) :=
  if ls2 then [(7070307, 1, 0); (7069744, 8, 7069752); (7069736, 4, 4); (7069760, 8, 1317312); (7070016, 8, 654096); (7069768, 8, 1317312); (7070024, 8, 722136); (7069776, 8, 1037552); (7070032, 8, 1463160); (7069784, 8, 483400); (7070040, 8, 0); (7069732, 4, 0); (7069752, 8, 0)]
  else [(7070307, 1, 0); (7069744, 8, 7069752); (7069736, 4, 2); (7069760, 8, 1317312); (7070016, 8, 654096); (7069768, 8, 1317312); (7070024, 8, 722136); (7069732, 4, 0); (7069752, 8, 0)].
Definition XC_REST : list (Z * Z * Z) :=
  [(7070272, 4, 0); (7071704, 8, 0); (1464080, 8, 1463848); (1463988, 4, 4294967295); (1463888, 8, 0); (1463904, 8, 0); (1463856, 8, 0); (1463864, 8, 0); (1463840, 8, 1463608); (1463600, 8, 1463368); (1463508, 4, 4294967295); (1463408, 8, 0); (1463424, 8, 0); (1463376, 8, 0); (1463384, 8, 0); (6931796, 1, 0)].
Definition XC_CELLS_T : list (Z * Z * Z) :=
  [(7070272, 4, 0); (7070307, 1, 0); (7069744, 8, 7069752); (7069736, 4, 2); (7069760, 8, 1317312); (7070016, 8, 654096); (7069732, 4, 0); (7069752, 8, 0); (7071704, 8, 0); (1464080, 8, 1463848); (1463988, 4, 4294967295); (1463888, 8, 0); (1463904, 8, 0); (1463856, 8, 0); (1463864, 8, 0); (1463840, 8, 1463608); (1463600, 8, 1463368); (1463508, 4, 4294967295); (1463408, 8, 0); (1463424, 8, 0); (1463376, 8, 0); (1463384, 8, 0); (7069768, 8, 1317312); (7070024, 8, 722136); (6931796, 1, 0)].
Definition XC_CELLS_L : list (Z * Z * Z) :=
  [(7070272, 4, 0); (7070307, 1, 0); (7069744, 8, 7069752); (7069736, 4, 4); (7069760, 8, 1317312); (7070016, 8, 654096); (7069732, 4, 0); (7069752, 8, 0); (7071704, 8, 0); (1464080, 8, 1463848); (1463988, 4, 4294967295); (1463888, 8, 0); (1463904, 8, 0); (1463856, 8, 0); (1463864, 8, 0); (1463840, 8, 1463608); (1463600, 8, 1463368); (1463508, 4, 4294967295); (1463408, 8, 0); (1463424, 8, 0); (1463376, 8, 0); (1463384, 8, 0); (7069768, 8, 1317312); (7070024, 8, 722136); (7069776, 8, 1037552); (7070032, 8, 1463160); (7069784, 8, 483400); (7070040, 8, 0); (6931796, 1, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6938408) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x165740 <= i < 0x166840 -> MV (Z_to_bv 64 i) = None).
Definition exitT (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_T
  /\ rdn ASEGS MV (Z_to_bv 64 6938408) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x165740 <= i < 0x166840 -> MV (Z_to_bv 64 i) = None).
Definition exitL (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_L
  /\ rdn ASEGS MV (Z_to_bv 64 6938408) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x165740 <= i < 0x166840 -> MV (Z_to_bv 64 i) = None).
Definition exitR (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_REST
  /\ rdn ASEGS MV (Z_to_bv 64 6938408) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x165740 <= i < 0x166840 -> MV (Z_to_bv 64 i) = None).
Lemma cells_at_in : forall MV l a n v, cells_at MV l -> In (a, n, v) l ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l a n v HC Hin. exact (proj1 (Forall_forall _ _) HC (a, n, v) Hin). Qed.
Ltac in_cells := cbn [In]; solve [repeat first [left; reflexivity | right]].
Lemma cells_at_sub : forall MV l1 l2 l, cells_at MV l1 -> cells_at MV l2 -> (forall c, In c l -> In c l1 \/ In c l2) -> cells_at MV l.
Proof. intros MV l1 l2 l H1 H2 Hs. apply Forall_forall. intros c Hc. destruct (Hs c Hc) as [X|X]; [exact (proj1 (Forall_forall _ _) H1 c X) | exact (proj1 (Forall_forall _ _) H2 c X)]. Qed.
Lemma exitT_of_R : forall tid MV, exitR tid MV -> cells_at MV (ATX false) -> exitT tid MV.
Proof.
  intros tid MV (XR & REST) XT. split; [|exact REST]. apply (cells_at_sub MV XC_REST (ATX false)); [exact XR | exact XT|].
  intros c Hc. unfold XC_CELLS_T in Hc. cbn [In] in Hc. unfold XC_REST, ATX.
  repeat (destruct Hc as [<-|Hc]; [first [left; in_cells | right; in_cells]|]). destruct Hc.
Qed.
Lemma exitL_of_R : forall tid MV, exitR tid MV -> cells_at MV (ATX true) -> exitL tid MV.
Proof.
  intros tid MV (XR & REST) XT. split; [|exact REST]. apply (cells_at_sub MV XC_REST (ATX true)); [exact XR | exact XT|].
  intros c Hc. unfold XC_CELLS_L in Hc. cbn [In] in Hc. unfold XC_REST, ATX.
  repeat (destruct Hc as [<-|Hc]; [first [left; in_cells | right; in_cells]|]). destruct Hc.
Qed.

Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x141724) = Some ECALLW.
Proof. vmc_refl. Qed.

(* [comment removed for export] *)
Lemma msteps_vis_fx : forall (scfg : SpuriousCfg) (H : word -> bool) (A : list (Z * Z)) (fx fx' : PropExec.FPState) R (pc : word) M R' (pc' : word) MV' (model : Model) T,
  lzinv ASEGS H A model ->
  msteps ASEGS (@mkst fx R pc (mrestrict H M) (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) ->
  (forall M' (model' : Model), MInv A model' -> same_but_materialized model model' -> mrestrict H M' = MV' ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M' (seg_rom ASEGS)) model') T) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M (seg_rom ASEGS)) model) T.
Proof.
  intros scfg H A fx fx' R pc M R' pc' MV' model T (HH & HL & HA & HM & Hh) MS KONT.
  apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) model T HL HA HM Hh MS).
  intros model1 MI1 SBM HC.
  change (unrestrict H (ms_mem (@mkst fx R pc M (seg_rom ASEGS))) (@mkst fx' R' pc' MV' (seg_rom ASEGS))) with (@mkst fx' R' pc' (munrestrict H M MV') (seg_rom ASEGS)).
  apply (KONT _ model1 MI1 SBM). apply As0DrvKitA.mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.

(* [comment removed for export] *)
Definition cell_eqb (c d : Z * Z * Z) : bool := Z.eqb (fst (fst c)) (fst (fst d)) && Z.eqb (snd (fst c)) (snd (fst d)) && Z.eqb (snd c) (snd d).
Lemma cell_in_b : forall c l, existsb (cell_eqb c) l = true -> In c l.
Proof.
  intros [[a n] v] l H. apply existsb_exists in H as ([[a' n'] v'] & Hin & E). unfold cell_eqb in E. cbn [fst snd] in E.
  apply andb_prop in E as (E & E3). apply andb_prop in E as (E1 & E2). apply Z.eqb_eq in E1, E2, E3. subst. exact Hin.
Qed.
Lemma wsg_writableZ0 : forall (MV : word -> option byte) a n, wseg_ok ASEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> (0 <=? a) && (0 <=? n) && (a + n <=? 2 ^ 63) = true ->
  L5Defs.L5.writable ASEGS MV a n.
Proof.
  intros MV a n W Hb. apply andb_prop in Hb as (Hb & B3). apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2, B3. intros d k Hd Hk.
  apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) (Z.to_nat n) k a (a + n)); first [exact W | reflexivity | lia | (rewrite u64_lit by lia; lia)].
Qed.
Lemma cell1_of : forall (MV : word -> option byte) a v, rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat 1) = Some (word_to_le_bytes (Z.to_nat 1) (Z_to_bv 64 v)) -> (0 <=? v) && (v <? 2 ^ 64) = true ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof. intros MV a v H Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact H. Qed.
Ltac xhyp a := match goal with H : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact H end.
Ltac xcell EXB XCB a n v := first [ exact (EXB a n v ltac:(vm_compute; reflexivity)) | exact (XCB a n v ltac:(vm_compute; reflexivity)) ].
Ltac xprem SHW EXB XCB DESC :=
  lazymatch goal with
  | |- L5Defs.L5.writable _ _ ?a ?n =>
      lazymatch a with
      | Z.pos _ => first [ exact (SHW a n ltac:(vm_compute; reflexivity)) | exact (wsg_writableZ0 _ a n ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) ]
      | _ => assumption
      end
  | |- L5Defs.L5.img_clear _ ?lo ?hi => first [ assumption | (let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply DESC; lia) ]
  | |- L5Defs.L5.u64_at _ _ ?a ?v => first [ xhyp a | xcell EXB XCB a 8 v ]
  | |- L5Defs.L5.u32_at _ _ ?a ?v => first [ xhyp a | xcell EXB XCB a 4 v ]
  | |- L5Defs.L5.u8_at _ _ ?a ?v => first [ xhyp a | (apply cell1_of; [xcell EXB XCB a 1 v | vm_compute; reflexivity]) ]
  | |- _ => assumption
  end.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Exit.
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
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  (* [comment removed for export] *)
  Lemma ex_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) EX_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hex _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6c0000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_vis : forall LB LK cr A M (model : Model) ls2, dinvA LB LK cr A M model -> cells_at M (ATX ls2) -> cells_at (mrestrict (ahid A model) M) (ATX ls2).
  Proof using HIok DL Hsp.
    intros LB LK cr A M model ls2 D HC. apply Forall_forall. intros [[a n] v] Hc. pose proof (proj1 (Forall_forall _ _) HC _ Hc) as X. cbn [fst snd] in X |- *.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6c0000).
    { destruct ls2; unfold ATX in Hc; cbn [In] in Hc; repeat (destruct Hc as [Hc|Hc]; [injection Hc as <- <- <-; cbn; lia|]); destruct Hc. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Definition SHW_WINS : list (Z * Z) := [(2147469652, 2147471668); (2147628616, 2147628668); (2147633896, 2147634440)].
  Definition shchk (a n : Z) : bool := (0 <=? n) && existsb (fun w => (fst w <=? a) && (a + n <=? snd w)) SHW_WINS.
  Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model -> shchk a n = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SkK0!2+1+2+2!1+;0|600;!1,92!1+83|30;!1+8!1,95!1+:6!1,7'`N!2'_A,5#4!3'A+2+2#1!3'C+2+2#1!3'_70$w;R0!2'_=!2'_A:#6!2'_A!2'^8#6#5;'aD!3+=+^L!2'_A,5#5,^6%~R!3+=+^L!2'_A#2#1,^6!2'O#3#2$n;R+2$m;R+2!5'U>%~R!2'O#2#1!3+=+^L!2'_A#3#2,^6%~R!3+=+^L!2'_A#2#1,^6!2'O#3#2$~R>$~R%~R!2'O#3#2!3+=+^L!2'_A#4#3,^6#2!2'_D#2#1%n;R+2%m;R+2>!2'O,5#:%~R#1+^L!1+;#2%~R!3+=+^L!3'_7#3#2#1,^6!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6!2'^8#>#=!2'_=!2'_A:#>!2'_AE;!3'J0#1'aD!3'J0#2'aD!3'C+2+2#2!2'_A!3'A+2+2#6#F!2'_A!2'^8#F#E!3'C+2+2#6!3+=+^L!2'_A!3'A+2+2#7#G,^6!3'A+2+2#<!2'^8#N#M!3'C+2+2#>!2'O,5#1!2+MP!2'P#1#O!2'^8#Q#2!1,4|N3fffc954;!1,4|N3fffd134;!4,3+2+2ST!3+=0U#B!1,4|O00023648;!1,4|O0002367c;!4,3+2+2WX!3+=0Y#B!1,4|O00024ae8;!1,4|O00024d08;!4,3+2+2[\!2+T!3+=0^0#B+^0!2+TZ^1!1,Q6!2'O:#U!2'O!2'^8#V#UI!2'@3#6!1'a:!3+=7!1#Y^6^3!3+=+^L!3'`[#Z#X^6,Y!3'A+2+2U!2'^8#U#T!3'C+2+2U!2'^8#V#7!3+=+2#5^<|10;!1,4^>!1,4|50f;!2'_G^?^@!2'P,5^?!2'_B^?^@%~R^B%~R!2'O,5^@!2'P,5^C!2'O,5^?$Ha;R^E$~R+_H!3'_I^?^@#2%Ha;R^E%~R+_H!2'O,5^C!2'^;3/sp0;|40;!1,4^I!2'a8^H^J!2'^B^H^J!2'O,5^L%~R!2'O,5^H%~R!2'O,5^J^M!2'a9^H^J!3+=+2^J,5!2'a<^H^J%~R!1'a:^P!3+=+2^H!2'^8!2'a;^J^Q^L!2'a=^H^J!2'P,5^J%~R^T!2+M^M!2'P^L^J!2'a>^H^J%~R!2'P^J,5!2+M!2'P^J^L!2'O^L,5!2'a?^H^J%~R^P!3+=+2^Q,5!2'a@^H^J%~R^P!3+=+2^L^H!2'O,5#B!2'O,5#D!2'P#E#^6}5!2,`0+2_2}2!2,`0+2_4!2,`0+2,`1}4!2,`0+2_7}3!2,`0+2_9!1,7+_J!3,0+_J!2,_[!3,_\+2_3!3,_\+2_5_6,`2!3,0+_J!2,_[!3,_\+2_8!3,_\+2_:_6,`2_;!1+;+_J!2,_K+2#3!2,_K+2#5!1,`4+2!4,`3+2_>#2!4,`3+2_?#4_@!1+_L+2!1+_N+2!2,_S+2^>|21;!2,_S+2_E!7,_M_C'_O+_P+_P,_Q!4,_R+2_D,`;_F,_U!1,Q+_P!2,`9+2,5!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7_D,_U!2,`9+2S!2,_S+2,6!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7_L,_U!3,`6+2_L_F!2,`9+2T!1,4|^13fff80000000;|11;!7,_M_C'_O+_P+_P,_Q!4,_R+2!2,`9+2_P,`7!2,_S+2_Q,_U!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#7!3,`6+2_L_D!2'_V_C,_Q!4'_W#1#3vv!2,^3+^L,^6!3+=+^L!2'_X#1#3,^6!3'_Y+2,5#2!2'P#2#4!2'O,5#3!2'^8#4#7!2'O_P#7!2+M_Z#9!2'^8#6#7!2'O^H^C!2+M!2'OS#5!2'P#5T!2+M!2'O'aG#6!2'P#6'aH!2'^8#W#8!3+=+2#6`3!2'O,5#C|N3fff8000;!1,4`6!1,4|O0fff7000;!2'O,5#E!2'P#F#^7!2,_K+2#2!7,`:_C'_O+_P+_P,_Q_M!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;_O,_U!2,`9+2`7!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2`=,`7_L,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;!2,`9+2`8,_U!2'OS#1!2+M`?!2'P#1T!2+M!2'O`7#2!2'P#2`8!1'aM^6%~R!3+=+^L!1'aN#1,Y!3+=+^L#2,^6%~R!3+=+^L#1,^6!3+=+^L!1'aN#2,Y$b;R+^L!5'U`C`D%~R!3+=+^L#1,^6!3+=+^L!1'aN#2,Y$~R`C$~R%~R!3+=+^L#2,^6!3+=+^L!1'aN#3,Y#1!1'aP#1%b;R+^L`D!1,4|N3fffd000;!2'P#8`G!2'O`G#8!2'aO#^0!1'aM!2'@3#9!1'`T#\!1,4|A00000;|@0000;!1,4`M!2'^8#[#<!3+=+2#:`Ovd!2,^3+2`O`P!2'O,5#G!2'P#G#^8!2'O`N`L!2'O,5#I!2'P#J#^;!2,`9+2`N!2,`9+2`L!1'aT/L;!5'aU/L;/ar;/IL;/sp0;/DL;!1,4|F2c0000;!2'^8`L^J!2'O`\`[!2,`9+2^J!3,`6+2`Xa1!2,`9+2`[!1'aV/L;!5'aW/L;/ar;/IL;/sp0;/DL;&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;a1,_U_U_V^T#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S^T$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`Va6#2#1#F$r;R0!2+T!2'O`\:!2'O;`L!1,4|A04aa0;!1,4|A04ac0;!4,3+2+2a9a:!1,4|A04c00;!1,4|A04c60;!4,3+2+2a<a=!1,4|A04c80;!1,4|A04ea0;!4,3+2+2a?a@!1,4|A050a0;!1,4|A05b20;!4,3+2+2aBaC!1,4|A05b60;!1,4|A084e0;!4,3+2+2aEaF!1,4|A08700;!1,4|A08760;!4,3+2+2aHaI!1,4|A08860;!1,4|A089a0;!4,3+2+2aKaL!1,4|D5b240;!1,4|D5b3e0;!4,3+2+2aNaO!1,4|D65740;!1,4|D66840;!4,3+2+2aQaR!1,70!3,00aSaT!3,00aPaU!3,00aMaV!3,00aJaW!3,00aGaX!3,00aDaY!3,00aAaZ!3,00a>a[!2+T!2'O`\a9!2'Oa:`L!2,`9+2a9!2,`9+2a:!3'A+2+2a;!3'C+2+2a;!2+T!2'O`\a<!2'Oa=`L!2,`9+2a<!2,`9+2a=!3'A+2+2a>!3'C+2+2a>!2+T!2'O`\a?!2'Oa@`L!2,`9+2a?!2,`9+2a@!3'A+2+2aA!3'C+2+2aA!2+T!2'O`\aB!2'OaC`L!2,`9+2aB!2,`9+2aC!3'A+2+2aD!3'C+2+2aD!2+T!2'O`\aE!2'OaF`L!2,`9+2aE!2,`9+2aF!3'A+2+2aG!3'C+2+2aG!2+T!2'O`\aH!2'OaI`L!2,`9+2aH!2,`9+2aI!3'A+2+2aJ!3'C+2+2aJ!2+T!2'O`\aK!2'OaL`L!2,`9+2aK!2,`9+2aL!3'A+2+2aM!3'C+2+2aM!2+T!2'O`\aN!2'OaO`L!2,`9+2aN!2,`9+2aO!3'A+2+2aP!3'C+2+2aP!2+T!2'O`\aQ!2'OaR`L!2,`9+2aQ!2,`9+2aR!3'A+2+2aS!3'C+2+2aS!1'a[/IL;!2'a\/IL;/ILY;!3'b0`L^J#1!3'b1#^2#2,5!3'b1#^3#2,5%x;R+2%~Rc2c4!3'b1#^5#2,5!1,4|N3fffc000;!2'^8#^3#A!3+=+2#?c8vd!2,^3+2c8c9!1,45!2'O,5c;!2'a<`Lc;!1,4,6!2'b4`\c>!2'a<c?c;!3+=+2c;,5!1'a:cA!2'^B`Lc;!2'P,5c;!2'Pc;,5!2'^Bc?c;!2'O,5#\!2'P#\#^M!2'O,5#^1!2'P#^2#^P!3,b5+2!2,b6+2c;_6!2,`G+2!1,`H,6!3,0+_J!2,_[!3,_\+2_3!3,_\+2_8cK,`2!3,0+_J!2,_[!3,_\+2_:!3,_\+2!3,`F+2cL_5cK,`2_;!2,_K+2#6!4,`3+2!4,`3+2_@#3!4,`3+2cN#6_@#2!4,`3+2!4,`3+2_?#6_@#4_@!2,`9+2c;!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;cP,_U|32;!2,_S+2cR!8,`5_C'_O+_P+_P,_QcQ_H!7,`:_C'_O+_P+_P,_Q!6,`J_C'_O+_P+_P,_Q#8!7,_M_C'_O+_P+_P,_Q!4,_R+2cS,`;cP,_U!6,b7_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2cP,_T_I,_U!2,`9+2c>!3,`6+2!3,b9+2cP_DcS|31;!2,_S+2cX!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7cY,_U!6,`J_C'_O+_P+_P,_Q#9!8,`5_C'_O+_P+_P,_QcQ_H!7,`:_C'_O+_P+_P,_QcZc[!3,`6+2!3,b9+2cP_LcY!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#:!3,`6+2_L`=!2,`9+2c7!3,`6+2_D`=%~RcD!2+M#7!2'P#6c;%~RcA+^0!2'^8!2'a;c;#4#7!2'O,5#7%~RcD!2+Md8#:!2'^8!2'a;c;#5#8!2+M_Z#<!2'^8#6`7!2'^8#7`7!2'O,5#=!=#1`0!2'P#Dc;d>#=#D^H#>#E#B#C#I#J/Hsp;!2'@3c7!1'aMd@!2'@3!2'a;!2'a<#1'b:'b:!2'@3#A!2'^;3dC$z;R+2!3+=4dB!2'@3!2'a;!2'a<dD'b:'b:!2'a;!2'a<c7'b:'b:!1'@3!2'a;!2'a<#@'b:'b:!2,^3%~R+24dG!2'^8#^4#B!3+=+2#@dJvd!2,^3+2dJdK|<000;!1,4dM!2'O,5c7!2'O,5dN!2'a<c7dN!2'b3#DdN%~R_0%~RdP!2'O,5!2'a<#FdN!3+=+2dN,5!1'a:dT!2'^Bc7dN!2'P,5dN!2'PdN,5!2'a9#MdN!2'^B#NdN%~RdU!3+=+2#N!2'^8!2'a;dN!2'a<#NdNdZ!2'a=#NdN!2'^B#OdN%~RdW!2+M!2'O,5e0!2'Pe0dN!2'a>#OdN!2'^B#PdN%~RdX!2+M!2'PdNe3!2'Oe3,5!2'a?#PdN!2'a<#QdN%~RdT!3+=+2e6,5!2'a@#QdN!2'^B#RdN%~RdT!3+=+2e9#R!2'a<#RdN!2'^B#SdN!2'O,5#^0!2'P#^0#^N!2'O,5#^2!2'P#^3#^Q}<!2,`0+2eA}:!2,`0+2eC!3,`F+2cLeD}9!2,`0+2eF}8!2,`0+2eH!3,_\+2eGeI}1!2,`0+2eK!2,b<eJ!2,b<_5!2,_[!3,_\+2_5!3,_\+2eL_6,`2!2,b6+2dN!3,b5+2eN_6};!2,`0+2eP!3,`F+2cLeI}7!2,`0+2eS!2,b<_6!2,_[!3,_\+2eO!3,_\+2eB!3,_\+2eQ!3,_\+2eD!3,_\+2eR!3,_\+2!3,`F+2cLeT!3,_\+2_8_:,`2!2,_K+2#7!4,`3+2!2,_K+2#9#5_@!2,_K+2#8!4,`3+2!4,`3+2!4,`3+2eV#9_@#3eW#2!4,`3+2!4,`3+2eX#9_@#4cN!2,`9+2dN!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;eZ,_U!8,`5_C'_O+_P+_P,_Qe[_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7cS,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2cS,`;eZ,_U!6,b7_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2eZ,_T_I,_U!2,_S+25!8,`5_C'_O+_P+_P,_Qf0_H!7,_M_C'_O+_P+_P,_Q!4,_R+2f1,_T!3,`6+2!3,b9+2eZ_DcS,_U!8,`5_C'_O+_P+_P,_Qe[_H!7,`:_C'_O+_P+_P,_QcZ!7,_M_C'_O+_P+_P,_Q!4,_R+2cY,`;eZ,_U!3,`6+2!3,b9+2eZ_LcY|22;!2,_S+2f5|23;!2,_S+2f7!7,_M_C'_O+_P+_P,_Q!4,_R+2f1,_T!3,`6+2f6f8,_U!2,`9+2`G!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7f1,_U!6,`J_C'_O+_P+_P,_Q#;!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7f8,_U!6,`J_C'_O+_P+_P,_Q#<!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b9+2_LeZ,_T!3,b9+2_DeZ,_U%~RdW!2+M!2'O,5#9!2'P#9dN%~RdT+^0!2'a;dN#4%~RfA!3+=+2#8!2'^8fB#:%~RdW!2+MA!2'P#:dN!2'a;dN#5!2'^8fE#;!3+=+2#:!2'^8#8#9!2'OS#<!2'a;#;dN!2'a;#<dN!2'@3#@!2'^;3fK!1,42!2'_G^?fM!2'_B^?fM%~R^B%~R!2'O,5fM!2'P,5fO$Ha;R^E$~R+_H!3'_I^?fM#2%Ha;R^E%~R+_H!2'O,5fO!2'O,5#O!2'P#O#^@!2'O,5#Q!2'P#R#^C!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7_L,_U!2,`9+2^?!3,`8+2fX3!7,`:_C'_O+_P+_P,_QfW!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;fY,_U!2'O,5#2!2+Mf[!2'P#2fO!2'_Z#@&heq_x;RdLdK&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UfSfT!2+M!2'O,5#M!2'P#MfO$~RfS$~R!2'P#P#^A!2$H4;RfU$H5;RfV&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q`<_HfZ_U_V%__x1;R+2%~R`@f\!2#1#R#M#2#1#N!2+MdO!2'Pc7fO!1'aMfK!3+=4dAg2$b;R4!3+=+^L!2'aO#^9#1,^6!1'aMdC!2'O`NaF!2'^8aF^J!2'Og7`[!3,`6+2bFa1$r;R0!2+T!2'Og7:!2'O;aF!2+T!2'Og7a9!2'Oa:aF!2+T!2'Og7a<!2'Oa=aF!2+T!2'Og7a?!2'Oa@aF!2+T!2'Og7aB!2'OaCaF!2+T!2'Og7aE!2'OaFaF!2+T!2'Og7aH!2'OaIaF!2+T!2'Og7aK!2'OaLaF!2+T!2'Og7aN!2'OaOaF!2+T!2'Og7aQ!2'OaRaF!3'b0aF^J#1%x;R+2%~RgDc4!1,4|N3fffd09c;!2'a<aFc;!2'b4g7c>!2'a<gHc;!2'^BaFc;!2'^BgHc;!2,`9+2gF!2'@3gF!1'aMgM!2'a;!2'a<gF'b:'b:!2'O,5gF!2'a<gFdN!2'^BgFdN!3,b5+2eNeL}6!2,`0+2gT!3,_\+2eB!3,_\+2eE_8!2+MgP!2'PgFfO!3+=4gNg2!3+=0Y#C!2+T!3+=0^0#C+^0!3+=0Y#D!3+=0^0#D!2+Tg\+^0!2'O:#W!2'O!2'^8#X#WI!2'@3#8!1'a:!3+=7!1#[h3^3!3+=+^L!3'`[#\#Zh3,Y!3'A+2+2Y!2'^8#W#V!3'C+2+2Y!2'^8#X#9!3+=+2#7h9!2'O,5#F!2,`9+2W!7,_M_C'_O+_P+_P,_Q!4,_R+2h<,`7_L,_U!2,`9+2X!2+M!2'OW#7!2'P#7X!2+M!2'O'aG#8!2'P#8'aH!2'^8#Y#:!3+=+2#8hA!2'P#H#^9!7,`:_C'_O+_P+_P,_Qh=!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;h>,_U!2'OW#1!2+MhE!2'P#1X!1'aMh3!1,4|D58000;!2'^8#Z#;!3+=+2#9hIvd!2,^3+2hIhJ!2'O`NhH!2'O,5#H!2'P#I#^:!2,`9+2hH!2'^8hH^J!2'OhP`[!3,`6+2hOa1$r;R0!2+T!2'OhP:!2'O;hH!2+T!2'OhPa9!2'Oa:hH!2+T!2'OhPa<!2'Oa=hH!2+T!2'OhPa?!2'Oa@hH!2+T!2'OhPaB!2'OaChH!2+T!2'OhPaE!2'OaFhH!2+T!2'OhPaH!2'OaIhH!2+T!2'OhPaK!2'OaLhH!2+T!2'OhPaN!2'OaOhH!2+T!2'OhPaQ!2'OaRhH!3'b0hH^J#1%x;R+2%~Ri0c3!3'b1#^4#2,5!1,4|O00023000;!2'^8#^2#@!3+=+2#>i4!2'b4hPc>!2'a<i6c;!2'a<hHc;!2'^BhHc;!2'^Bi6c;!2'O,5#[!2'P#^1#^O!2,`9+2i3!2'@3i3!1'aMi>!2'a;!2'a<i3'b:'b:!2'a;!2'a<#?'b:'b:!2'O,5i3!2'a<i3dN!2'^Bi3dN!2'^B#QdN}=!2,`0+2iF!2'O,5#;!2'@3#?!2'O,5#N!2'P#N#^?!2'O,5#P!2'P#Q#^B!2+MiB!2'Pi3fO!3+=4i?!1'aMiI!3+=0^0#E!3+=0^0#F!2'@3#:!1'a:!3+=7!1#^0iR^3!3+=+^L!3'`[#^1#\iR,Y!3'A+2+2^0!2'^8#Y#X!3'C+2+2^0!2,`9+2[!7,_M_C'_O+_P+_P,_Q!4,_R+2iX,`7_L,_U!2,`9+2\!2+M!2'O[#9!2'P#9\!2+M!2'O'aG#:!2'P#:'aH!7,`:_C'_O+_P+_P,_QiY!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;iZ,_U!2'O[#1!2+Mj1!2'P#1\!1'aMiR!1,4|D60040;!2'^8#\#=!3+=+2#;j5vd!2,^3+2j5j6!2'O`Nj4!2'O,5#J!2'P#K#^<!2,`9+2j4!2'^8j4^J!2'Oj<`[!3,`6+2j;a1$r;R0!2+T!2'Oj<:!2'O;j4!2+T!2'Oj<a9!2'Oa:j4!2+T!2'Oj<a<!2'Oa=j4!2+T!2'Oj<a?!2'Oa@j4!2+T!2'Oj<aB!2'OaCj4!2+T!2'Oj<aE!2'OaFj4!2+T!2'Oj<aH!2'OaIj4!2+T!2'Oj<aK!2'OaLj4!2+T!2'Oj<aN!2'OaOj4!2+T!2'Oj<aQ!2'OaRj4!3'b0j4^J#1%x;R+2%~RjIi2!1,4|O00024008;!2'b4j<c>!2'a<jLc;!2'a<j4c;!2'^Bj4c;!2'^BjLc;!2,`9+2jK!2'@3jK!1'aMjR!2'@3#B!2'a;!2'a<jK'b:'b:!2'a;!2'a<#A'b:'b:!2'^8#^5#C!3+=+2#AjWvd!2,^3+2jWjX!2'O,5jK!2'a<jKdN!2'^BjKdN!2'O,5#^3!2'O[#;!2'P#P#^A!2'O,5#R!2'P#S#^D!2+MjZ!2'PjKfO!3+=4jSg5!2'@3R!3+=0U#@!2+T!3+=0Y#@!2+T!3+=0^0#@+^0|51f;!1,4k:!2'_B^?k;!2'_G^?k;%~R^B%~R!2'O,5k;!2'P,5k<$Ha;R^E$~R+_H!3'_I^?k;#2%Ha;R^E%~R+_H!2'O,5k<!4,`3+2_>#2_@!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7!3,`8+2fX!1,9k:,_U!7,`:_C'_O+_P+_P,_QfWkB!2'^8#2#3!2+M_X!2'O!2'^8#3#4k<!2'^Z!2'`[#T#R#S!2'@3!2'^8#S#2!2'@3!2'^8#T#3!1'a:!3+=7!1#VkH^3!2'@3!2'^8#X#7$LB;R1$LK;R!1+;'`N$cr;R'`O$A;R1$M;R%~R47$model;R+^O$a;R+2$n;R+2$D;R!:+`P/ar;/HI;/sp0;/M0;#8#7#6#5#4#3$Hb;R!3+=+^L!2'aE#3#2,^6&HH;R!;'`R/ar;/HI;/sp0;/M0;#:#9#8#7#6#5#2!8'`S/HI;#:8#9#8#7#6!1'`T#5&Hb;R!3'_<9<#2!2+M!3+=+^L9,^6!3+=+^L<,^6!5'U=!3+=+^L!3'_70$w;R0!2'_=!2'_A:#7!2'_A!2'^8#7#6;'aD,^6!4'_C'?!2'^Z!2'`[#9#7#8#6#5$~R=$~R!3+=+^L!3'_70$w;R0!2'_=!2'_A:#8!2'_A!2'^8#8#7;'aD,^6!2$Hn;R!3+=+^L!2'_A,5#7,^6$Hb;R!3+=+^L!3'_70$w;R0!2'_=!2'_A:#:!2'_A!2'^8#:#9;'aD,^6&H;R?@&Hn;R!3#1,5#:#3A&H;R$A;R{g_7d;$f;RB$l;RC!5'UD%~R!2+_9#3$x;R#3!2+M!3'J#4#1#2!3+=+^L!1#3#1,^6!3+=+^L!3'_7#4#3#2,^6%~R!3+=+^L!3'_7#3#2#1,^6!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6$~RD$~R%~R!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6!3+=+^L!3'_7#5#4#3,^6#2!3'_:#3#2#1%A;R{g_7d;%f;RB%l;RCD&Hb;R!4#10$w;R0F'aD#4!2+_90$x;R0!2+MG!3+=+^LF,^6!5'_;0$x;R0!2+MG!3+=+^L!2'_=!2'_A:#?!2'_A!2'^8#?#>;,^6!4'_C'?!2'^Z!2'`[#A#?#@#>#=$x;R0$~R!1$x;R0!2+MG!3+=+^L!2'_=!2'_A:#@!2'_A!2'^8#@#?;,^6#1!2$w;R0$H;R!2+MG!3+=+^L!2'_=!2'_A:#A!2'_A!2'^8#A#@;,^6!5'UH!3+=+^L!2'_=!2'_A!3'A+2+2#2#B!2'_A!2'^8#B#AI,^6!4'_C'?!2'^Z!2'`[#E#C#D#B#A$~RH$~R!3+=+^L!2'_=!2'_A!3'A+2+2#3#C!2'_A!2'^8#C#B!3'C+2+2#3,^6!2$Hw;R!3'J0#4'aD$Hc;R!3+=+^L!2'_=!2'_A!3'A+2+2#5#E!2'_A!2'^8#E#D!3'C+2+2#5,^6&Hc;R!3'_<JK#1!2+M!3+=+^LJ,^6!3+=+^LK,^6!5'UL!3+=+^L!2'_A!2'^8#G#F!3'C+2+2#7,^6!4'_C'?!2'^Z!2'`[#J#H#I#G#F$~RL$~R!3+=+^L!2'_A!2'^8#H#G!3'C+2+2#8,^6!2$C1;R!3+=+^L!2'_A!3'A+2+2#9#I,^6$C2;R!3+=+^L!2'_A!2'^8#J#I!3'C+2+2#:,^6&H;R?@&C1;R!3#1M#L#3!2'OM#L&H;R?@&C2;R!3#1NO#4!2'ONO&CORE;R$i;R+2$Hi;RQ&x;RR+2!6'VV^2!2+M!1'a:!3+=7!1#T!2'@3#1^3!3+=+^L!3'`[#U#S!2'@3#1,Y$~RV!1$H;R!3+=0U#C!8'^10U$w;R0%C1;R^4%C2;R^5!2+M^7^8$C1;R!2'O^9#T$C2;R!2'O^:^;&Hx;Rvd&heq_x;Rvd!2,^3+2^<^=^=&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U^\!2'P#B#^3!2+M!2'OS!2'^8#^4#B!2'P!2'^8#^4#BT$~R^\$~R!2'P#C#^4!2$H4;R_0$H5;R_1&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_Q_M_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7_O,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;_O,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'OS#3%~R!2'O_YT%~R_[!2+M!2'OS_\!2'P_\T!:#1`0#^8^H#G#^9#2#3#B#A/Hsp;#2#1#A`1`1!4,[^7^8!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^08#\#[#Z#Y!1'`T#X#S#6!3,^2`2!2+M!2'O'aI#6!2'P#6'aJvd&heq_x;Rvd!2,^3+2`3`4`4&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`5!2'P#C#^4!2+M!2'O`7#A!2'P#A`8$~R`5$~R!2'P#D#^5!2$H4;R`9$H5;R`:&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q`<_H`>_U_V%__x1;R+2%~R`@`A!2#1#F#A#2#1#B`2vd!3'aK!2'aL`B!1'^T#X!1'aN!2'aO#Z`B&H;R`E`F!2#1!2'aO#[!1'aM!2'@3#7&s;R!2'aQ#7`G!2+aR!2'P#7`G!2'O`G#7-aRRN$s;R!2+aR`H`I!3+=+^L`J,^6#12$l;R`H!1$Hpg;R!2'P#9`G&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#W`L^J!6'^?+2`N$z;R+2!2'O#1`L&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S`T$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7`X,_U_U_V`T#1#2#1#F`Y`Z!6'^?+2`[$z;R+2!2'O`\#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sa0$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7a3,_U_U_Va0#1#2#1#Fa4a5a7!6'^?1'aX$l;R1!3+<0a8#1!6,aY0a8a;a\vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb0$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b1,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b2,`7`X,_U_U_Vb0#1#2#1#F!2+T!2'O`\b3!2'Ob4`L!6,aY0a8a>a[vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb5$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b6,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b7,`7`X,_U_U_Vb5#1#2#1#F!2+T!2'O`\b8!2'Ob9`L!6,aY0a8aAaZvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb:$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b<,`7`X,_U_U_Vb:#1#2#1#F!2+T!2'O`\b=!2'Ob>`L!6,aY0a8aDaYvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb?$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b@,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bA,`7`X,_U_U_Vb?#1#2#1#F!2+T!2'O`\bB!2'ObC`L!6,aY0a8aGaXvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbD$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bF,`7`X,_U_U_VbD#1#2#1#F!2+T!2'O`\bG!2'ObH`L!6,aY0a8aJaWvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbI$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bJ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bK,`7`X,_U_U_VbI#1#2#1#F!2+T!2'O`\bL!2'ObM`L!6,aY0a8aMaVvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbN$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bO,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bP,`7`X,_U_U_VbN#1#2#1#F!2+T!2'O`\bQ!2'ObR`L!6,aY0a8aPaUvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbS$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bT,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bU,`7`X,_U_U_VbS#1#2#1#F!2+T!2'O`\bV!2'ObW`L!6,aY0a8aSaTvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbX$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bY,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bZ,`7`X,_U_U_VbX#1#2#1#F!2+T!2'O`\b[!2'Ob\`L!2,aZ0a8c0c1!2+M%x;R+2%~Rc2c3!3'b2#^1`L^J!5'Uc5!3'b2#^2`L^J!3+=+^L!2'aO#^2!1'aM!2'@3#;,^6$~Rc5$~R!3'b2#^3`L^J!2$_H;R%x;R+2%~Rc2c6$SA;R!3'b2#^5`L^J&SA;R!2#1c7vdvd&heq_x;Rc:c9&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3`Lc;%~R!2'O,5`L%~Rc<!2'O,5c=&__sat4;R!2'b3c?c;%~R!2'O,5c?%~Rc<!2'O,5c@&__sat3;R^K^N&H;R!2'a9`Lc;%~RcB!3+=+2`L!2'^8!2'a;c;c=cC&H0;R!2'a=`Lc;%~RcD!2+M!2'O,5cC!2'PcCc;&H1;R!2'a>`Lc;%~RcE!2+M!2'Pc;cC!2'OcC,5&H2;R!2'a?`Lc;%~RcA!3+=+2c=,5&H3;R!2'a@`Lc;%~RcA!3+=+2cC`L&q;Rc=+2&r;RcC+2&H4;R!2'a9c?c;%~RcB!3+=+2c?!2'^8!2'a;c;c@cF&H5;R!2'a=c?c;%~RcD!2+M!2'O,5cF!2'PcFc;&H6;R!2'a>c?c;%~RcE!2+M!2'Pc;cF!2'OcF,5&H7;R!2'a?c?c;%~RcA!3+=+2c@,5&H8;R!2'a@c?c;%~RcA!3+=+2cFc?&q0;Rc@+2&r0;RcF+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcGcH!2+M!2'O!2'^8#@`7c7!2'Oc7!2'^8#9`7$~RcG$~R!2'P#^0#^N!2$H14;RcI$H15;RcJ&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;RcM_=&__varmap;RcO_B&__ff;R!8,`5_C'_O+_P+_P,_QcT_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2a2cV,_TcW,_U_H!8,`5_C'_O+_P+_P,_Qc\_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2`X,_Td0,_U_H!8,`5_C'_O+_P+_P,_Qd1_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2d2,`7d3,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2d3,`7d4,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rd5%~R%~Rd6!3+=+2c?d7%~Rd9%~R%~Rd6!3+=+2`Ld:%~Rd;!2+M!2'Od<c7!2'Oc7d=d?#2#1#[!2+M!2'O!2'^8c=`7c7!2'Oc7!2'^8c@`7!3'b0`L^Jc7!3+=+^L!2'aO#^6dA,^6&H;Rvd!6'^?+2c7dE!6'^?+2#@$z;R+2!3+=4!2'@3dFdB!8'b;+24dGdGdFdHdIvd&heq_x;RdLdK&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3c7dN%~RdO%~RdP!2'O,5dQ&__sat4;RdRdS&__sat3;R^K^N&H;R!2'a9c7dN%~RdU!3+=+2c7!2'^8!2'a;dNdQdV&H0;R!2'a=c7dN%~RdW!2+M!2'O,5dV!2'PdVdN&H1;R!2'a>c7dN%~RdX!2+M!2'PdNdV!2'OdV,5&H2;R!2'a?c7dN%~RdT!3+=+2dQ,5&H3;R!2'a@c7dN%~RdT!3+=+2dVc7&q;RdQ+2&r;RdV+2&H4;RdYd[&H5;Rd\e1&H6;Re2e4&H7;Re5e7&H8;Re8e:&q0;Re;+2&r0;Re<+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'Ue=e>!3+=+2!2'a;#@dN!2'a;#9dN$~Re=$~R!2'P#^1#^O!2$H14;Re?$H15;Re@&__arith;R$__p2;Rw$__p1;Rw$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<!3,_\+2eB!3,_\+2eE_3eM!3,0+_JeU_;_=&__varmap;ReY_B&__ff;R!8,`5_C'_O+_P+_P,_Qe\_H!8,`5_C'_O+_P+_P,_Qf2_H!8,`5_C'_O+_P+_P,_Qf3_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qf0_H!7,_M_C'_O+_P+_P,_Q!4,_R+2d3,_Tf4,_U_H!8,`5_C'_O+_P+_P,_Qf9_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2f1,`;f:,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Qf;f<_H!8,`5_C'_O+_P+_P,_Qf=_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7f6,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_Rf>_Hf?_U_V%__p2;Rw%__p1;Rw%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rf@%~RfC%~RfD%~R%~RfA!3+=+2c7fF%~RfG%~R!2'P#;`G%~R!2+MfH#?%~R!2'O,5#<%~RfH%~R!2+M!2'O_P#<#C!3+=+2fIfJ!D#1`0!2'P#^3T#=#D#^3#^5#^T^H#>#E#B#C#I#J#P#W#[#3#^0/Hsp;#2#1#\!3+=+2dFdHfLg0!2'^;3d@!2'_Zc7&heq_x;RdLdK&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UfSfTg1$~RfS$~R!2'P#P#^A!2$H4;RfU$H5;RfV&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7d3,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2d3,`;fY,_U_U_Vg1#1#2#1#Ng3g3!6'^14dAg4#2g5#1#2#1#1#1$l;R`I!1$Hpg;R!2'O`G#9&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#WaF^J!6'^?+2`N$z;R+2!2'O#1aF&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg6$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7bF,_U_U_Vg6#1#2#1#F`Y`Z!6'^?+2`[$z;R+2!2'Og7#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg8$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7a3,_U_U_Vg8#1#2#1#Fa4a5a7!6'^?1'aX$l;R1!3+<0g:#1!6,aY0g:a;a\vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg;$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7b1,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b2,`7bF,_U_U_Vg;#1#2#1#F!2+T!2'Og7b3!2'Ob4aF!6,aY0g:a>a[vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg<$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7b6,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b7,`7bF,_U_U_Vg<#1#2#1#F!2+T!2'Og7b8!2'Ob9aF!6,aY0g:aAaZvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg=$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7b;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b<,`7bF,_U_U_Vg=#1#2#1#F!2+T!2'Og7b=!2'Ob>aF!6,aY0g:aDaYvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg>$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7b@,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bA,`7bF,_U_U_Vg>#1#2#1#F!2+T!2'Og7bB!2'ObCaF!6,aY0g:aGaXvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg?$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7bE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bF,`7bF,_U_U_Vg?#1#2#1#F!2+T!2'Og7bG!2'ObHaF!6,aY0g:aJaWvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sg@$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7bJ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bK,`7bF,_U_U_Vg@#1#2#1#F!2+T!2'Og7bL!2'ObMaF!6,aY0g:aMaVvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgA$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7bO,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bP,`7bF,_U_U_VgA#1#2#1#F!2+T!2'Og7bQ!2'ObRaF!6,aY0g:aPaUvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgB$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7bT,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bU,`7bF,_U_U_VgB#1#2#1#F!2+T!2'Og7bV!2'ObWaF!6,aY0g:aSaTvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgC$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2g9,`7bY,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bZ,`7bF,_U_U_VgC#1#2#1#F!2+T!2'Og7b[!2'Ob\aF!2,aZ0g:c0c1!2+M%x;R+2%~RgDc3!3'b2#^1aF^J!5'UgE!3'b2#^2aF^J!3+=+^L!2'aO#^2!1'aM!2'@3#;,^6$~RgE$~R!3'b2#^3aF^J!2$_H;R%x;R+2%~RgDc6$SA;R!3'b2#^5aF^J&SA;R!2#1gFvdvd&heq_x;Rc:c9&__sat7;R!2'b3aFc;%~R!2'O,5aF%~Rc<!2'O,5gG&__sat6;R^A^D&__sat5;R^F^G&__sat4;R!2'b3gHc;%~R!2'O,5gH%~Rc<!2'O,5gI&__sat3;R^K^N&H;R!2'a9aFc;%~RcB!3+=+2aF!2'^8!2'a;c;gGgJ&H0;R!2'a=aFc;%~RcD!2+M!2'O,5gJ!2'PgJc;&H1;R!2'a>aFc;%~RcE!2+M!2'Pc;gJ!2'OgJ,5&H2;R!2'a?aFc;%~RcA!3+=+2gG,5&H3;R!2'a@aFc;%~RcA!3+=+2gJaF&q;RgG+2&r;RgJ+2&H4;R!2'a9gHc;%~RcB!3+=+2gH!2'^8!2'a;c;gIgK&H5;R!2'a=gHc;%~RcD!2+M!2'O,5gK!2'PgKc;&H6;R!2'a>gHc;%~RcE!2+M!2'Pc;gK!2'OgK,5&H7;R!2'a?gHc;%~RcA!3+=+2gI,5&H8;R!2'a@gHc;%~RcA!3+=+2gKgH&q0;RgI+2&r0;RgK+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcGcH!2+M!2'O!2'^8#@`7gF!2'OgF!2'^8#9`7$~RcG$~R!2'P#^0#^N!2$H14;RcI$H15;RcJ&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;RcM_=&__varmap;RcO_B&__ff;R!8,`5_C'_O+_P+_P,_QcT_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2g9cV,_TcW,_U_H!8,`5_C'_O+_P+_P,_Qc\_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2bF,_Td0,_U_H!8,`5_C'_O+_P+_P,_Qd1_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2d2,`7gL,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2gL,`7d4,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rd5%~R%~Rd6!3+=+2gHd7%~Rd9%~R%~Rd6!3+=+2aFd:%~Rd;!2+M!2'Od<gF!2'OgFd=d?#2#1#[!2+M!2'O!2'^8gG`7gF!2'OgF!2'^8gI`7!3'b0aF^JgF!3+=+^L!2'aO#^6gN,^6&H;Rvd!6'^?+2gFdE!6'^?+2#@$z;R+2!3+=4!2'@3gOdB!8'b;+24dGdGgOdHdIvd&heq_x;RdLdK&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3gFdN%~RgP%~RdP!2'O,5gQ&__sat4;RdRdS&__sat3;R^K^N&H;R!2'a9gFdN%~RdU!3+=+2gF!2'^8!2'a;dNgQgR&H0;R!2'a=gFdN%~RdW!2+M!2'O,5gR!2'PgRdN&H1;R!2'a>gFdN%~RdX!2+M!2'PdNgR!2'OgR,5&H2;R!2'a?gFdN%~RdT!3+=+2gQ,5&H3;R!2'a@gFdN%~RdT!3+=+2gRgF&q;RgQ+2&r;RgR+2&H4;RdYd[&H5;Rd\e1&H6;Re2e4&H7;Re5e7&H8;Re8e:&q0;Re;+2&r0;Re<+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'Ue=e>!3+=+2!2'a;#@dN!2'a;#9dN$~Re=$~R!2'P#^1#^O!2$H14;Re?$H15;Re@&__arith;R$__p1;Rw$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<!3,_\+2eT!3,`F+2cL_3!2,b<eL!2,_[!3,_\+2gS!3,_\+2eO!3,_\+2eQ!3,_\+2eDgU,`2!3,0+_J!2,b<!3,_\+2gU_3!2,b<eL!2,_[!3,_\+2gS!3,_\+2eOgV,`2_;_=&__varmap;R!4,`3+2!4,`3+2!4,`3+2_?#7_@#3!4,`3+2eV#7_@#2!4,`3+2!4,`3+2cN#7_@#4_@_B&__ff;R!8,`5_C'_O+_P+_P,_Qe\_H!8,`5_C'_O+_P+_P,_Qf2_H!8,`5_C'_O+_P+_P,_Qf3_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qf0_H!7,_M_C'_O+_P+_P,_Q!4,_R+2gL,_Tf4,_U_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2f:,`7f1,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Qf;!7,_M_C'_O+_P+_P,_Q!4,_R+2f1,`;_O,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_Rc[_Hf?_U_V%__p1;Rw%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R%~RdW!2+Md8!2'P#7dN%~R%~RfA!3+=+2#6!2'^8fB#8%~R%~RdW!2+M!2'O,5#8!2'P#8dN%~R%~RfA!3+=+2gF!2'^8fE#9%~R`I%~R!2+M!2'OS#9!2'P#9T%~R!2+M!2'O_P#9#=!3+=+2!2'a;#8dN!2'a;#9dN!>#1`0#=#D#^3^H#>#E#B#C#I#J#W#[/Hsp;#2#1#\!3+=+2gOdHfLg0!2'^;3gM!2'_ZgF&heq_x;RdLdK&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UfSfTgW$~RfS$~R!2'P#P#^A!2$H4;RfU$H5;RfV&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7gL,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2gL,`;fY,_U_U_VgW#1#2#1#NgXgX!6'^14gNg4#2g5#1#2#1#1#1^8#D#1#8#6#1$~R^2!1$Hw;R!2+TgYgZ!6'Vg[h0!2+M!1'a:!3+=7!1#V!2'@3#3^3!3+=+^L!3'`[#W#U!2'@3#3,Y$~Rg[!1$H;R!3+=0Y#E!8'^10Y$w;R0%C1;Rh1%C2;Rh2!2+Mh4h5$C1;R!2'Oh6#V$C2;R!2'Oh7h8&Hx;Rvd&heq_x;Rvd!2,^3+2h9h:h:&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U_0!2'P#D#^5!2+M!2'OW!2'^8#^6#D!2'P!2'^8#^6#DX$~R_0$~R!2'P#E#^6!2$H4;Rh;$H5;R`S&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_Qh=_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7h>,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2h<,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;h>,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'OW#3%~R!2'O_YX%~R_[!2+M!2'OW_\!2'P_\X!:#1`0#^:^H#I#^;#2#3#B#A/Hsp;#2#1#Ch?h?!4,[h4h5!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^28#^1#^0#\#[!1'`T#Z#U#8!3,^2h@!2+M!2'O'aI#8!2'P#8'aJvd&heq_x;Rvd!2,^3+2hAhBhB&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`9_1!2+M!2'O`7#C!2'P#C`8$~R`9$~R!2'P#F#^7!2$H4;R`R$H5;RhC&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QhD_H`>_U_V%__x1;R+2%~RhF`A!2#1#H#A#2#1#Dh@vd!3'aK!2'aLhG!1'^T#Z!1'aN!2'aO#\hG&H;R`E`F!2#1`J&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^38#^2#^1#^0#\!1'`T#[#VhH^J!6'^?+2`N$z;R+2!2'O#1hH&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hL$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7hO,_U_U_VhL#1#2#1#E`Y`Z!6'^?+2`[$z;R+2!2'OhP#1&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hQ$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7a3,_U_U_VhQ#1#2#1#Ea4a5&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:^T$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhNa6#2#1#E!6'^?1'aX$l;R1!3+<0hS#1!6,aY0hSa;a\vd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hT$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7b1,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b2,`7hO,_U_U_VhT#1#2#1#E!2+T!2'OhPb3!2'Ob4hH!6,aY0hSa>a[vd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hU$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7b6,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b7,`7hO,_U_U_VhU#1#2#1#E!2+T!2'OhPb8!2'Ob9hH!6,aY0hSaAaZvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hV$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7b;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b<,`7hO,_U_U_VhV#1#2#1#E!2+T!2'OhPb=!2'Ob>hH!6,aY0hSaDaYvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hW$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7b@,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bA,`7hO,_U_U_VhW#1#2#1#E!2+T!2'OhPbB!2'ObChH!6,aY0hSaGaXvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hX$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7bE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bF,`7hO,_U_U_VhX#1#2#1#E!2+T!2'OhPbG!2'ObHhH!6,aY0hSaJaWvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hY$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7bJ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bK,`7hO,_U_U_VhY#1#2#1#E!2+T!2'OhPbL!2'ObMhH!6,aY0hSaMaVvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:hZ$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7bO,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bP,`7hO,_U_U_VhZ#1#2#1#E!2+T!2'OhPbQ!2'ObRhH!6,aY0hSaPaUvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:h[$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7bT,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bU,`7hO,_U_U_Vh[#1#2#1#E!2+T!2'OhPbV!2'ObWhH!6,aY0hSaSaTvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:h\$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hR,`7bY,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bZ,`7hO,_U_U_Vh\#1#2#1#E!2+T!2'OhPb[!2'Ob\hH!2,aZ0hSc0c1!2+M%x;R+2%~Ri0!3'b1#^1#2,5!3'b2#^0hH^J!5'Ui1!3'b2#^1hH^J!3+=+^L!2'aO#^1!1'aM!2'@3#:,^6$~Ri1$~R!3'b2#^2hH^J!2$_H;R%x;R+2%~Ri0i2$SA;R!3'b2#^4hH^J&SA;R!2#1i3vdvd&heq_x;Rvd!2,^3+2i4i5i5&__sat7;R!2'b3i6c;%~R!2'O,5i6%~Rc<!2'O,5i7&__sat6;R^A^D&__sat5;R^F^G&__sat4;R^K^N&__sat3;R!2'b3hHc;%~R!2'O,5hH%~Rc<!2'O,5i8&H;R!2'a9hHc;%~RcB!3+=+2hH!2'^8!2'a;c;i8i9&H0;R!2'a=hHc;%~RcD!2+M!2'O,5i9!2'Pi9c;&H1;R!2'a>hHc;%~RcE!2+M!2'Pc;i9!2'Oi9,5&H2;R!2'a?hHc;%~RcA!3+=+2i8,5&H3;R!2'a@hHc;%~RcA!3+=+2i9hH&q;Ri8+2&r;Ri9+2&H4;R!2'a9i6c;%~RcB!3+=+2i6!2'^8!2'a;c;i7i:&H5;R!2'a=i6c;%~RcD!2+M!2'O,5i:!2'Pi:c;&H6;R!2'a>i6c;%~RcE!2+M!2'Pc;i:!2'Oi:,5&H7;R!2'a?i6c;%~RcA!3+=+2i7,5&H8;R!2'a@i6c;%~RcA!3+=+2i:i6&q0;Ri7+2&r0;Ri:+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'Ui;!2'P#[#^L!2+M!2'O!2'^8#@`7i3!2'Oi3!2'^8#9`7$~Ri;$~R!2'P#\#^M!2$H14;Re=$H15;Ri<&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;RcM_=&__varmap;RcO_B&__ff;R!8,`5_C'_O+_P+_P,_QcT_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2hRcV,_TcW,_U_H!8,`5_C'_O+_P+_P,_Qc\_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2hO,_Td0,_U_H!8,`5_C'_O+_P+_P,_Qd1_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2d2,`7i=,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2i=,`7d4,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rd5%~R%~Rd6!3+=+2i6d7%~Rd9%~R%~Rd6!3+=+2hHd:%~Rd;!2+M!2'Od<i3!2'Oi3d=d?#2#1#Z!2+M!2'O!2'^8i8`7i3!2'Oi3!2'^8i7`7!3'b0hH^Ji3!3+=+^L!2'aO#^5i?,^6&H;Rvd!6'^?+2i3$z;R+2!3+=4dB!2'@3!2'a;!2'a<fL'b:'b:!6'^?+2#?$z;R+2!3+=4!2'@3i@dB!8'b;+24dGdGi@iAdIvd&heq_x;Rc:c9&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3#BdN%~R^\%~RdP!2'O,5!2'a<#DdN&__sat4;R!2'b3i3dN%~RiB%~RdP!2'O,5iC&__sat3;R^K^N&H;R!2'a9i3dN%~RdU!3+=+2i3!2'^8!2'a;dNiCiD&H0;R!2'a=i3dN%~RdW!2+M!2'O,5iD!2'PiDdN&H1;R!2'a>i3dN%~RdX!2+M!2'PdNiD!2'OiD,5&H2;R!2'a?i3dN%~RdT!3+=+2iC,5&H3;R!2'a@i3dN%~RdT!3+=+2iDi3&q;RiC+2&r;RiD+2&H4;R!2'a9#LdN%~RdU!3+=+2#M!2'^8!2'a;dN!2'a<#MdN!2'^B#MdN&H5;R!2'a=#MdN%~RdW!2+M!2'O,5dZ!2'PdZdN&H6;R!2'a>#NdN%~RdX!2+M!2'PdNe0!2'Oe0,5&H7;R!2'a?#OdN%~RdT!3+=+2!2'a<#PdN,5&H8;R!2'a@#PdN%~RdT!3+=+2iE#Q&q0;Re6+2&r0;Re9+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcGcH!3+=+2!2'a;#@dN!2'a;#9dN$~RcG$~R!2'P#^0#^N!2$H14;RcI$H15;RcJ&__arith;R$__p2;Rw$__p1;Rw$__x9;R+2$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<_6!2,_[!3,_\+2eO!3,_\+2iG!3,_\+2eB!3,_\+2eQ!3,_\+2!3,`F+2cLeG!3,_\+2eR!3,_\+2_3_8,`2!3,0+_J!2,b<eJ!2,b<eL!2,_[!3,_\+2gS!3,_\+2eO!3,_\+2!2,`0+2}?!3,_\+2!3,`F+2cLiG!3,_\+2eG!3,_\+2eT_8,`2_;_=&__varmap;R!4,`3+2!4,`3+2!4,`3+2eX#:_@#3!4,`3+2!2,_K+2#:#6_@#2!4,`3+2eW#4eV_B&__ff;R!8,`5_C'_O+_P+_P,_Qe\_H!8,`5_C'_O+_P+_P,_Qf2_H!8,`5_C'_O+_P+_P,_Qf3_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qf0_H!7,_M_C'_O+_P+_P,_Q!4,_R+2i=,_Tf4,_U_H!8,`5_C'_O+_P+_P,_Qf9_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2h<,`7f1,_Uf>_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2f8,`;_F,_U_H!8,`5_C'_O+_P+_P,_Qf=_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2h<,`7f6,_U_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,`6+2f6_F,`7h>,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#=_Hf?_U_V%__p2;Rw%__p1;Rw%__x9;R+2%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RfD%~R%~RfA!3+=+2#9!2'^8fB#;%~R%~RdW!2+MiH!2'P#;dN%~R%~RfA!3+=+2i3!2'^8fE#<%~R!3+=+2#;!2'^8#9#:%~R!2+M!2'OW#<#?%~R!2'P#<#:%~Rd>%~R!2'OW#=%~R!2'OEX%~R!2+M!2'O_P#=#E!3+=+2fJ!2'a;#=dN!F#1`0!2'P#^2X#=#D#^2#^4#^S#^R^H#>#E#B#C#I#J#P#X#2#3#Z#Y/Hsp;#2#1#[!3+=+2i@iA!2'^;3iI!2'_Z#?&heq_x;Rc:c9&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UiJiK!2+M!2'O,5#L!2'P#LfO$~RiJ$~R!2'P#O#^@!2$H4;RiL$H5;RiM&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QhD_HfZ_U_V%__x1;R+2%~RhFf\!2#1#Q#J#2#1#M!2'^;3i>!2'_Zi3&heq_x;Rc:c9&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UiJiKiN$~RiJ$~R!2'P#O#^@!2$H4;RiL$H5;RiM&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7i=,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2i=,`;fY,_U_U_ViN#1#2#1#MiOiO!6'^14i?$b;R4!3+=+^L!2'aO#^8#1,^6#2g2#1#2#1#1h5#F#1#:#8#1$~Rh0!1$Hw;R!2+TiP+^0!6'ViQ+^0!2+M!1'a:!3+=7!1#X!2'@3#5^3!3+=+^L!3'`[#Y#W!2'@3#5,Y$~RiQ!1$H;R!3+=0^0#G!8'^10^0$w;R0%C1;R!2'O:#Y%C2;R!2'O!2'^8#Z#YI!2+MiSiT$C1;R!2'OiU#X$C2;R!2'OiViW&Hx;Rvd&heq_x;RhKhJ&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uh;`:!2+M!2'O[!2'^8#^8#F!2'P!2'^8#^8#F\$~Rh;$~R!2'P#G#^8!2$H4;RhM$H5;RhN&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_QiY_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7iZ,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2iX,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;iZ,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'O[#3%~R!2'O_Y\%~R_[!2+M!2'O[_\!2'P_\\!:#1`0#^<^H#K#^=#2#3#B#A/Hsp;#2#1#Ei[i[!4,[iSiT!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#W#:!3,^2i\!2+M!2'O'aI#:!2'P#:'aJvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S!2+M!2'O`7#E!2'P#E`8$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Qj0_H`>_U_V%__x1;R+2%~Rj2`A!2#1#J#A#2#1#Fi\vd!3'aK!2'aLj3!1'^T#\!1'aN!2'aO#^1j3&H;R`E`F!2#1!2'aO#^2!1'aM!2'@3#;&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^58#^4#^3#^2#^1!1'`T#^0#Xj4^J!6'^?+2`N$z;R+2!2'O#1j4&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCj8$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7j;,_U_U_Vj8#1#2#1#G`Y`Z!6'^?+2`[$z;R+2!2'Oj<#1&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCj=$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7a3,_U_U_Vj=#1#2#1#Ga4a5&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhC^T$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:a6#2#1#G!6'^?1'aX$l;R1!3+<0j?#1!6,aY0j?a;a\vd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCj@$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7b1,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b2,`7j;,_U_U_Vj@#1#2#1#G!2+T!2'Oj<b3!2'Ob4j4!6,aY0j?a>a[vd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjA$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7b6,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b7,`7j;,_U_U_VjA#1#2#1#G!2+T!2'Oj<b8!2'Ob9j4!6,aY0j?aAaZvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjB$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7b;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b<,`7j;,_U_U_VjB#1#2#1#G!2+T!2'Oj<b=!2'Ob>j4!6,aY0j?aDaYvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjC$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7b@,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bA,`7j;,_U_U_VjC#1#2#1#G!2+T!2'Oj<bB!2'ObCj4!6,aY0j?aGaXvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjD$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7bE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bF,`7j;,_U_U_VjD#1#2#1#G!2+T!2'Oj<bG!2'ObHj4!6,aY0j?aJaWvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjE$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7bJ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bK,`7j;,_U_U_VjE#1#2#1#G!2+T!2'Oj<bL!2'ObMj4!6,aY0j?aMaVvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjF$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7bO,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bP,`7j;,_U_U_VjF#1#2#1#G!2+T!2'Oj<bQ!2'ObRj4!6,aY0j?aPaUvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjG$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7bT,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bU,`7j;,_U_U_VjG#1#2#1#G!2+T!2'Oj<bV!2'ObWj4!6,aY0j?aSaTvd&heq_x;Rj7j6&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhMhCjH$~RhM$~R!2'P#I#^:!2$H4;Rj9$H5;Rj:&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j>,`7bY,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bZ,`7j;,_U_U_VjH#1#2#1#G!2+T!2'Oj<b[!2'Ob\j4!2,aZ0j?c0c1!2+M%x;R+2%~RjIc4!3'b2#^2j4^J!5'UjJ!3'b2#^3j4^J!3+=+^L!2'aO#^3!1'aM!2'@3#<,^6$~RjJ$~R!3'b2#^4j4^J!2$_H;R%x;R+2%~RjI!3'b1#^6#2,5$SA;R!3'b2#^6j4^J&SA;R!2#1jKvdvd&heq_x;RdLdK&__sat7;R!2'b3jLc;%~R!2'O,5jL%~Rc<!2'O,5jM&__sat6;R^A^D&__sat5;R^F^G&__sat4;R^K^N&__sat3;R!2'b3j4c;%~R!2'O,5j4%~Rc<!2'O,5jN&H;R!2'a9j4c;%~RcB!3+=+2j4!2'^8!2'a;c;jNjO&H0;R!2'a=j4c;%~RcD!2+M!2'O,5jO!2'PjOc;&H1;R!2'a>j4c;%~RcE!2+M!2'Pc;jO!2'OjO,5&H2;R!2'a?j4c;%~RcA!3+=+2jN,5&H3;R!2'a@j4c;%~RcA!3+=+2jOj4&q;RjN+2&r;RjO+2&H4;R!2'a9jLc;%~RcB!3+=+2jL!2'^8!2'a;c;jMjP&H5;R!2'a=jLc;%~RcD!2+M!2'O,5jP!2'PjPc;&H6;R!2'a>jLc;%~RcE!2+M!2'Pc;jP!2'OjP,5&H7;R!2'a?jLc;%~RcA!3+=+2jM,5&H8;R!2'a@jLc;%~RcA!3+=+2jPjL&q0;RjM+2&r0;RjP+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'Ue=e>!2+M!2'O!2'^8#@`7jK!2'OjK!2'^8#9`7$~Re=$~R!2'P#^1#^O!2$H14;Re?$H15;Re@&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;RcM_=&__varmap;RcO_B&__ff;R!8,`5_C'_O+_P+_P,_QcT_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2j>cV,_TcW,_U_H!8,`5_C'_O+_P+_P,_Qc\_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QcU_H!7,_M_C'_O+_P+_P,_Q!4,_R+2j;,_Td0,_U_H!8,`5_C'_O+_P+_P,_Qd1_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2d2,`7jQ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2jQ,`7d4,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rd5%~R%~Rd6!3+=+2jLd7%~Rd9%~R%~Rd6!3+=+2j4d:%~Rd;!2+M!2'Od<jK!2'OjKd=d?#2#1#\!2+M!2'O!2'^8jN`7jK!2'OjK!2'^8jM`7!3'b0j4^JjK!3+=+^L!2'aO#^7jS,^6&H;Rvd!6'^?+2jK$z;R+2!3+=4dB!2'@3!2'a;!2'a<!2'^;3jT'b:'b:!6'^?+2#A$z;R+2!3+=4!2'@3jUdB!8'b;+24dGdGjUjVdIvd&heq_x;RjYjX&__sat7;R^A^D&__sat6;R^F^G&__sat5;RdRdS&__sat4;R!2'b3jKdN%~RjZ%~RdP!2'O,5j[&__sat3;R^K^N&H;R!2'a9jKdN%~RdU!3+=+2jK!2'^8!2'a;dNj[j\&H0;R!2'a=jKdN%~RdW!2+M!2'O,5j\!2'Pj\dN&H1;R!2'a>jKdN%~RdX!2+M!2'PdNj\!2'Oj\,5&H2;R!2'a?jKdN%~RdT!3+=+2j[,5&H3;R!2'a@jKdN%~RdT!3+=+2j\jK&q;Rj[+2&r;Rj\+2&H4;R!2'a9#NdN%~RdU!3+=+2#O!2'^8!2'a;dN!2'a<#OdNe0&H5;R!2'a=#OdN%~RdW!2+M!2'O,5e3!2'Pe3dN&H6;R!2'a>#PdN%~RdX!2+M!2'PdNiE!2'OiE,5&H7;R!2'a?#QdN%~RdT!3+=+2e;,5&H8;R!2'a@#RdN%~RdT!3+=+2e<#S&q0;R!2'a<#SdN+2&r0;R!2'^B#TdN+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcIi<!3+=+2!2'a;#@dN!2'a;#9dN$~RcI$~R!2'P#^2#^P!2$H14;Rk0$H15;R!2'P#^4#^R&__arith;R$__p1;Rw$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_JeU!3,0+_J!2,b<gVeM_;_=&__varmap;ReY_B&__ff;R!8,`5_C'_O+_P+_P,_Qe\_H!8,`5_C'_O+_P+_P,_Qf2_H!8,`5_C'_O+_P+_P,_Qf3_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qf0_H!7,_M_C'_O+_P+_P,_Q!4,_R+2jQ,_Tf4,_U_H!8,`5_C'_O+_P+_P,_Qf9_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2iX,`7f1,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2f1,`;iZ,_U_H!8,`5_C'_O+_P+_P,_Qf=_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2iX,`7f6,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_Rf<_Hf?_U_V%__p1;Rw%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~Rf@%~RfC%~RfD%~R%~RfA!3+=+2jKfF%~RfG%~R!2+Mk1!2'P#;\%~RiH%~Rk1%~R!2+M!2'O_P#;#A!3+=+2!2'a;#:dNfI!B#1`0#=#D#^4#^6#^U^H#>#E#B#C#I#J#P#X#3#Z/Hsp;#2#1#^0!3+=+2jUjVdD!2'_Z#A&heq_x;RjYjX&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UiLk2!2+M!2'O,5#N!2'P#NfO$~RiL$~R!2'P#Q#^B!2$H4;Rk3$H5;Rk4&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Qj0_HfZ_U_V%__x1;R+2%~Rj2f\!2#1#S#J#2#1#O!2'^;3jR!2'_ZjK&heq_x;RjYjX&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UiLk2k5$~RiL$~R!2'P#Q#^B!2$H4;Rk3$H5;Rk4&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7jQ,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2jQ,`;fY,_U_U_Vk5#1#2#1#Ok6k6!6'^14jS$b;R4!3+=+^L!2'aO#^:#1,^6#2!1'aMjT#1#2#1#1iT#H#1#<#:#1$~R+^0!1$Hw;R+^0!2'^5!2+M!1'a:!3+=7!1#Z!2'@3#7^3!3+=+^L!3'`[#[#Y!2'@3#7,Y#1#1#1#1#1#1#>%i;R+2%~RQ!2+M!1'a:!3+=7!1#Sk7^3!3+=+^L!3'`[#T#Rk7,Y&A0;R!6'Vk8k9!2+M!2'O,5#P!2'O!2'^8#P#Ok<$~Rk8!1$H;R!3+=0U#A!8'^10U$w;R0%C1;R!2'O:#S%C2;R!2'O!2'^8#T#SI!2+M!2'O,5#U!2'O^:k<$C1;R!2'O^9#R$C2;R!2'O!2'^8#S#R^;&__sat7;Rk=k>&__sat6;Rk?k@&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkA_B&__ff;R!8,`5_C'_O+_P+_P,_Q_M_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7_O,_U_HkC_U_V%__x2;R+2%__x1;R+2%~R`?%~R!2'OkDTkE!4#1#^3#^4#?#>#B#1#6#4#1$~Rk9!1$Hw;R!2+T!3+=0Y#A!2+T!3+=0^0#A+^0!6'VZ^1!2+M!2'O,5#R!2'O!2'^8#R#Qk<$~RZ!1$H;RgY!8'^10Y$w;R0%C1;R^4%C2;R^5!2+M!2'O,5#W!2'Oh7k<$C1;R!2'Oh6#T$C2;R!2'O^:h8&__sat7;Rk=k>&__sat6;Rk?k@&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkA_B&__ff;R!8,`5_C'_O+_P+_P,_Qh=_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7h>,_U_HkC_U_V%__x2;R+2%__x1;R+2%~RhE%~R!2'OkDXkE!4#1#^5#^6#?#>#D#1#8#6#1$~R^1!1$Hw;RgZ!6'Vg\+^0!2+M!2'O,5#T!2'O!2'^8#T#Sk<$~Rg\!1$H;RiP!8'^10^0$w;R0%C1;Rh1%C2;Rh2!2+M!2'O,5#Y!2'OiVk<$C1;R!2'OiU#V$C2;R!2'Oh7iW&__sat7;Rk=k>&__sat6;Rk?k@&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkA_B&__ff;R!8,`5_C'_O+_P+_P,_QiY_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7iZ,_U_HkC_U_V%__x2;R+2%__x1;R+2%~Rj1%~R!2'OkD\kE!4#1#^7#^8#?#>#F#1#:#8#1$~R+^0!1$Hw;R+^0!2'^5!2+M!2'O,5#V!2'O!2'^8#V#Uk<#1#1#1#1#1#1#<!2+MiL!2'O!2'^8#P#Ok<!7'b='?kF#Q#Pvd$i;R+2$Hi;R!2+MP!2'P#1#Q&a0;R!2#4#2#1!2+M!1'a:!3+=7!1#UkG^3!3+=+^L!3'`[#V#TkG,Y!5'UkI!3+=+^L!3'`[#W#UkH,Y!1'a:!3+=7!3'^Z!2'`[#W#U#V!2'@3!2'^8#T#3^3$~RkI$~R!3+=+^L!3'`[#X#V!2'@3!2'^8#U#4,Y!2$DEF;R!1'a:!3+=7!1#X!2'@3!2'^8#V#5^3$VIS;R!3+=+^L!3'`[#Z#X!2'@3!2'^8#W#6,Yvd!6'^?+^L,Y$b;R+^L!1'a:!3+=7-^LRN$~R+^L7#12^3!1#[!2'@3!2'^8#Y#8^3#2!3'`[#[#YkJ#1!1'a:!3+=7!3'^Z!2'`[#[#Y#ZkJ^3#2#1#1!3'b>kF#Q#P&__sat7;Rk=k>&__sat6;Rk?k@&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__p1;Rw$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_QfW!6,`J_C'_O+_P+_P,_Q#4_HfW_U_V%__p1;Rw%__x1;R+2%~R!2+MP#2f[!3#1!2'O!2'^8#^1#^0k<#^1#>&__sat9;Rk=k>&__sat8;Rk?k@&__sat7;R^A^D&__sat6;R^F^G&__sat5;RfNfP&__sat4;RfQfR&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__p1;Rw$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkA_B&__ff;R!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!6,`J_C'_O+_P+_P,_Q#5kB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7fY,_U_U_V%__p1;Rw%__x2;R+2%__x1;R+2%~R!2+M#3!2'O!2'^8#1#2k<!2'OkDfO!4#1k0#^2#^3#@#2#1#1#2#1#1#2#1#1#2#1#1").
Qed.

  (* [comment removed for export] *)
  Lemma wsg_writable : forall (MV : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
    L5Defs.L5.writable ASEGS MV a (Z.of_nat n).
  Proof.
    intros MV a n W Ha Hn d k Hd Hk.
    apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) n k a (a + Z.of_nat n)); first [exact W | reflexivity | lia | rewrite u64_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Definition exit_pre (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    (* WINDOW, old beside new, here and in every exit_pre* / WIN1 / WIN3 below: was
       [usp - 8388608 <= a]; the zero-filled window is [DRV_ZWIN] = 6144513 at LPS 75d69e00
       (Pm4DrvEntry).  The frames below sp that these feed are a few KiB. *)
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1449984 -> MV (Z_to_bv 64 i) = None)
    /\ exitA tid MV.
  Definition exit_preT (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1449984 -> MV (Z_to_bv 64 i) = None)
    /\ exitT tid MV.
  Definition exit_preL (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1449984 -> MV (Z_to_bv 64 i) = None)
    /\ exitL tid MV.

  Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_T = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX.dpX_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x141724) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x141724) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 1463748) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 1463648) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1463664) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1463616) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1463624) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
    pose proof Hsp as Hsp'. destruct SOP as (SOlock & SOwpos & SOwbase & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXe.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXe:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x141724) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x141724) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_T = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX2_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 1) 0 0 (zero_lines 1%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX3_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_T = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX3_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 2) 0 0 (zero_lines 2%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX4_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_T = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_T i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_T i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_T i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX4_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 3) 0 0 (zero_lines 3%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_0L : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXL.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_L = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_L i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_L i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_L i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXL.dpXL_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x141724) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x141724) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXL.KS_dpXL; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_2L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXL2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_L = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_L i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_L i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_L i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL2_pre.dpXL2_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL2_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 1) 0 0 (zero_lines 1%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_3L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXL3_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_L = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_L i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_L i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_L i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL3_pre.dpXL3_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL3_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 2) 0 0 (zero_lines 2%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_4L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1315408 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6938576 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x141a14) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXL4_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, shchk a n = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (EXB : forall a n v, existsb (cell_eqb (a, n, v)) EX_CELLS = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (ex_cell_vis _ _ _ _ _ _ a n v D (cell_in_b _ _ Hb))).
    assert (XCB : forall a n v, existsb (cell_eqb (a, n, v)) XC_CELLS_L = true -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros a n v Hb; exact (cells_at_in MV _ a n v XC (cell_in_b _ _ Hb))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_L i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_L i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_L i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x165740 <=? a) && (a + Z.of_nat n <=? 0x166840) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL4_pre.dpXL4_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL4_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1468480 \/ 1472440 <= i < 7069728 \/ 7069752 <= i < 7070272 \/ 7070276 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x141a14) M R1 (Z_to_bv 64 0x1493f8) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7071728) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 7071728 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463608 /\ (1463608 + 124 <= q \/ q + 32 + 16 <= 1463608 + 120) /\ 1463608 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1463608 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 7071728 (2 * 3) 0 0 (zero_lines 3%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { rewrite (sbm_rdrA _ _ SBM1). exact (di_rdr _ _ _ _ _ _ _ _ _ _ D). }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }

    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1468480) || ((1472440 <=? a) && (a + Z.of_nat n <=? 7069728)) || ((7070276 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1463608 <= a -> a + n <= 1463608 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463608) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1463640 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1463648 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1463664 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1463696 8%nat _ SObuf eq_refl)
           (LIT3 1463704 8%nat _ SObufsz eq_refl) (LIT3 7069712 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1463616 8%nat _ SOrpos eq_refl) (LIT3 1463624 8%nat _ SOrend eq_refl)
           (LIT3 1463600 8%nat _ (XCC 16%nat 1463600 8 1463368 eq_refl) eq_refl) (LIT3 1463508 4%nat _ (XCC 17%nat 1463508 4 4294967295 eq_refl) eq_refl)
           (LIT3 1463408 8%nat _ (XCC 18%nat 1463408 8 0 eq_refl) eq_refl) (LIT3 1463424 8%nat _ (XCC 19%nat 1463424 8 0 eq_refl) eq_refl)
           (LIT3 1463376 8%nat _ (XCC 20%nat 1463376 8 0 eq_refl) eq_refl) (LIT3 1463384 8%nat _ (XCC 21%nat 1463384 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x149404) M3 R4 (Z_to_bv 64 0x141724) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x141724) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

End Exit.
End FPX_1.
