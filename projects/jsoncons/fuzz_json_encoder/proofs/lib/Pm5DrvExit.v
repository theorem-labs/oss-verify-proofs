(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, the 6144513-byte zero-filled stack window): changed XC_CELLS_L, XC_CELLS_T, XC_REST and 31 more; added vmc_refl; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9DrvExit.v, 2172 lines within its lines 18-3112. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm5IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm5DrvEntry Pm5Drv_defs Pm5DrvLib Pm5DrvRead Pm5DrvPiece Pm5DiagLoopK Pm5DrvStdio Pm5DrvPrintfK Pm5DrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require L5Defs L5KnA L5Core ArtMem Pm5ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5DrvP_dpX Pm5DrvP_dpX2_pre Pm5DrvP_dpX3_pre Pm5DrvP_dpX4_pre Pm5DrvP_dpXd_2 Pm5DrvP_dpXd_3 Pm5DrvP_dpXd_4 Pm5DrvP_dpXe Pm5DrvP_dpXL Pm5DrvP_dpXL2_pre Pm5DrvP_dpXL3_pre Pm5DrvP_dpXL4_pre.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @nil]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Lists; @ListDef; @Forall]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @AsanUbsan; @M; @loaded_segments]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Datatypes; @fst]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Datatypes; @snd]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Corelib; @Init; @Datatypes; @nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cells_at]; [@Stdlib; @Lists; @List; @nth_error]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @In]; [@Stdlib; @Lists; @List; @Forall_forall]; [@Stdlib; @Lists; @List; @nth_error_In]; [@Corelib; @Init; @Logic; @and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @XC_CELLS_T]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @XC_CELLS_L]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @XC_REST]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @exitR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @ATX]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @exitT]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cells_at_sub]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @true]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @exitL]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SeqExec; @rdn_app]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@stdpp; @bitvector; @definitions; @bv_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @nat_to_word]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@stdpp; @bitvector; @definitions; @bv_add_unsigned]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @ECALLW]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @SpuriousCfg]; [@Corelib; @Init; @Datatypes; @bool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @H_off_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @lazy_cover]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @A_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @MInv]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @mrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcctShape; @srz_msteps_restricted_T]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5Drv_defs; @asegs_wx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @hclean]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @munrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @mrestrict_munrestrict]; [@Stdlib; @Lists; @List; @existsb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cell_eqb]; [@Corelib; @Init; @Logic; @ex]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StreamSim; @wseg_ok]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @writable]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_window]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AgentLib; @u64_lit]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @art_bytes1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @dinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvStdio; @EX_CELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @di_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ri_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @cell_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ahid]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @dla_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @rdn_mrestrict_eq]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @f_equal]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvStdio; @vis_low]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @woff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @range_avoids]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @SHW_WINS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @shchk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmIcptDrvA; @aic_shadow_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @LOWSH_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @LOWSH_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @HIGHSH_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @HIGHSH_HI]; [@Stdlib; @Bool; @Bool; @andb_false_intro2]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_in_ranges]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @page_allowedb]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmIcptDrvA; @aic_img_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @dla_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @dla_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5ArtFsInv; @ART_POISON]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @icl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5IcptLayout; @aicl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @in_shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @byte_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_allowed]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_size]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @writable_of_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @exit_preT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvPrintfK; @stdoutA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvPrintf1; @stdoutXA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_exit]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvPrintfK; @SOBUF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX; @AS0DRVP_dpX; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @store_ok_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @wsg_writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @sh_writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @ex_cell_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cell_in_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cells_at_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cells_at_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvStdio; @img_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX; @AS0DRVP_dpX; @dpX_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @img_clear]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @wsg_writableZ0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u32_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @cell1_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u8_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX; @AS0DRVP_dpX; @KS_dpX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @dinv_lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @msteps_vis_fx]; [@LinuxProcessSemantics; @LinuxProcessSem; @Fs; @Fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @DrvNodesLazyK; @rz_exit_at_lit_lz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @fetch_exitA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SymDriveX; @is_ecall_ECALLW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @sbm_halted_eq]; [@Corelib; @Init; @Logic; @eq_trans]; [@Corelib; @Init; @Logic; @proj2]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvLib; @sbm_fds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @exit_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @exitA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @stdoutPA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @XC_CELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXe; @AS0DRVP_dpXe; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXe; @AS0DRVP_dpXe; @dpXe_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXe; @AS0DRVP_dpXe; @KS_dpXe]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @zero_lines]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @dpX2_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX2_pre; @AS0DRVP_dpX2_pre; @KS_dpX2_pre]; [@Corelib; @Init; @Datatypes; @orb]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Bool; @Bool; @orb_true_iff]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @or_iff_morphism]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvStdio; @rdn_tr]; [@Corelib; @Init; @Nat; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @rdn_cons1]; [@Corelib; @Init; @Nat; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvPrintf1; @nl_pt]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_mono]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @map]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @wv_loop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeLaws; @t_exit_has_nil]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @sbm_lazy_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @sbm_fds']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @wv_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @wv_iov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @wv_buf]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Corelib; @Numbers; @BinNums; @positive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @WV_KEEP]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Init; @Logic; @eq_sym]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_2; @AS0DRVP_dpXd_2; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_2; @AS0DRVP_dpXd_2; @dpXd_2_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_2; @AS0DRVP_dpXd_2; @KS_dpXd_2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv_sbm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DiagLoopK; @wv_done]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @dpX3_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX3_pre; @AS0DRVP_dpX3_pre; @KS_dpX3_pre]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_3; @AS0DRVP_dpXd_3; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_3; @AS0DRVP_dpXd_3; @dpXd_3_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_3; @AS0DRVP_dpXd_3; @KS_dpXd_3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @dpX4_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpX4_pre; @AS0DRVP_dpX4_pre; @KS_dpX4_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_4; @AS0DRVP_dpXd_4; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_4; @AS0DRVP_dpXd_4; @dpXd_4_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXd_4; @AS0DRVP_dpXd_4; @KS_dpXd_4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5DrvExit; @FPX_1; @Exit; @exit_preL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL; @AS0DRVP_dpXL; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL; @AS0DRVP_dpXL; @dpXL_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL; @AS0DRVP_dpXL; @KS_dpXL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @dpXL2_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL2_pre; @AS0DRVP_dpXL2_pre; @KS_dpXL2_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @dpXL3_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL3_pre; @AS0DRVP_dpXL3_pre; @KS_dpXL3_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @dpXL4_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm5DrvP_dpXL4_pre; @AS0DRVP_dpXL4_pre; @KS_dpXL4_pre]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Definition XC_CELLS : list (Z * Z * Z) :=
  [(7084800, 4, 0); (7084835, 1, 0); (7084272, 8, 7084280); (7084264, 4, 1); (7084288, 8, 1332024); (7084544, 8, 656352); (7084260, 4, 0); (7084280, 8, 0); (7086232, 8, 0); (1478672, 8, 1478440); (1478580, 4, 4294967295); (1478480, 8, 0); (1478496, 8, 0); (1478448, 8, 0); (1478456, 8, 0); (1478432, 8, 1478200); (1478192, 8, 1477960); (1478100, 4, 4294967295); (1478000, 8, 0); (1478016, 8, 0); (1477968, 8, 0); (1477976, 8, 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATX (ls2 : bool) : list (Z * Z * Z) :=
  if ls2 then [(7084835, 1, 0); (7084272, 8, 7084280); (7084264, 4, 4); (7084288, 8, 1332024); (7084544, 8, 656352); (7084296, 8, 1332024); (7084552, 8, 724392); (7084304, 8, 1052264); (7084560, 8, 1477752); (7084312, 8, 485656); (7084568, 8, 0); (7084260, 4, 0); (7084280, 8, 0)]
  else [(7084835, 1, 0); (7084272, 8, 7084280); (7084264, 4, 2); (7084288, 8, 1332024); (7084544, 8, 656352); (7084296, 8, 1332024); (7084552, 8, 724392); (7084260, 4, 0); (7084280, 8, 0)].
Definition XC_REST : list (Z * Z * Z) :=
  [(7084800, 4, 0); (7086232, 8, 0); (1478672, 8, 1478440); (1478580, 4, 4294967295); (1478480, 8, 0); (1478496, 8, 0); (1478448, 8, 0); (1478456, 8, 0); (1478432, 8, 1478200); (1478192, 8, 1477960); (1478100, 4, 4294967295); (1478000, 8, 0); (1478016, 8, 0); (1477968, 8, 0); (1477976, 8, 0); (6946324, 1, 0)].
Definition XC_CELLS_T : list (Z * Z * Z) :=
  [(7084800, 4, 0); (7084835, 1, 0); (7084272, 8, 7084280); (7084264, 4, 2); (7084288, 8, 1332024); (7084544, 8, 656352); (7084260, 4, 0); (7084280, 8, 0); (7086232, 8, 0); (1478672, 8, 1478440); (1478580, 4, 4294967295); (1478480, 8, 0); (1478496, 8, 0); (1478448, 8, 0); (1478456, 8, 0); (1478432, 8, 1478200); (1478192, 8, 1477960); (1478100, 4, 4294967295); (1478000, 8, 0); (1478016, 8, 0); (1477968, 8, 0); (1477976, 8, 0); (7084296, 8, 1332024); (7084552, 8, 724392); (6946324, 1, 0)].
Definition XC_CELLS_L : list (Z * Z * Z) :=
  [(7084800, 4, 0); (7084835, 1, 0); (7084272, 8, 7084280); (7084264, 4, 4); (7084288, 8, 1332024); (7084544, 8, 656352); (7084260, 4, 0); (7084280, 8, 0); (7086232, 8, 0); (1478672, 8, 1478440); (1478580, 4, 4294967295); (1478480, 8, 0); (1478496, 8, 0); (1478448, 8, 0); (1478456, 8, 0); (1478432, 8, 1478200); (1478192, 8, 1477960); (1478100, 4, 4294967295); (1478000, 8, 0); (1478016, 8, 0); (1477968, 8, 0); (1477976, 8, 0); (7084296, 8, 1332024); (7084552, 8, 724392); (7084304, 8, 1052264); (7084560, 8, 1477752); (7084312, 8, 485656); (7084568, 8, 0); (6946324, 1, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6952936) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x169040 <= i < 0x16a100 -> MV (Z_to_bv 64 i) = None).
Definition exitT (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_T
  /\ rdn ASEGS MV (Z_to_bv 64 6952936) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x169040 <= i < 0x16a100 -> MV (Z_to_bv 64 i) = None).
Definition exitL (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_L
  /\ rdn ASEGS MV (Z_to_bv 64 6952936) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x169040 <= i < 0x16a100 -> MV (Z_to_bv 64 i) = None).
Definition exitR (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_REST
  /\ rdn ASEGS MV (Z_to_bv 64 6952936) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x169040 <= i < 0x16a100 -> MV (Z_to_bv 64 i) = None).
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

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x14509c) = Some ECALLW.
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
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6c4000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma atx_vis : forall LB LK cr A M (model : Model) ls2, dinvA LB LK cr A M model -> cells_at M (ATX ls2) -> cells_at (mrestrict (ahid A model) M) (ATX ls2).
  Proof using HIok DL Hsp.
    intros LB LK cr A M model ls2 D HC. apply Forall_forall. intros [[a n] v] Hc. pose proof (proj1 (Forall_forall _ _) HC _ Hc) as X. cbn [fst snd] in X |- *.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6c4000).
    { destruct ls2; unfold ATX in Hc; cbn [In] in Hc; repeat (destruct Hc as [Hc|Hc]; [injection Hc as <- <- <-; cbn; lia|]); destruct Hc. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Definition SHW_WINS : list (Z * Z) := [(2147469664, 2147471724); (2147630476, 2147630492); (2147635720, 2147636256)].
  Definition shchk (a n : Z) : bool := (0 <=? n) && existsb (fun w => (fst w <=? a) && (a + n <=? snd w)) SHW_WINS.
  Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model -> shchk a n = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "Sl60!2+1+2+2!1+;0|600;!1,92!1+83|30;!1+8!1,95!1+:6!1,7'`N!2'_A,5#4!3'A+2+2#1!3'C+2+2#1!3'_70$w;R0!2'_=!2'_A:#6!2'_A!2'^8#6#5;'aD!3+=+^L!2'_A,5#5,^6%~R!3+=+^L!2'_A#2#1,^6!2'O#3#2$n;R+2$m;R+2!5'U>%~R!2'O#2#1!3+=+^L!2'_A#3#2,^6%~R!3+=+^L!2'_A#2#1,^6!2'O#3#2$~R>$~R%~R!2'O#3#2!3+=+^L!2'_A#4#3,^6#2!2'_D#2#1%n;R+2%m;R+2>!2'O,5#:%~R#1+^L!1+;#2%~R!3+=+^L!3'_7#3#2#1,^6!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6!2'^8#>#=!2'_=!2'_A:#>!2'_AE;!3'J0#1'aD!3'J0#2'aD!3'C+2+2#2!2'_A!3'A+2+2#6#F!2'_A!2'^8#F#E!3'C+2+2#6!3+=+^L!2'_A!3'A+2+2#7#G,^6!3'A+2+2#<!2'^8#N#M!3'C+2+2#>!2'O,5#1!2+MP!2'P#1#O!2'^8#Q#2!1,4|N3fffc960;!1,4|N3fffd16c;!4,3+2+2ST!3+=0U#B!1,4|O00023d8c;!1,4|O00023d9c;!4,3+2+2WX!3+=0Y#B!1,4|O00025208;!1,4|O00025420;!4,3+2+2[\!2+T!3+=0^0#B+^0!2+TZ^1!1,Q6!2'O:#U!2'O!2'^8#V#UI!2'@3#6!1'a:!3+=7!1#Y^6^3!3+=+^L!3'`[#Z#X^6,Y!3'A+2+2U!2'^8#U#T!3'C+2+2U!2'^8#V#7!3+=+2#5^<|10;!1,4^>!1,4|50f;!2'_G^?^@!2'P,5^?!2'_B^?^@%~R^B%~R!2'O,5^@!2'P,5^C!2'O,5^?$Ha;R^E$~R+_H!3'_I^?^@#2%Ha;R^E%~R+_H!2'O,5^C!2'^;3/sp0;|40;!1,4^I!2'a8^H^J!2'^B^H^J!2'O,5^L%~R!2'O,5^H%~R!2'O,5^J^M!2'a9^H^J!3+=+2^J,5!2'a<^H^J%~R!1'a:^P!3+=+2^H!2'^8!2'a;^J^Q^L!2'a=^H^J!2'P,5^J%~R^T!2+M^M!2'P^L^J!2'a>^H^J%~R!2'P^J,5!2+M!2'P^J^L!2'O^L,5!2'a?^H^J%~R^P!3+=+2^Q,5!2'a@^H^J%~R^P!3+=+2^L^H!2'O,5#B!2'O,5#D!2'P#E#^6}5!2,`0+2_2}2!2,`0+2_4!2,`0+2,`1}4!2,`0+2_7}3!2,`0+2_9!1,7+_J!3,0+_J!2,_[!3,_\+2_3!3,_\+2_5_6,`2!3,0+_J!2,_[!3,_\+2_8!3,_\+2_:_6,`2_;!1+;+_J!2,_K+2#3!2,_K+2#5!1,`4+2!4,`3+2_>#2!4,`3+2_?#4_@!1+_L+2!1+_N+2!2,_S+2^>|21;!2,_S+2_E!7,_M_C'_O+_P+_P,_Q!4,_R+2_D,`;_F,_U!1,Q+_P!2,`9+2,5!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7_D,_U!2,`9+2S!2,_S+2,6!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7_L,_U!3,`6+2_L_F!2,`9+2T!1,4|^13fff80000000;|11;!7,_M_C'_O+_P+_P,_Q!4,_R+2!2,`9+2_P,`7!2,_S+2_Q,_U!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#7!3,`6+2_L_D!2'_V_C,_Q!4'_W#1#3vv!2,^3+^L,^6!3+=+^L!2'_X#1#3,^6!3'_Y+2,5#2!2'P#2#4!2'O,5#3!2'^8#4#7!2'O_P#7!2+M_Z#9!2'^8#6#7!2'O^H^C!2+M!2'OS#5!2'P#5T!2+M!2'O'aG#6!2'P#6'aH!2'^8#W#8!3+=+2#6`3!2'O,5#C|N3fff8000;!1,4`6!1,4|O0fff7000;!2'O,5#E!2'P#F#^7!2,_K+2#2!7,`:_C'_O+_P+_P,_Q_M!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;_O,_U!2,`9+2`7!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2`=,`7_L,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;!2,`9+2`8,_U!2'OS#1!2+M`?!2'P#1T!2+M!2'O`7#2!2'P#2`8!1'aM^6%~R!3+=+^L!1'aN#1,Y!3+=+^L#2,^6%~R!3+=+^L#1,^6!3+=+^L!1'aN#2,Y$b;R+^L!5'U`C`D%~R!3+=+^L#1,^6!3+=+^L!1'aN#2,Y$~R`C$~R%~R!3+=+^L#2,^6!3+=+^L!1'aN#3,Y#1!1'aP#1%b;R+^L`D!1,4|N3fffd000;!2'P#8`G!2'O`G#8!2'aO#^0!1'aM!2'@3#9!1'`T#\!1,4|A00000;|@0000;!1,4`M!2'^8#[#<!3+=+2#:`Ovd!2,^3+2`O`P!2'O,5#G!2'P#G#^8!2'O`N`L!2'O,5#I!2'P#J#^;!2,`9+2`N!2,`9+2`L!1'aT/L;!5'aU/L;/ar;/IL;/sp0;/DL;!1,4|F2c4000;!2'^8`L^J!2'O`\`[!2,`9+2^J!3,`6+2`Xa1!2,`9+2`[!1'aV/L;!5'aW/L;/ar;/IL;/sp0;/DL;&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;a1,_U_U_V^T#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S^T$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`Va6#2#1#F$r;R0!2+T!2'O`\:!2'O;`L!1,4|A04b00;!1,4|A04b20;!4,3+2+2a9a:!1,4|A04c60;!1,4|A04cc0;!4,3+2+2a<a=!1,4|A04ce0;!1,4|A04d40;!4,3+2+2a?a@!1,4|A04e80;!1,4|A05040;!4,3+2+2aBaC!1,4|A05240;!1,4|A05cc0;!4,3+2+2aEaF!1,4|A05d00;!1,4|A08680;!4,3+2+2aHaI!1,4|A088a0;!1,4|A08900;!4,3+2+2aKaL!1,4|A08a00;!1,4|A08a60;!4,3+2+2aNaO!1,4|A08a80;!1,4|A08b60;!4,3+2+2aQaR!1,4|D5ec60;!1,4|D5ece0;!4,3+2+2aTaU!1,4|D69040;!1,4|D6a100;!4,3+2+2aWaX!1,70!3,00aYaZ!3,00aVa[!3,00aSa\!3,00aPb0!3,00aMb1!3,00aJb2!3,00aGb3!3,00aDb4!3,00aAb5!3,00a>b6!2+T!2'O`\a9!2'Oa:`L!2,`9+2a9!2,`9+2a:!3'A+2+2a;!3'C+2+2a;!2+T!2'O`\a<!2'Oa=`L!2,`9+2a<!2,`9+2a=!3'A+2+2a>!3'C+2+2a>!2+T!2'O`\a?!2'Oa@`L!2,`9+2a?!2,`9+2a@!3'A+2+2aA!3'C+2+2aA!2+T!2'O`\aB!2'OaC`L!2,`9+2aB!2,`9+2aC!3'A+2+2aD!3'C+2+2aD!2+T!2'O`\aE!2'OaF`L!2,`9+2aE!2,`9+2aF!3'A+2+2aG!3'C+2+2aG!2+T!2'O`\aH!2'OaI`L!2,`9+2aH!2,`9+2aI!3'A+2+2aJ!3'C+2+2aJ!2+T!2'O`\aK!2'OaL`L!2,`9+2aK!2,`9+2aL!3'A+2+2aM!3'C+2+2aM!2+T!2'O`\aN!2'OaO`L!2,`9+2aN!2,`9+2aO!3'A+2+2aP!3'C+2+2aP!2+T!2'O`\aQ!2'OaR`L!2,`9+2aQ!2,`9+2aR!3'A+2+2aS!3'C+2+2aS!2+T!2'O`\aT!2'OaU`L!2,`9+2aT!2,`9+2aU!3'A+2+2aV!3'C+2+2aV!2+T!2'O`\aW!2'OaX`L!2,`9+2aW!2,`9+2aX!3'A+2+2aY!3'C+2+2aY!1'a[/IL;!2'a\/IL;/ILY;!3'b0`L^J#1!3'b1#^2#2,5!3'b1#^3#2,5%x;R+2%~RcDcF!3'b1#^5#2,5!1,4|N3fffc000;!2'^8#^3#A!3+=+2#?cJvd!2,^3+2cJcK!1,45!2'O,5cM!2'a<`LcM!1,4,6!2'b4`\cP!2'a<cQcM!3+=+2cM,5!1'a:cS!2'^B`LcM!2'P,5cM!2'PcM,5!2'^BcQcM!2'O,5#\!2'P#\#^M!2'O,5#^1!2'P#^2#^P!3,b5+2!2,b6+2cM_6!2,`G+2!1,`H,6!3,0+_J!2,_[!3,_\+2_3!3,_\+2_8d0,`2!3,0+_J!2,_[!3,_\+2_:!3,_\+2!3,`F+2d1_5d0,`2_;!2,_K+2#6!4,`3+2!4,`3+2_@#3!4,`3+2d3#6_@#2!4,`3+2!4,`3+2_?#6_@#4_@!2,`9+2cM!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;d5,_U|32;!2,_S+2d7!8,`5_C'_O+_P+_P,_Qd6_H!7,`:_C'_O+_P+_P,_Q!6,`J_C'_O+_P+_P,_Q#8!7,_M_C'_O+_P+_P,_Q!4,_R+2d8,`;d5,_U!6,b7_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2d5,_T_I,_U!2,`9+2cP!3,`6+2!3,b9+2d5_Dd8|31;!2,_S+2d=!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7d>,_U!6,`J_C'_O+_P+_P,_Q#9!8,`5_C'_O+_P+_P,_Qd6_H!7,`:_C'_O+_P+_P,_Qd?d@!3,`6+2!3,b9+2d5_Ld>!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#:!3,`6+2_L`=!2,`9+2cI!3,`6+2_D`=%~RcV!2+M#7!2'P#6cM%~RcS+^0!2'^8!2'a;cM#4#7!2'O,5#7%~RcV!2+MdJ#:!2'^8!2'a;cM#5#8!2+M_Z#<!2'^8#6`7!2'^8#7`7!2'O,5#=!=#1`0!2'P#DcMdP#=#D^H#>#E#B#C#I#J/Hsp;!2'@3cI!1'aMdR!2'@3!2'a;!2'a<#1'b:'b:!2'@3#A!2'^;3dU$z;R+2!3+=4dT!2'@3!2'a;!2'a<dV'b:'b:!2'a;!2'a<cI'b:'b:!1'@3!2'a;!2'a<#@'b:'b:!2,^3%~R+24dY!2'^8#^4#B!3+=+2#@d\vd!2,^3+2d\e0|<000;!1,4e2!2'O,5cI!2'O,5e3!2'a<cIe3!2'b3#De3%~R_0%~Re5!2'O,5!2'a<#Fe3!3+=+2e3,5!1'a:e9!2'^BcIe3!2'P,5e3!2'Pe3,5!2'a9#Me3!2'^B#Ne3%~Re:!3+=+2#N!2'^8!2'a;e3!2'a<#Ne3e?!2'a=#Ne3!2'^B#Oe3%~Re<!2+M!2'O,5eB!2'PeBe3!2'a>#Oe3!2'^B#Pe3%~Re=!2+M!2'Pe3eE!2'OeE,5!2'a?#Pe3!2'a<#Qe3%~Re9!3+=+2eH,5!2'a@#Qe3!2'^B#Re3%~Re9!3+=+2eK#R!2'a<#Re3!2'^B#Se3!2'O,5#^0!2'P#^0#^N!2'O,5#^2!2'P#^3#^Q}<!2,`0+2eS}:!2,`0+2eU!3,`F+2d1eV}9!2,`0+2eX}8!2,`0+2eZ!3,_\+2eYe[}1!2,`0+2f0!2,b<e\!2,b<_5!2,_[!3,_\+2_5!3,_\+2f1_6,`2!2,b6+2e3!3,b5+2f3_6};!2,`0+2f5!3,`F+2d1e[}7!2,`0+2f8!2,b<_6!2,_[!3,_\+2f4!3,_\+2eT!3,_\+2f6!3,_\+2eV!3,_\+2f7!3,_\+2!3,`F+2d1f9!3,_\+2_8_:,`2!2,_K+2#7!4,`3+2!2,_K+2#9#5_@!2,_K+2#8!4,`3+2!4,`3+2!4,`3+2f;#9_@#3f<#2!4,`3+2!4,`3+2f=#9_@#4d3!2,`9+2e3!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`;f?,_U!8,`5_C'_O+_P+_P,_Qf@_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7d8,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2d8,`;f?,_U!6,b7_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2f?,_T_I,_U!2,_S+25!8,`5_C'_O+_P+_P,_QfB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2fC,_T!3,`6+2!3,b9+2f?_Dd8,_U!8,`5_C'_O+_P+_P,_Qf@_H!7,`:_C'_O+_P+_P,_Qd?!7,_M_C'_O+_P+_P,_Q!4,_R+2d>,`;f?,_U!3,`6+2!3,b9+2f?_Ld>|22;!2,_S+2fG|23;!2,_S+2fI!7,_M_C'_O+_P+_P,_Q!4,_R+2fC,_T!3,`6+2fHfJ,_U!2,`9+2`G!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7fC,_U!6,`J_C'_O+_P+_P,_Q#;!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7fJ,_U!6,`J_C'_O+_P+_P,_Q#<!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b9+2_Lf?,_T!3,b9+2_Df?,_U%~Re<!2+M!2'O,5#9!2'P#9e3%~Re9+^0!2'a;e3#4%~RfS!3+=+2#8!2'^8fT#:%~Re<!2+MA!2'P#:e3!2'a;e3#5!2'^8fW#;!3+=+2#:!2'^8#8#9!2'OS#<!2'a;#;e3!2'a;#<e3!2'@3#@!2'^;3g0!1,42!2'_G^?g2!2'_B^?g2%~R^B%~R!2'O,5g2!2'P,5g4$Ha;R^E$~R+_H!3'_I^?g2#2%Ha;R^E%~R+_H!2'O,5g4!2'O,5#O!2'P#O#^@!2'O,5#Q!2'P#R#^C!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7_L,_U!2,`9+2^?!3,`8+2g=3!7,`:_C'_O+_P+_P,_Qg<!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;g>,_U!2'O,5#2!2+Mg@!2'P#2g4!2'_Z#@&heq_x;Re1e0&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ug8g9!2+M!2'O,5#M!2'P#Mg4$~Rg8$~R!2'P#P#^A!2$H4;Rg:$H5;Rg;&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q`<_Hg?_U_V%__x1;R+2%~R`@gA!2#1#R#M#2#1#N!2+Me4!2'PcIg4!1'aMg0!3+=4dSgD$b;R4!3+=+^L!2'aO#^9#1,^6!1'aMdU!2'O`NaI!2'^8aI^J!2'OgI`[!3,`6+2bSa1$r;R0!2+T!2'OgI:!2'O;aI!2+T!2'OgIa9!2'Oa:aI!2+T!2'OgIa<!2'Oa=aI!2+T!2'OgIa?!2'Oa@aI!2+T!2'OgIaB!2'OaCaI!2+T!2'OgIaE!2'OaFaI!2+T!2'OgIaH!2'OaIaI!2+T!2'OgIaK!2'OaLaI!2+T!2'OgIaN!2'OaOaI!2+T!2'OgIaQ!2'OaRaI!2+T!2'OgIaT!2'OaUaI!2+T!2'OgIaW!2'OaXaI!3'b0aI^J#1%x;R+2%~RgXcF!1,4|N3fffd0d0;!2'a<aIcM!2'b4gIcP!2'a<g\cM!2'^BaIcM!2'^Bg\cM!2,`9+2gZ!2'@3gZ!1'aMh4!2'a;!2'a<gZ'b:'b:!2'O,5gZ!2'a<gZe3!2'^BgZe3!3,b5+2f3f1}6!2,`0+2h;!3,_\+2eT!3,_\+2eW_8!2+Mh7!2'PgZg4!3+=4h5gD!3+=0Y#C!2+T!3+=0^0#C+^0!3+=0Y#D!3+=0^0#D!2+ThC+^0!2'O:#W!2'O!2'^8#X#WI!2'@3#8!1'a:!3+=7!1#[hG^3!3+=+^L!3'`[#\#ZhG,Y!3'A+2+2Y!2'^8#W#V!3'C+2+2Y!2'^8#X#9!3+=+2#7hM!2'O,5#F!2,`9+2W!7,_M_C'_O+_P+_P,_Q!4,_R+2hP,`7_L,_U!2,`9+2X!2+M!2'OW#7!2'P#7X!2+M!2'O'aG#8!2'P#8'aH!2'^8#Y#:!3+=+2#8hU!2'P#H#^9!7,`:_C'_O+_P+_P,_QhQ!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;hR,_U!2'OW#1!2+MhY!2'P#1X!1'aMhG!1,4|D58000;!2'^8#Z#;!3+=+2#9i0vd!2,^3+2i0i1!2'O`Nh\!2'O,5#H!2'P#I#^:!2,`9+2h\!2'^8h\^J!2'Oi7`[!3,`6+2i6a1$r;R0!2+T!2'Oi7:!2'O;h\!2+T!2'Oi7a9!2'Oa:h\!2+T!2'Oi7a<!2'Oa=h\!2+T!2'Oi7a?!2'Oa@h\!2+T!2'Oi7aB!2'OaCh\!2+T!2'Oi7aE!2'OaFh\!2+T!2'Oi7aH!2'OaIh\!2+T!2'Oi7aK!2'OaLh\!2+T!2'Oi7aN!2'OaOh\!2+T!2'Oi7aQ!2'OaRh\!2+T!2'Oi7aT!2'OaUh\!2+T!2'Oi7aW!2'OaXh\!3'b0h\^J#1%x;R+2%~RiFcE!3'b1#^4#2,5!1,4|O00023000;!2'^8#^2#@!3+=+2#>iJ!2'b4i7cP!2'a<iLcM!2'a<h\cM!2'^Bh\cM!2'^BiLcM!2'O,5#[!2'P#^1#^O!2,`9+2iI!2'@3iI!1'aMiT!2'a;!2'a<iI'b:'b:!2'a;!2'a<#?'b:'b:!2'O,5iI!2'a<iIe3!2'^BiIe3!2'^B#Qe3!2'OW#;!2'O,5#;!2'@3#?!2'O,5#N!2'P#N#^?!2'O,5#P!2'P#Q#^B!2+MiX!2'PiIg4!3+=4iU!1'aMj1!3+=0^0#E!3+=0^0#F!2'@3#:!1'a:!3+=7!1#^0j:^3!3+=+^L!3'`[#^1#\j:,Y!3'A+2+2^0!2'^8#Y#X!3'C+2+2^0!2,`9+2[!7,_M_C'_O+_P+_P,_Q!4,_R+2j@,`7_L,_U!2,`9+2\!2+M!2'O[#9!2'P#9\!2+M!2'O'aG#:!2'P#:'aH!7,`:_C'_O+_P+_P,_QjA!7,_M_C'_O+_P+_P,_Q!4,_R+2_L,`;jB,_U!2'O[#1!2+MjF!2'P#1\!1'aMj:!1,4|D68000;!2'^8#\#=!3+=+2#;jJvd!2,^3+2jJjK!2'O`NjI!2'O,5#J!2'P#K#^<!2,`9+2jI!2'^8jI^J!2'OjQ`[!3,`6+2jPa1$r;R0!2+T!2'OjQ:!2'O;jI!2+T!2'OjQa9!2'Oa:jI!2+T!2'OjQa<!2'Oa=jI!2+T!2'OjQa?!2'Oa@jI!2+T!2'OjQaB!2'OaCjI!2+T!2'OjQaE!2'OaFjI!2+T!2'OjQaH!2'OaIjI!2+T!2'OjQaK!2'OaLjI!2+T!2'OjQaN!2'OaOjI!2+T!2'OjQaQ!2'OaRjI!2+T!2'OjQaT!2'OaUjI!2+T!2'OjQaW!2'OaXjI!3'b0jI^J#1%x;R+2%~Rk3iH!1,4|O00025000;!2'b4jQcP!2'a<k6cM!2'a<jIcM!2'^BjIcM!2'^Bk6cM!2,`9+2k5!2'@3k5!1'aMk<!2'@3#B!2'a;!2'a<k5'b:'b:!2'a;!2'a<#A'b:'b:!2'^8#^5#C!3+=+2#AkAvd!2,^3+2kAkB!2'O,5k5!2'a<k5e3!2'^Bk5e3!2'O,5#^3}=!2,`0+2kH!2'P#P#^A!2'O,5#R!2'P#S#^D!2+MkD!2'Pk5g4!3+=4k=gG!2'@3R!3+=0U#@!2+T!3+=0Y#@!2+T!3+=0^0#@+^0|51f;!1,4kR!2'_B^?kS!2'_G^?kS%~R^B%~R!2'O,5kS!2'P,5kT$Ha;R^E$~R+_H!3'_I^?kS#2%Ha;R^E%~R+_H!2'O,5kT!4,`3+2_>#2_@!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7!3,`8+2g=!1,9kR,_U!7,`:_C'_O+_P+_P,_Qg<kZ!2'^8#2#3!2+M_X!2'O!2'^8#3#4kT!2'^Z!2'`[#T#R#S!2'@3!2'^8#S#2!2'@3!2'^8#T#3!1'a:!3+=7!1#Vl3^3!2'@3!2'^8#X#7$LB;R1$LK;R!1+;'`N$cr;R'`O$A;R1$M;R%~R47$model;R+^O$a;R+2$n;R+2$D;R!:+`P/ar;/HI;/sp0;/M0;#8#7#6#5#4#3$Hb;R!3+=+^L!2'aE#3#2,^6&HH;R!;'`R/ar;/HI;/sp0;/M0;#:#9#8#7#6#5#2!8'`S/HI;#:8#9#8#7#6!1'`T#5&Hb;R!3'_<9<#2!2+M!3+=+^L9,^6!3+=+^L<,^6!5'U=!3+=+^L!3'_70$w;R0!2'_=!2'_A:#7!2'_A!2'^8#7#6;'aD,^6!4'_C'?!2'^Z!2'`[#9#7#8#6#5$~R=$~R!3+=+^L!3'_70$w;R0!2'_=!2'_A:#8!2'_A!2'^8#8#7;'aD,^6!2$Hn;R!3+=+^L!2'_A,5#7,^6$Hb;R!3+=+^L!3'_70$w;R0!2'_=!2'_A:#:!2'_A!2'^8#:#9;'aD,^6&H;R?@&Hn;R!3#1,5#:#3A&H;R$A;R{g_7d;$f;RB$l;RC!5'UD%~R!2+_9#3$x;R#3!2+M!3'J#4#1#2!3+=+^L!1#3#1,^6!3+=+^L!3'_7#4#3#2,^6%~R!3+=+^L!3'_7#3#2#1,^6!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6$~RD$~R%~R!2+_9#4$x;R#4!2+M!3'J#5#1#3!3+=+^L!1#4#1,^6!3+=+^L!3'_7#5#4#3,^6#2!3'_:#3#2#1%A;R{g_7d;%f;RB%l;RCD&Hb;R!4#10$w;R0F'aD#4!2+_90$x;R0!2+MG!3+=+^LF,^6!5'_;0$x;R0!2+MG!3+=+^L!2'_=!2'_A:#?!2'_A!2'^8#?#>;,^6!4'_C'?!2'^Z!2'`[#A#?#@#>#=$x;R0$~R!1$x;R0!2+MG!3+=+^L!2'_=!2'_A:#@!2'_A!2'^8#@#?;,^6#1!2$w;R0$H;R!2+MG!3+=+^L!2'_=!2'_A:#A!2'_A!2'^8#A#@;,^6!5'UH!3+=+^L!2'_=!2'_A!3'A+2+2#2#B!2'_A!2'^8#B#AI,^6!4'_C'?!2'^Z!2'`[#E#C#D#B#A$~RH$~R!3+=+^L!2'_=!2'_A!3'A+2+2#3#C!2'_A!2'^8#C#B!3'C+2+2#3,^6!2$Hw;R!3'J0#4'aD$Hc;R!3+=+^L!2'_=!2'_A!3'A+2+2#5#E!2'_A!2'^8#E#D!3'C+2+2#5,^6&Hc;R!3'_<JK#1!2+M!3+=+^LJ,^6!3+=+^LK,^6!5'UL!3+=+^L!2'_A!2'^8#G#F!3'C+2+2#7,^6!4'_C'?!2'^Z!2'`[#J#H#I#G#F$~RL$~R!3+=+^L!2'_A!2'^8#H#G!3'C+2+2#8,^6!2$C1;R!3+=+^L!2'_A!3'A+2+2#9#I,^6$C2;R!3+=+^L!2'_A!2'^8#J#I!3'C+2+2#:,^6&H;R?@&C1;R!3#1M#L#3!2'OM#L&H;R?@&C2;R!3#1NO#4!2'ONO&CORE;R$i;R+2$Hi;RQ&x;RR+2!6'VV^2!2+M!1'a:!3+=7!1#T!2'@3#1^3!3+=+^L!3'`[#U#S!2'@3#1,Y$~RV!1$H;R!3+=0U#C!8'^10U$w;R0%C1;R^4%C2;R^5!2+M^7^8$C1;R!2'O^9#T$C2;R!2'O^:^;&Hx;Rvd&heq_x;Rvd!2,^3+2^<^=^=&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U^\!2'P#B#^3!2+M!2'OS!2'^8#^4#B!2'P!2'^8#^4#BT$~R^\$~R!2'P#C#^4!2$H4;R_0$H5;R_1&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_Q_M_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7_O,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;_O,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'OS#3%~R!2'O_YT%~R_[!2+M!2'OS_\!2'P_\T!:#1`0#^8^H#G#^9#2#3#B#A/Hsp;#2#1#A`1`1!4,[^7^8!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^08#\#[#Z#Y!1'`T#X#S#6!3,^2`2!2+M!2'O'aI#6!2'P#6'aJvd&heq_x;Rvd!2,^3+2`3`4`4&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`5!2'P#C#^4!2+M!2'O`7#A!2'P#A`8$~R`5$~R!2'P#D#^5!2$H4;R`9$H5;R`:&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q`<_H`>_U_V%__x1;R+2%~R`@`A!2#1#F#A#2#1#B`2vd!3'aK!2'aL`B!1'^T#X!1'aN!2'aO#Z`B&H;R`E`F!2#1!2'aO#[!1'aM!2'@3#7&s;R!2'aQ#7`G!2+aR!2'P#7`G!2'O`G#7-aRRN$s;R!2+aR`H`I!3+=+^L`J,^6#12$l;R`H!1$Hpg;R!2'P#9`G&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#W`L^J!6'^?+2`N$z;R+2!2'O#1`L&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S`T$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7`X,_U_U_V`T#1#2#1#F`Y`Z!6'^?+2`[$z;R+2!2'O`\#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sa0$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7a3,_U_U_Va0#1#2#1#Fa4a5a7!6'^?1'aX$l;R1!3+<0a8#1!6,aY0a8a;b7vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb8$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b:,`7`X,_U_U_Vb8#1#2#1#F!2+T!2'O`\b;!2'Ob<`L!6,aY0a8a>b6vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb=$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b?,`7`X,_U_U_Vb=#1#2#1#F!2+T!2'O`\b@!2'ObA`L!6,aY0a8aAb5vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbB$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bC,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bD,`7`X,_U_U_VbB#1#2#1#F!2+T!2'O`\bE!2'ObF`L!6,aY0a8aDb4vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbG$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bH,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bI,`7`X,_U_U_VbG#1#2#1#F!2+T!2'O`\bJ!2'ObK`L!6,aY0a8aGb3vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbL$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bM,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bN,`7`X,_U_U_VbL#1#2#1#F!2+T!2'O`\bO!2'ObP`L!6,aY0a8aJb2vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbQ$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bR,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bS,`7`X,_U_U_VbQ#1#2#1#F!2+T!2'O`\bT!2'ObU`L!6,aY0a8aMb1vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SbV$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7bW,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bX,`7`X,_U_U_VbV#1#2#1#F!2+T!2'O`\bY!2'ObZ`L!6,aY0a8aPb0vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sb[$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7b\,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c0,`7`X,_U_U_Vb[#1#2#1#F!2+T!2'O`\c1!2'Oc2`L!6,aY0a8aSa\vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sc3$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7c4,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c5,`7`X,_U_U_Vc3#1#2#1#F!2+T!2'O`\c6!2'Oc7`L!6,aY0a8aVa[vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sc8$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7c9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c:,`7`X,_U_U_Vc8#1#2#1#F!2+T!2'O`\c;!2'Oc<`L!6,aY0a8aYaZvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`Sc=$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2a2,`7c>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c?,`7`X,_U_U_Vc=#1#2#1#F!2+T!2'O`\c@!2'OcA`L!2,aZ0a8cBcC!2+M%x;R+2%~RcDcE!3'b2#^1`L^J!5'UcG!3'b2#^2`L^J!3+=+^L!2'aO#^2!1'aM!2'@3#;,^6$~RcG$~R!3'b2#^3`L^J!2$_H;R%x;R+2%~RcDcH$SA;R!3'b2#^5`L^J&SA;R!2#1cIvdvd&heq_x;RcLcK&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3`LcM%~R!2'O,5`L%~RcN!2'O,5cO&__sat4;R!2'b3cQcM%~R!2'O,5cQ%~RcN!2'O,5cR&__sat3;R^K^N&H;R!2'a9`LcM%~RcT!3+=+2`L!2'^8!2'a;cMcOcU&H0;R!2'a=`LcM%~RcV!2+M!2'O,5cU!2'PcUcM&H1;R!2'a>`LcM%~RcW!2+M!2'PcMcU!2'OcU,5&H2;R!2'a?`LcM%~RcS!3+=+2cO,5&H3;R!2'a@`LcM%~RcS!3+=+2cU`L&q;RcO+2&r;RcU+2&H4;R!2'a9cQcM%~RcT!3+=+2cQ!2'^8!2'a;cMcRcX&H5;R!2'a=cQcM%~RcV!2+M!2'O,5cX!2'PcXcM&H6;R!2'a>cQcM%~RcW!2+M!2'PcMcX!2'OcX,5&H7;R!2'a?cQcM%~RcS!3+=+2cR,5&H8;R!2'a@cQcM%~RcS!3+=+2cXcQ&q0;RcR+2&r0;RcX+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcYcZ!2+M!2'O!2'^8#@`7cI!2'OcI!2'^8#9`7$~RcY$~R!2'P#^0#^N!2$H14;Rc[$H15;Rc\&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;Rd2_=&__varmap;Rd4_B&__ff;R!8,`5_C'_O+_P+_P,_Qd9_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2a2d;,_Td<,_U_H!8,`5_C'_O+_P+_P,_QdA_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2`X,_TdB,_U_H!8,`5_C'_O+_P+_P,_QdC_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2dD,`7dE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2dE,`7dF,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RdG%~R%~RdH!3+=+2cQdI%~RdK%~R%~RdH!3+=+2`LdL%~RdM!2+M!2'OdNcI!2'OcIdOdQ#2#1#[!2+M!2'O!2'^8cO`7cI!2'OcI!2'^8cR`7!3'b0`L^JcI!3+=+^L!2'aO#^6dS,^6&H;Rvd!6'^?+2cIdW!6'^?+2#@$z;R+2!3+=4!2'@3dXdT!8'b;+24dYdYdXdZd[vd&heq_x;Re1e0&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3cIe3%~Re4%~Re5!2'O,5e6&__sat4;Re7e8&__sat3;R^K^N&H;R!2'a9cIe3%~Re:!3+=+2cI!2'^8!2'a;e3e6e;&H0;R!2'a=cIe3%~Re<!2+M!2'O,5e;!2'Pe;e3&H1;R!2'a>cIe3%~Re=!2+M!2'Pe3e;!2'Oe;,5&H2;R!2'a?cIe3%~Re9!3+=+2e6,5&H3;R!2'a@cIe3%~Re9!3+=+2e;cI&q;Re6+2&r;Re;+2&H4;Re>e@&H5;ReAeC&H6;ReDeF&H7;ReGeI&H8;ReJeL&q0;ReM+2&r0;ReN+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UeOeP!3+=+2!2'a;#@e3!2'a;#9e3$~ReO$~R!2'P#^1#^O!2$H14;ReQ$H15;ReR&__arith;R$__p2;Rw$__p1;Rw$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<!3,_\+2eT!3,_\+2eW_3f2!3,0+_Jf:_;_=&__varmap;Rf>_B&__ff;R!8,`5_C'_O+_P+_P,_QfA_H!8,`5_C'_O+_P+_P,_QfD_H!8,`5_C'_O+_P+_P,_QfE_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QfB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2dE,_TfF,_U_H!8,`5_C'_O+_P+_P,_QfK_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2fC,`;fL,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_QfMfN_H!8,`5_C'_O+_P+_P,_QfO_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_K,`7fH,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_RfP_HfQ_U_V%__p2;Rw%__p1;Rw%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RfR%~RfU%~RfV%~R%~RfS!3+=+2cIfX%~RfY%~R!2'P#;`G%~R!2+MfZ#?%~R!2'O,5#<%~RfZ%~R!2+M!2'O_P#<#C!3+=+2f[f\!D#1`0!2'P#^3T#=#D#^3#^5#^T^H#>#E#B#C#I#J#P#W#[#3#^0/Hsp;#2#1#\!3+=+2dXdZg1gB!2'^;3dR!2'_ZcI&heq_x;Re1e0&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ug8g9gC$~Rg8$~R!2'P#P#^A!2$H4;Rg:$H5;Rg;&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7dE,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2dE,`;g>,_U_U_VgC#1#2#1#NgEgE!6'^14dSgF#2gG#1#2#1#1#1$l;R`I!1$Hpg;R!2'O`G#9&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#WaI^J!6'^?+2`N$z;R+2!2'O#1aI&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgH$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7bS,_U_U_VgH#1#2#1#F`Y`Z!6'^?+2`[$z;R+2!2'OgI#1&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgJ$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7a3,_U_U_VgJ#1#2#1#Fa4a5a7!6'^?1'aX$l;R1!3+<0gL#1!6,aY0gLa;b7vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgM$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7b9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b:,`7bS,_U_U_VgM#1#2#1#F!2+T!2'OgIb;!2'Ob<aI!6,aY0gLa>b6vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgN$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7b>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b?,`7bS,_U_U_VgN#1#2#1#F!2+T!2'OgIb@!2'ObAaI!6,aY0gLaAb5vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgO$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7bC,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bD,`7bS,_U_U_VgO#1#2#1#F!2+T!2'OgIbE!2'ObFaI!6,aY0gLaDb4vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgP$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7bH,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bI,`7bS,_U_U_VgP#1#2#1#F!2+T!2'OgIbJ!2'ObKaI!6,aY0gLaGb3vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgQ$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7bM,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bN,`7bS,_U_U_VgQ#1#2#1#F!2+T!2'OgIbO!2'ObPaI!6,aY0gLaJb2vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgR$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7bR,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bS,`7bS,_U_U_VgR#1#2#1#F!2+T!2'OgIbT!2'ObUaI!6,aY0gLaMb1vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgS$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7bW,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bX,`7bS,_U_U_VgS#1#2#1#F!2+T!2'OgIbY!2'ObZaI!6,aY0gLaPb0vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgT$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7b\,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c0,`7bS,_U_U_VgT#1#2#1#F!2+T!2'OgIc1!2'Oc2aI!6,aY0gLaSa\vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgU$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7c4,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c5,`7bS,_U_U_VgU#1#2#1#F!2+T!2'OgIc6!2'Oc7aI!6,aY0gLaVa[vd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgV$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7c9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c:,`7bS,_U_U_VgV#1#2#1#F!2+T!2'OgIc;!2'Oc<aI!6,aY0gLaYaZvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`SgW$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2gK,`7c>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c?,`7bS,_U_U_VgW#1#2#1#F!2+T!2'OgIc@!2'OcAaI!2,aZ0gLcBcC!2+M%x;R+2%~RgXcE!3'b2#^1aI^J!5'UgY!3'b2#^2aI^J!3+=+^L!2'aO#^2!1'aM!2'@3#;,^6$~RgY$~R!3'b2#^3aI^J!2$_H;R%x;R+2%~RgXcH$SA;R!3'b2#^5aI^J&SA;R!2#1gZvdvd&heq_x;RcLcK&__sat7;R!2'b3aIcM%~R!2'O,5aI%~RcN!2'O,5g[&__sat6;R^A^D&__sat5;R^F^G&__sat4;R!2'b3g\cM%~R!2'O,5g\%~RcN!2'O,5h0&__sat3;R^K^N&H;R!2'a9aIcM%~RcT!3+=+2aI!2'^8!2'a;cMg[h1&H0;R!2'a=aIcM%~RcV!2+M!2'O,5h1!2'Ph1cM&H1;R!2'a>aIcM%~RcW!2+M!2'PcMh1!2'Oh1,5&H2;R!2'a?aIcM%~RcS!3+=+2g[,5&H3;R!2'a@aIcM%~RcS!3+=+2h1aI&q;Rg[+2&r;Rh1+2&H4;R!2'a9g\cM%~RcT!3+=+2g\!2'^8!2'a;cMh0h2&H5;R!2'a=g\cM%~RcV!2+M!2'O,5h2!2'Ph2cM&H6;R!2'a>g\cM%~RcW!2+M!2'PcMh2!2'Oh2,5&H7;R!2'a?g\cM%~RcS!3+=+2h0,5&H8;R!2'a@g\cM%~RcS!3+=+2h2g\&q0;Rh0+2&r0;Rh2+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcYcZ!2+M!2'O!2'^8#@`7gZ!2'OgZ!2'^8#9`7$~RcY$~R!2'P#^0#^N!2$H14;Rc[$H15;Rc\&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;Rd2_=&__varmap;Rd4_B&__ff;R!8,`5_C'_O+_P+_P,_Qd9_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2gKd;,_Td<,_U_H!8,`5_C'_O+_P+_P,_QdA_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2bS,_TdB,_U_H!8,`5_C'_O+_P+_P,_QdC_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2dD,`7h3,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2h3,`7dF,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RdG%~R%~RdH!3+=+2g\dI%~RdK%~R%~RdH!3+=+2aIdL%~RdM!2+M!2'OdNgZ!2'OgZdOdQ#2#1#[!2+M!2'O!2'^8g[`7gZ!2'OgZ!2'^8h0`7!3'b0aI^JgZ!3+=+^L!2'aO#^6h5,^6&H;Rvd!6'^?+2gZdW!6'^?+2#@$z;R+2!3+=4!2'@3h6dT!8'b;+24dYdYh6dZd[vd&heq_x;Re1e0&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3gZe3%~Rh7%~Re5!2'O,5h8&__sat4;Re7e8&__sat3;R^K^N&H;R!2'a9gZe3%~Re:!3+=+2gZ!2'^8!2'a;e3h8h9&H0;R!2'a=gZe3%~Re<!2+M!2'O,5h9!2'Ph9e3&H1;R!2'a>gZe3%~Re=!2+M!2'Pe3h9!2'Oh9,5&H2;R!2'a?gZe3%~Re9!3+=+2h8,5&H3;R!2'a@gZe3%~Re9!3+=+2h9gZ&q;Rh8+2&r;Rh9+2&H4;Re>e@&H5;ReAeC&H6;ReDeF&H7;ReGeI&H8;ReJeL&q0;ReM+2&r0;ReN+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UeOeP!3+=+2!2'a;#@e3!2'a;#9e3$~ReO$~R!2'P#^1#^O!2$H14;ReQ$H15;ReR&__arith;R$__p1;Rw$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<!3,_\+2f9!3,`F+2d1_3!2,b<f1!2,_[!3,_\+2h:!3,_\+2f4!3,_\+2f6!3,_\+2eVh<,`2!3,0+_J!2,b<!3,_\+2h<_3!2,b<f1!2,_[!3,_\+2h:!3,_\+2f4h=,`2_;_=&__varmap;R!4,`3+2!4,`3+2!4,`3+2_?#7_@#3!4,`3+2f;#7_@#2!4,`3+2!4,`3+2d3#7_@#4_@_B&__ff;R!8,`5_C'_O+_P+_P,_QfA_H!8,`5_C'_O+_P+_P,_QfD_H!8,`5_C'_O+_P+_P,_QfE_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QfB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2h3,_TfF,_U_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2fL,`7fC,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_QfM!7,_M_C'_O+_P+_P,_Q!4,_R+2fC,`;_O,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_Rd@_HfQ_U_V%__p1;Rw%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R%~Re<!2+MdJ!2'P#7e3%~R%~RfS!3+=+2#6!2'^8fT#8%~R%~Re<!2+M!2'O,5#8!2'P#8e3%~R%~RfS!3+=+2gZ!2'^8fW#9%~R`I%~R!2+M!2'OS#9!2'P#9T%~R!2+M!2'O_P#9#=!3+=+2!2'a;#8e3!2'a;#9e3!>#1`0#=#D#^3^H#>#E#B#C#I#J#W#[/Hsp;#2#1#\!3+=+2h6dZg1gB!2'^;3h4!2'_ZgZ&heq_x;Re1e0&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ug8g9h>$~Rg8$~R!2'P#P#^A!2$H4;Rg:$H5;Rg;&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7h3,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2h3,`;g>,_U_U_Vh>#1#2#1#Nh?h?!6'^14h5gF#2gG#1#2#1#1#1^8#D#1#8#6#1$~R^2!1$Hw;R!2+Th@hA!6'VhBhD!2+M!1'a:!3+=7!1#V!2'@3#3^3!3+=+^L!3'`[#W#U!2'@3#3,Y$~RhB!1$H;R!3+=0Y#E!8'^10Y$w;R0%C1;RhE%C2;RhF!2+MhHhI$C1;R!2'OhJ#V$C2;R!2'OhKhL&Hx;Rvd&heq_x;Rvd!2,^3+2hMhNhN&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U_0!2'P#D#^5!2+M!2'OW!2'^8#^6#D!2'P!2'^8#^6#DX$~R_0$~R!2'P#E#^6!2$H4;RhO$H5;R`S&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_QhQ_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7hR,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hP,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;hR,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'OW#3%~R!2'O_YX%~R_[!2+M!2'OW_\!2'P_\X!:#1`0#^:^H#I#^;#2#3#B#A/Hsp;#2#1#ChShS!4,[hHhI!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^28#^1#^0#\#[!1'`T#Z#U#8!3,^2hT!2+M!2'O'aI#8!2'P#8'aJvd&heq_x;Rvd!2,^3+2hUhVhV&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`9_1!2+M!2'O`7#C!2'P#C`8$~R`9$~R!2'P#F#^7!2$H4;R`R$H5;RhW&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QhX_H`>_U_V%__x1;R+2%~RhZ`A!2#1#H#A#2#1#DhTvd!3'aK!2'aLh[!1'^T#Z!1'aN!2'aO#\h[&H;R`E`F!2#1`J&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^38#^2#^1#^0#\!1'`T#[#Vh\^J!6'^?+2`N$z;R+2!2'O#1h\&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i3$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7i6,_U_U_Vi3#1#2#1#E`Y`Z!6'^?+2`[$z;R+2!2'Oi7#1&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i8$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7a3,_U_U_Vi8#1#2#1#Ea4a5&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:^T$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5a6#2#1#E!6'^?1'aX$l;R1!3+<0i:#1!6,aY0i:a;b7vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i;$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7b9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b:,`7i6,_U_U_Vi;#1#2#1#E!2+T!2'Oi7b;!2'Ob<h\!6,aY0i:a>b6vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i<$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7b>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b?,`7i6,_U_U_Vi<#1#2#1#E!2+T!2'Oi7b@!2'ObAh\!6,aY0i:aAb5vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i=$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7bC,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bD,`7i6,_U_U_Vi=#1#2#1#E!2+T!2'Oi7bE!2'ObFh\!6,aY0i:aDb4vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i>$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7bH,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bI,`7i6,_U_U_Vi>#1#2#1#E!2+T!2'Oi7bJ!2'ObKh\!6,aY0i:aGb3vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i?$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7bM,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bN,`7i6,_U_U_Vi?#1#2#1#E!2+T!2'Oi7bO!2'ObPh\!6,aY0i:aJb2vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:i@$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7bR,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bS,`7i6,_U_U_Vi@#1#2#1#E!2+T!2'Oi7bT!2'ObUh\!6,aY0i:aMb1vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:iA$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7bW,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bX,`7i6,_U_U_ViA#1#2#1#E!2+T!2'Oi7bY!2'ObZh\!6,aY0i:aPb0vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:iB$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7b\,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c0,`7i6,_U_U_ViB#1#2#1#E!2+T!2'Oi7c1!2'Oc2h\!6,aY0i:aSa\vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:iC$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7c4,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c5,`7i6,_U_U_ViC#1#2#1#E!2+T!2'Oi7c6!2'Oc7h\!6,aY0i:aVa[vd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:iD$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7c9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c:,`7i6,_U_U_ViD#1#2#1#E!2+T!2'Oi7c;!2'Oc<h\!6,aY0i:aYaZvd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:iE$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2i9,`7c>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c?,`7i6,_U_U_ViE#1#2#1#E!2+T!2'Oi7c@!2'OcAh\!2,aZ0i:cBcC!2+M%x;R+2%~RiF!3'b1#^1#2,5!3'b2#^0h\^J!5'UiG!3'b2#^1h\^J!3+=+^L!2'aO#^1!1'aM!2'@3#:,^6$~RiG$~R!3'b2#^2h\^J!2$_H;R%x;R+2%~RiFiH$SA;R!3'b2#^4h\^J&SA;R!2#1iIvdvd&heq_x;Rvd!2,^3+2iJiKiK&__sat7;R!2'b3iLcM%~R!2'O,5iL%~RcN!2'O,5iM&__sat6;R^A^D&__sat5;R^F^G&__sat4;R^K^N&__sat3;R!2'b3h\cM%~R!2'O,5h\%~RcN!2'O,5iN&H;R!2'a9h\cM%~RcT!3+=+2h\!2'^8!2'a;cMiNiO&H0;R!2'a=h\cM%~RcV!2+M!2'O,5iO!2'PiOcM&H1;R!2'a>h\cM%~RcW!2+M!2'PcMiO!2'OiO,5&H2;R!2'a?h\cM%~RcS!3+=+2iN,5&H3;R!2'a@h\cM%~RcS!3+=+2iOh\&q;RiN+2&r;RiO+2&H4;R!2'a9iLcM%~RcT!3+=+2iL!2'^8!2'a;cMiMiP&H5;R!2'a=iLcM%~RcV!2+M!2'O,5iP!2'PiPcM&H6;R!2'a>iLcM%~RcW!2+M!2'PcMiP!2'OiP,5&H7;R!2'a?iLcM%~RcS!3+=+2iM,5&H8;R!2'a@iLcM%~RcS!3+=+2iPiL&q0;RiM+2&r0;RiP+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UiQ!2'P#[#^L!2+M!2'O!2'^8#@`7iI!2'OiI!2'^8#9`7$~RiQ$~R!2'P#\#^M!2$H14;ReO$H15;RiR&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;Rd2_=&__varmap;Rd4_B&__ff;R!8,`5_C'_O+_P+_P,_Qd9_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2i9d;,_Td<,_U_H!8,`5_C'_O+_P+_P,_QdA_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2i6,_TdB,_U_H!8,`5_C'_O+_P+_P,_QdC_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2dD,`7iS,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2iS,`7dF,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RdG%~R%~RdH!3+=+2iLdI%~RdK%~R%~RdH!3+=+2h\dL%~RdM!2+M!2'OdNiI!2'OiIdOdQ#2#1#Z!2+M!2'O!2'^8iN`7iI!2'OiI!2'^8iM`7!3'b0h\^JiI!3+=+^L!2'aO#^5iU,^6&H;Rvd!6'^?+2iI$z;R+2!3+=4dT!2'@3!2'a;!2'a<g1'b:'b:!6'^?+2#?$z;R+2!3+=4!2'@3iVdT!8'b;+24dYdYiViWd[vd&heq_x;RcLcK&__sat7;R^A^D&__sat6;R^F^G&__sat5;R!2'b3#Be3%~R^\%~Re5!2'O,5!2'a<#De3&__sat4;R!2'b3iIe3%~RiX%~Re5!2'O,5iY&__sat3;R^K^N&H;R!2'a9iIe3%~Re:!3+=+2iI!2'^8!2'a;e3iYiZ&H0;R!2'a=iIe3%~Re<!2+M!2'O,5iZ!2'PiZe3&H1;R!2'a>iIe3%~Re=!2+M!2'Pe3iZ!2'OiZ,5&H2;R!2'a?iIe3%~Re9!3+=+2iY,5&H3;R!2'a@iIe3%~Re9!3+=+2iZiI&q;RiY+2&r;RiZ+2&H4;R!2'a9#Le3%~Re:!3+=+2#M!2'^8!2'a;e3!2'a<#Me3!2'^B#Me3&H5;R!2'a=#Me3%~Re<!2+M!2'O,5e?!2'Pe?e3&H6;R!2'a>#Ne3%~Re=!2+M!2'Pe3eB!2'OeB,5&H7;R!2'a?#Oe3%~Re9!3+=+2!2'a<#Pe3,5&H8;R!2'a@#Pe3%~Re9!3+=+2i[#Q&q0;ReH+2&r0;ReK+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UcYcZ!3+=+2!2'a;#@e3!2'a;#9e3$~RcY$~R!2'P#^0#^N!2$H14;Rc[$H15;Rc\&__arith;R$__p1;Rw$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_Jf:!3,0+_J!2,b<h=f2_;_=&__varmap;Rf>_B&__ff;R!8,`5_C'_O+_P+_P,_QfA_H!8,`5_C'_O+_P+_P,_QfD_H!8,`5_C'_O+_P+_P,_QfE_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QfB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2iS,_TfF,_U_H!8,`5_C'_O+_P+_P,_QfK_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hP,`7fC,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2fC,`;hR,_U_H!8,`5_C'_O+_P+_P,_QfO_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2hP,`7fH,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_RfN_HfQ_U_V%__p1;Rw%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RfR%~RfU%~RfV%~R%~RfS!3+=+2iIfX%~RfY%~R!2+Mi\!2'P#;X%~Rj0%~Ri\%~R!2+M!2'O_P#;#A!3+=+2!2'a;#:e3f[!B#1`0#=#D#^2#^4#^S^H#>#E#B#C#I#J#P#X#3#Z/Hsp;#2#1#[!3+=+2iViW!2'^;3j1!2'_Z#?&heq_x;RcLcK&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uj2j3!2+M!2'O,5#L!2'P#Lg4$~Rj2$~R!2'P#O#^@!2$H4;Rj4$H5;Rj5&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QhX_Hg?_U_V%__x1;R+2%~RhZgA!2#1#Q#J#2#1#M!2'^;3iT!2'_ZiI&heq_x;RcLcK&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uj2j3j6$~Rj2$~R!2'P#O#^@!2$H4;Rj4$H5;Rj5&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7iS,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2iS,`;g>,_U_U_Vj6#1#2#1#Mj7j7!6'^14iU$b;R4!3+=+^L!2'aO#^8#1,^6#2gD#1#2#1#1hI#F#1#:#8#1$~RhD!1$Hw;R!2+Tj8+^0!6'Vj9+^0!2+M!1'a:!3+=7!1#X!2'@3#5^3!3+=+^L!3'`[#Y#W!2'@3#5,Y$~Rj9!1$H;R!3+=0^0#G!8'^10^0$w;R0%C1;R!2'O:#Y%C2;R!2'O!2'^8#Z#YI!2+Mj;j<$C1;R!2'Oj=#X$C2;R!2'Oj>j?&Hx;Rvd&heq_x;Ri2i1&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'UhO`:!2+M!2'O[!2'^8#^8#F!2'P!2'^8#^8#F\$~RhO$~R!2'P#G#^8!2$H4;Ri4$H5;Ri5&__arith;R$__p1;Rw$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R_<_=&__varmap;R_A_B&__ff;R!8,`5_C'_O+_P+_P,_Q_G_H!8,`5_C'_O+_P+_P,_Q_J_H!8,`5_C'_O+_P+_P,_QjA_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_N,`7jB,_U_H!8,`5_C'_O+_P+_P,_Q_S_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j@,`7_T,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`;jB,_U_U_V%__p1;Rw%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~R_W%~R_X%~R!2'O[#3%~R!2'O_Y\%~R_[!2+M!2'O[_\!2'P_\\!:#1`0#^<^H#K#^=#2#3#B#A/Hsp;#2#1#EjCjC!4,[j;j<!@'aF/L;/ar;/IL;/scfg;/HI;/ICok;#^48#^3#^2#^1#^0`K#W#:!3,^2jD!2+M!2'O'aI#:!2'P#:'aJvd&heq_x;R`Q`P&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'U`R`S!2+M!2'O`7#E!2'P#E`8$~R`R$~R!2'P#H#^9!2$H4;R`U$H5;R`V&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QjE_H`>_U_V%__x1;R+2%~RjG`A!2#1#J#A#2#1#FjDvd!3'aK!2'aLjH!1'^T#\!1'aN!2'aO#^1jH&H;R`E`F!2#1!2'aO#^2!1'aM!2'@3#;&a0;R!D'aS/L;/ar;/IL;/scfg;/HI;/ICok;#^58#^4#^3#^2#^1!1'`T#^0#XjI^J!6'^?+2`N$z;R+2!2'O#1jI&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjM$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2`W,`7jP,_U_U_VjM#1#2#1#G`Y`Z!6'^?+2`[$z;R+2!2'OjQ#1&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjR$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7a3,_U_U_VjR#1#2#1#Ga4a5&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hW^T$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjOa6#2#1#G!6'^?1'aX$l;R1!3+<0jT#1!6,aY0jTa;b7vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjU$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7b9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b:,`7jP,_U_U_VjU#1#2#1#G!2+T!2'OjQb;!2'Ob<jI!6,aY0jTa>b6vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjV$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7b>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2b?,`7jP,_U_U_VjV#1#2#1#G!2+T!2'OjQb@!2'ObAjI!6,aY0jTaAb5vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjW$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7bC,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bD,`7jP,_U_U_VjW#1#2#1#G!2+T!2'OjQbE!2'ObFjI!6,aY0jTaDb4vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjX$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7bH,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bI,`7jP,_U_U_VjX#1#2#1#G!2+T!2'OjQbJ!2'ObKjI!6,aY0jTaGb3vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjY$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7bM,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bN,`7jP,_U_U_VjY#1#2#1#G!2+T!2'OjQbO!2'ObPjI!6,aY0jTaJb2vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWjZ$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7bR,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bS,`7jP,_U_U_VjZ#1#2#1#G!2+T!2'OjQbT!2'ObUjI!6,aY0jTaMb1vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWj[$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7bW,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2bX,`7jP,_U_U_Vj[#1#2#1#G!2+T!2'OjQbY!2'ObZjI!6,aY0jTaPb0vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWj\$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7b\,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c0,`7jP,_U_U_Vj\#1#2#1#G!2+T!2'OjQc1!2'Oc2jI!6,aY0jTaSa\vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWk0$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7c4,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c5,`7jP,_U_U_Vk0#1#2#1#G!2+T!2'OjQc6!2'Oc7jI!6,aY0jTaVa[vd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWk1$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7c9,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c:,`7jP,_U_U_Vk1#1#2#1#G!2+T!2'OjQc;!2'Oc<jI!6,aY0jTaYaZvd&heq_x;RjLjK&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Ui4hWk2$~Ri4$~R!2'P#I#^:!2$H4;RjN$H5;RjO&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`I_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2jS,`7c>,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2c?,`7jP,_U_U_Vk2#1#2#1#G!2+T!2'OjQc@!2'OcAjI!2,aZ0jTcBcC!2+M%x;R+2%~Rk3cF!3'b2#^2jI^J!5'Uk4!3'b2#^3jI^J!3+=+^L!2'aO#^3!1'aM!2'@3#<,^6$~Rk4$~R!3'b2#^4jI^J!2$_H;R%x;R+2%~Rk3!3'b1#^6#2,5$SA;R!3'b2#^6jI^J&SA;R!2#1k5vdvd&heq_x;Re1e0&__sat7;R!2'b3k6cM%~R!2'O,5k6%~RcN!2'O,5k7&__sat6;R^A^D&__sat5;R^F^G&__sat4;R^K^N&__sat3;R!2'b3jIcM%~R!2'O,5jI%~RcN!2'O,5k8&H;R!2'a9jIcM%~RcT!3+=+2jI!2'^8!2'a;cMk8k9&H0;R!2'a=jIcM%~RcV!2+M!2'O,5k9!2'Pk9cM&H1;R!2'a>jIcM%~RcW!2+M!2'PcMk9!2'Ok9,5&H2;R!2'a?jIcM%~RcS!3+=+2k8,5&H3;R!2'a@jIcM%~RcS!3+=+2k9jI&q;Rk8+2&r;Rk9+2&H4;R!2'a9k6cM%~RcT!3+=+2k6!2'^8!2'a;cMk7k:&H5;R!2'a=k6cM%~RcV!2+M!2'O,5k:!2'Pk:cM&H6;R!2'a>k6cM%~RcW!2+M!2'PcMk:!2'Ok:,5&H7;R!2'a?k6cM%~RcS!3+=+2k7,5&H8;R!2'a@k6cM%~RcS!3+=+2k:k6&q0;Rk7+2&r0;Rk:+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'UeOeP!2+M!2'O!2'^8#@`7k5!2'Ok5!2'^8#9`7$~ReO$~R!2'P#^1#^O!2$H14;ReQ$H15;ReR&__arith;R$__p3;Rw$__p2;Rw$__p1;Rw$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;Rd2_=&__varmap;Rd4_B&__ff;R!8,`5_C'_O+_P+_P,_Qd9_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,b8+2jSd;,_Td<,_U_H!8,`5_C'_O+_P+_P,_QdA_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_Qd:_H!7,_M_C'_O+_P+_P,_Q!4,_R+2jP,_TdB,_U_H!8,`5_C'_O+_P+_P,_QdC_H!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2dD,`7k;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2k;,`7dF,_U_U_V%__p3;Rw%__p2;Rw%__p1;Rw%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RdG%~R%~RdH!3+=+2k6dI%~RdK%~R%~RdH!3+=+2jIdL%~RdM!2+M!2'OdNk5!2'Ok5dOdQ#2#1#\!2+M!2'O!2'^8k8`7k5!2'Ok5!2'^8k7`7!3'b0jI^Jk5!3+=+^L!2'aO#^7k=,^6&H;Rvd!6'^?+2k5$z;R+2!3+=4dT!2'@3!2'a;!2'a<!2'^;3k>'b:'b:!6'^?+2#A$z;R+2!3+=4!2'@3k?dT!8'b;+24dYdYk?k@d[vd&heq_x;RkCkB&__sat7;R^A^D&__sat6;R^F^G&__sat5;Re7e8&__sat4;R!2'b3k5e3%~RkD%~Re5!2'O,5kE&__sat3;R^K^N&H;R!2'a9k5e3%~Re:!3+=+2k5!2'^8!2'a;e3kEkF&H0;R!2'a=k5e3%~Re<!2+M!2'O,5kF!2'PkFe3&H1;R!2'a>k5e3%~Re=!2+M!2'Pe3kF!2'OkF,5&H2;R!2'a?k5e3%~Re9!3+=+2kE,5&H3;R!2'a@k5e3%~Re9!3+=+2kFk5&q;RkE+2&r;RkF+2&H4;R!2'a9#Ne3%~Re:!3+=+2#O!2'^8!2'a;e3!2'a<#Oe3eB&H5;R!2'a=#Oe3%~Re<!2+M!2'O,5eE!2'PeEe3&H6;R!2'a>#Pe3%~Re=!2+M!2'Pe3i[!2'Oi[,5&H7;R!2'a?#Qe3%~Re9!3+=+2eM,5&H8;R!2'a@#Re3%~Re9!3+=+2eN#S&q0;R!2'a<#Se3+2&r0;R!2'^B#Te3+2&H9;R^O^R&H10;R^S^U&H11;R^V^W&H12;R^X^Y&H13;R^Z^[&q1;R^Q+2&r1;R^L+2!5'Uc[iR!3+=+2!2'a;#@e3!2'a;#9e3$~Rc[$~R!2'P#^2#^P!2$H14;RkG$H15;R!2'P#^4#^R&__arith;R$__p2;Rw$__p1;Rw$__x9;R+2$__x8;R+2$__x7;R+2$__x6;R+2$__x5;R+2$__x4;R+2$__x3;R+2$__x2;R+2$__x1;R+2&__wit;R!3,0+_J!2,b<_6!2,_[!3,_\+2f4!3,_\+2kI!3,_\+2eT!3,_\+2f6!3,_\+2!3,`F+2d1eY!3,_\+2f7!3,_\+2_3_8,`2!3,0+_J!2,b<e\!2,b<f1!2,_[!3,_\+2h:!3,_\+2f4!3,_\+2!2,`0+2}?!3,_\+2!3,`F+2d1kI!3,_\+2eY!3,_\+2f9_8,`2_;_=&__varmap;R!4,`3+2!4,`3+2!4,`3+2f=#:_@#3!4,`3+2!2,_K+2#:#6_@#2!4,`3+2f<#4f;_B&__ff;R!8,`5_C'_O+_P+_P,_QfA_H!8,`5_C'_O+_P+_P,_QfD_H!8,`5_C'_O+_P+_P,_QfE_H!8,`5_C'_O+_P+_P,_Q!8,`5_C'_O+_P+_P,_QfB_H!7,_M_C'_O+_P+_P,_Q!4,_R+2k;,_TfF,_U_H!8,`5_C'_O+_P+_P,_QfK_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j@,`7fC,_UfP_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2fJ,`;_F,_U_H!8,`5_C'_O+_P+_P,_QfO_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2j@,`7fH,_U_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2!3,`6+2fH_F,`7jB,_U_H!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q_R!6,`J_C'_O+_P+_P,_Q#=_HfQ_U_V%__p2;Rw%__p1;Rw%__x9;R+2%__x8;R+2%__x7;R+2%__x6;R+2%__x5;R+2%__x4;R+2%__x3;R+2%__x2;R+2%__x1;R+2%~RfV%~R%~RfS!3+=+2#9!2'^8fT#;%~R%~Re<!2+Mj0!2'P#;e3%~R%~RfS!3+=+2k5!2'^8fW#<%~R!3+=+2#;!2'^8#9#:%~R!2+M!2'O[#<#?%~R!2'P#<#:%~RdP%~R!2'O[#=%~R!2'OE\%~R!2+M!2'O_P#=#E!3+=+2f\!2'a;#=e3!F#1`0!2'P#^4\#=#D#^4#^6#^U#^T^H#>#E#B#C#I#J#P#X#2#3#Z#Y/Hsp;#2#1#^0!3+=+2k?k@dV!2'_Z#A&heq_x;RkCkB&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uj4kJ!2+M!2'O,5#N!2'P#Ng4$~Rj4$~R!2'P#Q#^B!2$H4;RkK$H5;RkL&__arith;R$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_QjE_Hg?_U_V%__x1;R+2%~RjGgA!2#1#S#J#2#1#O!2'^;3k<!2'_Zk5&heq_x;RkCkB&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2!5'Uj4kJkM$~Rj4$~R!2'P#Q#^B!2$H4;RkK$H5;RkL&__arith;R&__wit;R_;_=&__varmap;R_@_B&__ff;R!7,`:_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_I,`7k;,_U!7,_M_C'_O+_P+_P,_Q!4,_R+2k;,`;g>,_U_U_VkM#1#2#1#OkNkN!6'^14k=$b;R4!3+=+^L!2'aO#^:#1,^6#2!1'aMk>#1#2#1#1j<#H#1#<#:#1$~R+^0!1$Hw;R+^0!2'^5!2+M!1'a:!3+=7!1#Z!2'@3#7^3!3+=+^L!3'`[#[#Y!2'@3#7,Y#1#1#1#1#1#1#>%i;R+2%~RQ!2+M!1'a:!3+=7!1#SkO^3!3+=+^L!3'`[#T#RkO,Y&A0;R!6'VkPkQ!2+M!2'O,5#P!2'O!2'^8#P#OkT$~RkP!1$H;R!3+=0U#A!8'^10U$w;R0%C1;R!2'O:#S%C2;R!2'O!2'^8#T#SI!2+M!2'O,5#U!2'O^:kT$C1;R!2'O^9#R$C2;R!2'O!2'^8#S#R^;&__sat7;RkUkV&__sat6;RkWkX&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkY_B&__ff;R!8,`5_C'_O+_P+_P,_Q_M_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7_O,_U_Hk[_U_V%__x2;R+2%__x1;R+2%~R`?%~R!2'Ok\Tl0!4#1#^3#^4#?#>#B#1#6#4#1$~RkQ!1$Hw;R!2+T!3+=0Y#A!2+T!3+=0^0#A+^0!6'VZ^1!2+M!2'O,5#R!2'O!2'^8#R#QkT$~RZ!1$H;Rh@!8'^10Y$w;R0%C1;R^4%C2;R^5!2+M!2'O,5#W!2'OhKkT$C1;R!2'OhJ#T$C2;R!2'O^:hL&__sat7;RkUkV&__sat6;RkWkX&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkY_B&__ff;R!8,`5_C'_O+_P+_P,_QhQ_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7hR,_U_Hk[_U_V%__x2;R+2%__x1;R+2%~RhY%~R!2'Ok\Xl0!4#1#^5#^6#?#>#D#1#8#6#1$~R^1!1$Hw;RhA!6'VhC+^0!2+M!2'O,5#T!2'O!2'^8#T#SkT$~RhC!1$H;Rj8!8'^10^0$w;R0%C1;RhE%C2;RhF!2+M!2'O,5#Y!2'Oj>kT$C1;R!2'Oj=#V$C2;R!2'OhKj?&__sat7;RkUkV&__sat6;RkWkX&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkY_B&__ff;R!8,`5_C'_O+_P+_P,_QjA_H!8,`5_C'_O+_P+_P,_Q!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7jB,_U_Hk[_U_V%__x2;R+2%__x1;R+2%~RjF%~R!2'Ok\\l0!4#1#^7#^8#?#>#F#1#:#8#1$~R+^0!1$Hw;R+^0!2'^5!2+M!2'O,5#V!2'O!2'^8#V#UkT#1#1#1#1#1#1#<!2+Mj4!2'O!2'^8#P#OkT!7'b='?l1#Q#Pvd$i;R+2$Hi;R!2+MP!2'P#1#Q&a0;R!2#4#2#1!2+M!1'a:!3+=7!1#Ul2^3!3+=+^L!3'`[#V#Tl2,Y!5'Ul4!3+=+^L!3'`[#W#Ul3,Y!1'a:!3+=7!3'^Z!2'`[#W#U#V!2'@3!2'^8#T#3^3$~Rl4$~R!3+=+^L!3'`[#X#V!2'@3!2'^8#U#4,Y!2$DEF;R!1'a:!3+=7!1#X!2'@3!2'^8#V#5^3$VIS;R!3+=+^L!3'`[#Z#X!2'@3!2'^8#W#6,Yvd!6'^?+^L,Y$b;R+^L!1'a:!3+=7-^LRN$~R+^L7#12^3!1#[!2'@3!2'^8#Y#8^3#2!3'`[#[#Yl5#1!1'a:!3+=7!3'^Z!2'`[#[#Y#Zl5^3#2#1#1!3'b>l1#Q#P&__sat7;RkUkV&__sat6;RkWkX&__sat5;R^A^D&__sat4;R^F^G&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__p1;Rw$__x1;R+2&__wit;R_;_=&__varmap;R`;_B&__ff;R!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Qg<!6,`J_C'_O+_P+_P,_Q#4_Hg<_U_V%__p1;Rw%__x1;R+2%~R!2+MP#2g@!3#1!2'O!2'^8#^1#^0kT#^1#>&__sat9;RkUkV&__sat8;RkWkX&__sat7;R^A^D&__sat6;R^F^G&__sat5;Rg3g5&__sat4;Rg6g7&__sat3;R^K^N&H;R^O^R&H0;R^S^U&H1;R^V^W&H2;R^X^Y&H3;R^Z^[&q;R^Q+2&r;R^L+2&__arith;R$__p1;Rw$__x2;R+2$__x1;R+2&__wit;R_;_=&__varmap;RkY_B&__ff;R!8,`5_C'_O+_P+_P,_Q!7,`:_C'_O+_P+_P,_Q!6,`J_C'_O+_P+_P,_Q#5kZ_H!7,_M_C'_O+_P+_P,_Q!4,_R+2_T,`7g>,_U_U_V%__p1;Rw%__x2;R+2%__x1;R+2%~R!2+M#3!2'O!2'^8#1#2kT!2'Ok\g4!4#1kG#^2#^3#@#2#1#1#2#1#1#2#1#1#2#1#1").
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
       (Pm5DrvEntry).  The frames below sp that these feed are a few KiB. *)
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1466368 -> MV (Z_to_bv 64 i) = None)
    /\ exitA tid MV.
  Definition exit_preT (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1466368 -> MV (Z_to_bv 64 i) = None)
    /\ exitT tid MV.
  Definition exit_preL (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1466368 -> MV (Z_to_bv 64 i) = None)
    /\ exitL tid MV.

  Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX.dpX_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14509c) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x14509c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 1478340) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 1478240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1478256) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1478208) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1478216) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXe:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14509c) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x14509c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX2_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 1) 0 0 (zero_lines 1%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX3_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 2) 0 0 (zero_lines 2%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preT LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpX4_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 3) 0 0 (zero_lines 3%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_0L : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXL.dpXL_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL:" G end.
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14509c) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x14509c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXL.KS_dpXL; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_2L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL2_pre.dpXL2_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL2_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 1) 0 0 (zero_lines 1%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_3L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL3_pre.dpXL3_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL3_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 2) 0 0 (zero_lines 2%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

  Lemma exit_run_4L : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preL LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1330120 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6953104 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 7084240) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x14538c) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
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
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x169040 <=? a) && (a + Z.of_nat n <=? 0x16a100) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }

    destruct (AS0DRVP_dpXL4_pre.dpXL4_pre_conc fx R MV V) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    all: cbn [V]. all: try solve [xprem SHW EXB XCB DESC].
    1: lazymatch goal with |- srealizes _ _ _ _ => idtac | |- ?G => fail "porta-B: unsolved premise of the exit piece dpXL4_pre:" G end.
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).

    set (good := fun i : Z => i < 1483008 \/ 1486968 <= i < 7084256 \/ 7084280 <= i < 7084800 \/ 7084804 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x14538c) M R1 (Z_to_bv 64 0x14ce10) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }

    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 7086256) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 7086256 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }

    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1478200 /\ (1478200 + 124 <= q \/ q + 32 + 16 <= 1478200 + 120) /\ 1478200 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1478200 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 7086256 (2 * 3) 0 0 (zero_lines 3%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1483008) || ((1486968 <=? a) && (a + Z.of_nat n <=? 7084256)) || ((7084804 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1478200 <= a -> a + n <= 1478200 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1466368 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1478200) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7084240) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 1478232 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 1478240 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1478256 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1478288 8%nat _ SObuf eq_refl)
           (LIT3 1478296 8%nat _ SObufsz eq_refl) (LIT3 7084240 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1478208 8%nat _ SOrpos eq_refl) (LIT3 1478216 8%nat _ SOrend eq_refl)
           (LIT3 1478192 8%nat _ (XCC 16%nat 1478192 8 1477960 eq_refl) eq_refl) (LIT3 1478100 4%nat _ (XCC 17%nat 1478100 4 4294967295 eq_refl) eq_refl)
           (LIT3 1478000 8%nat _ (XCC 18%nat 1478000 8 0 eq_refl) eq_refl) (LIT3 1478016 8%nat _ (XCC 19%nat 1478016 8 0 eq_refl) eq_refl)
           (LIT3 1477968 8%nat _ (XCC 20%nat 1477968 8 0 eq_refl) eq_refl) (LIT3 1477976 8%nat _ (XCC 21%nat 1477976 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x14ce1c) M3 R4 (Z_to_bv 64 0x14509c) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x14509c) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

End Exit.
End FPX_1.
