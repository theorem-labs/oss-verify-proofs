(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require ParseStringXBW_blobs1 ParseStringXBW_blobs2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB CutShC CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsW PmRef PmRefXA PmLibSpecsXAW RelLeaf.      (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Cut_ps_xbothw_T Cut_ps_xbothw_D Cut_ps_xbothw.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PsKitA PsSmA XKitXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PmLibSpecsBLocal.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import ParseStringChkXBW PsAuxXBW PsLeafXBW.      (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseSW Require Import UvZ.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import ParseStringBitsXBW PswSpecsXB PswConvKitXB PswRefKitXB PswTabXB PswTabRXB.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @CUR0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @WLEN]; [@Corelib; @Init; @Datatypes; @list]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @env]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @saddr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @estart]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @edenot]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u32_at]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @flat]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Peano; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @adenot]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @micromega; @VarMap; @Empty]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @adenot_start]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @kentry_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @defined_bytes]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @bytes_at]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @bytes_at_rdn]; [@Corelib; @Lists; @ListDef; @map]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @ex_intro]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @bytes_le_to_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @bytes_le_to_Z_bound]; [@Stdlib; @Lists; @List; @length_map]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundSums; @APSX; @word_to_le_bytes_of_bytes_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @Ex; @ex_un]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u8_at]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @bytes1]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @in_foot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @C_xboth]; [@Corelib; @Init; @Datatypes; @prod]; [@Stdlib; @Lists; @List; @In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @FOOT]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @snd]; [@Corelib; @Init; @Logic; @not]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_rt_static]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @FOOTX]; [@Stdlib; @Lists; @List; @in_or_app]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @LIT_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @LIT_HI]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @ainfr]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_zero]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @fobj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @ainfr_sub]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @apart]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @eghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @kenc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @kenc_nonneg]; [@Corelib; @Init; @Logic; @proj1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_k_per_malloc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_b_lin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_b_overhead]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_cost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KENC0]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_buf]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @eev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KXG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BXG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @r_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @parse_string]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @parser_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_segs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_win]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @VT_PARSER]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @lstr_short]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @VT_FUNC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_level]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_sst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_nst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_more]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @str_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @SLong]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_bcap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_bptr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_sb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_stack]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_scap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_STRING]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PAR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @wf_ps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_ROOT]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Lists; @ListDef; @Forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @is_container]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @handled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @transient]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_EXPECT_COMMA_OR_END]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_NUMBER]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @num_prefix]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @b2z]; [@Stdlib; @micromega; @Tauto; @FF]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WFX]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Lists; @ListDef; @nth]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @esc_need]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @buf_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @winlen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @buf_need]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @lstr_long]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @pcredit_xA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @pcreditA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @kleft]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @bleft]; [@Stdlib; @ZArith; @Zdiv; @Z_div_mod_eq_full]; [@Stdlib; @ZArith; @Zdiv; @Z_mod_mult]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @ev_reg]; [@Corelib; @Init; @Nat; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@stdpp; @bitvector; @definitions; @BV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @E0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_tp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_segs]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @AsanUbsan; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rng_of_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rng_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @g_lbv]; [@Stdlib; @Lists; @List; @incl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rng_incl]; [@Stdlib; @Lists; @List; @incl_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rf_ceil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_sptop]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rf_sptop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @astk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @OV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @infr_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @FS_BYTES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @BIGSHADOW_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @BIGSHADOW_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rf_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @app_mem]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_blocks]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ablock_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframes_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @mod8_of_16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BBX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BCX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ESCN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @VV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibSym; @u64_of_Z]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @unsigned_lit]; [@stdpp; @bitvector; @definitions; @bv_add]; [@stdpp; @bitvector; @definitions; @bv_add_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @uv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uv_add_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @u_lin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @uE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @tden]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @lden]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_scr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @HDECL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SCRV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @NF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @W_parA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @W_encA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @Wo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @ERRCAT_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @ATEXIT_TAB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmIcptIfaceA; @ATEXIT_TAB_BYTES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @in_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @aclientw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @in_shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @infr_wok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_wrs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @in_reg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @shadow_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @sclientA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @aclient]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @in_fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_addr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_class]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @not_stk_shadow_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SHR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @not_stk_shadow_sh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @SB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @shreg_in_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @div8_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_crs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UBC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVPK]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLKC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @elenZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @estart_srl3']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @infr_sh_wok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @aclientw_client]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @shreg_sub]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_l]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_decidable]; [@Stdlib; @ZArith; @Zdiv; @Z_div_plus]; [@Stdlib; @micromega; @RingMicromega; @OpGt]; [@Stdlib; @ZArith; @BinInt; @Z; @gt]; [@Stdlib; @ZArith; @Zdiv; @Z_div_plus_full]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @RFO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLKCo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLKSo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_static_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_rt_ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_ro_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @segs_below_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @segs_below]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @wx_segs_nowrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @wx_nowrap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @SCELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_cells]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @GLO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @GHI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_got_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_got_lo]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @FOOTC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @IMG_RO_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @IMG_RO_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @LIT_NULL_S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @LIT_FALSE_G]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @inW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @infr_clientw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @FOOTCL]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @two64]; [@Stdlib; @ZArith; @Zdiv; @Zplus_mod_idemp_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_lit64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_add64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mkAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @mkAlu_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @eaddz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @eadd]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_sub64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @esub]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@Stdlib; @ZArith; @Zdiv; @Zmult_mod_idemp_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_mul64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mkMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @mkMd_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @escale]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_diag]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@Stdlib; @ZArith; @BinInt; @Z; @divide]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_divide]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_sltu64]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ESCV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @img_clear]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymRun3; @kimg_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @mrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ahid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @vis_def]; [@Stdlib; @Lists; @List; @in_map_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @At]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @GT; @t0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UWL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @client_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @aclient_incl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @visr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @aclient_scr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @defined_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_frm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @PM_FS_CLASSES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ff_remove]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_upper_bound]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Stdlib; @setoid_ring; @Algebra_syntax; @equality]; [@Stdlib; @setoid_ring; @Ncring; @eq_notation]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @BinNums; @PosDef; @Pos; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pos_sub]; [@Stdlib; @setoid_ring; @Ncring_initial; @Zops]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Stdlib; @setoid_ring; @Ncring; @ring_plus_comp]; [@Stdlib; @setoid_ring; @Ncring_initial; @Zr]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@Stdlib; @ZArith; @BinInt; @Z; @div_add_l]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_comm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_small_high]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @SCFG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_nodup]; [@stdpp; @base; @NoDup]; [@stdpp; @base; @elem_of]; [@stdpp; @base; @list_elem_of]; [@stdpp; @list_relations; @list; @NoDup_cons]; [@stdpp; @base; @list_elem_of_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @in_lb_remove_neq]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @ec_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @u32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @OBJ_JSON_CATEGORY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @ls_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @img_ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @atexit_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ls_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @foot_pristine]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @loc_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @errcat_guard]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @byte_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kword64_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u64_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @visr_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @kword32_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u32_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @kword8_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u8_vis]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @shz_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @byte_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KZero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @regs_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @know_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @regs_ok_id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KUnk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KIMG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @static_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @NF32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SCOK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @GOTOK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @SLOT2]; [@Corelib; @Classes; @RelationClasses; @reflexivity]; [@Corelib; @Classes; @RelationClasses; @PreOrder_Reflexive]; [@Stdlib; @ZArith; @BinInt; @Z; @le_preorder]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @ISH2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @kzero_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @vis_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kwr_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @krange_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kalign_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kdisj_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVS2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kunk_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kblob_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @bytes_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVCH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ind_valn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ESCV2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @akept]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @outside]; [@Stdlib; @Lists; @List; @in_app_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WCL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AP1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AP3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KSHO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @stksh_rng]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AL8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @NLIT]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @GLOC_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @GLOC_PTR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @SYSCAT_GUARD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @NEED_LOCKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @LOCALE_LOCK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibStaticsA; @PMTA; @C_xboth_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibStaticsA; @PMTA; @consts_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibStaticsA; @PMTA; @cell_in_foot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @in_tab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @IMGCL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @blk0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @blk1]; [@Stdlib; @ZArith; @BinInt; @Z; @log2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @bufcredA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @bcapI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @stk_kx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @scapI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @stk_bx]; [@Stdlib; @ZArith; @BinInt; @Z; @log2_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_nonneg_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @pstate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @stk_pot_nonneg]; [@Corelib; @Init; @Logic; @iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KXG0]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_add_distr_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_add_distr_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @FIXA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ecv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @LS2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @xfoot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @kind_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @depth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @g_es]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ECV]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XIj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @xinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @GF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @lits_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @xfoot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @xinv_keep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @lits_inside_xboth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @LBr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LBV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @okV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @HDECL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @ctrl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_sst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @CPX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_cp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @CP2X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_cp2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @SIZX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @PTRX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @TAGX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @ckind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SSTEP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @STEXT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SATC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SU8C]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SU4C]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SRET4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SERR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SESV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SRETX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SIM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymRun3; @env_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @expr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @uv_agree]; [@Corelib; @Init; @Peano; @lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uvA]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @lowcells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @lowcells_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @CPL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LOWC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @TAGL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @bytes_at_frame]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KStep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KText]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @same_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @same_cells_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @NOF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uvV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @CPL_same]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFL_same]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @TAGL_same]; [@Stdlib; @Lists; @List; @forallb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @plain]; [@Corelib; @Lists; @ListDef; @skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @curform]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVRw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @CUR0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @ADD]; [@Stdlib; @Lists; @List; @existsb]; [@Stdlib; @Lists; @List; @Forall_forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @H_off_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @hasb]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @has_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @jlt_fact]; [@Stdlib; @Bool; @Bool; @orb_prop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @lt_fact]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @has_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @SLTUE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @ENDE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @uv_sltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @curform_val]; [@Stdlib; @ZArith; @ZArith_dec; @Z_le_gt_dec]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KFill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @kword8_elim]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @has_cell_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u8_full]; [@Stdlib; @Lists; @List; @nth_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RelLeaf; @RLF; @u8_at_mod]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Stdlib; @Lists; @List; @firstn_skipn]; [@Corelib; @Init; @Nat; @min]; [@Stdlib; @Arith; @PeanoNat; @Nat; @min]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_min]; [@Stdlib; @ZArith; @BinInt; @Z; @min_spec]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @Lists; @List; @length_firstn]; [@Stdlib; @Lists; @List; @firstn_firstn]; [@Stdlib; @Lists; @List; @firstn_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @stepping]; [@Stdlib; @Arith; @PeanoNat; @Nat; @lt_ge_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KTAB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KBad]; [@Stdlib; @Lists; @List; @nth_overflow]; [@Corelib; @Lists; @ListDef; @seq]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Lists; @List; @forallb_forall]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Lists; @List; @in_seq]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @tokn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun_plain]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @firstn_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @CT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_nst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_more]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_level]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_stack]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_dlen]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @u8_feeds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @c_u8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @sres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @sdesc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @cpu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @sdesc_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xstep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @appu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @res]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xfin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @err]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @end_string]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @hexv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @is_high_surr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_SP1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @ret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_TEXT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @core_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @tok_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @utf8_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @pair_cp]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @parse_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @is_hex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @hexval]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @hexval_digit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @hexval_lower]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @hexval_upper]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @hexval_none]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_nx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @cutn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @cut_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KEntry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KAtc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @A0X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @ECVX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @bufkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @szc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @szok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KConv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @b256]; [@Stdlib; @Lists; @List; @app_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @b256_id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @b256_idem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @b256_app]; [@Stdlib; @Lists; @List; @Forall_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun_inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @winb_inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @length_b256]; [@Stdlib; @Lists; @List; @length_app]; [@Corelib; @Lists; @ListDef; @repeat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FR]; [@Stdlib; @Lists; @List; @nth_repeat_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FFS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @blocks]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @BLS]; [@Stdlib; @Lists; @List; @hd]; [@Stdlib; @Lists; @List; @tl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KSm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @okV_def0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @okV_defup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @aambV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @Cred]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @frame00]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @IH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @CPS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @ambV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XIW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @fp_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @ih_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @Wo_okV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WOKo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @CRS_okV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @CRS_OKo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @aamb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @amodel_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @model_rt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ri_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @curB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @curF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @ffroom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @bptrI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @sbI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @FE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @den]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @bls_i]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @denF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ffs_i]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @rf_frm]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @mod8_of_64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cutpoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @post_spec]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Stdlib; @Lists; @List; @nth_error]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @leaf_factsA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @leaf_agree0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @NF_le]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @dummy_cp]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb_le]; [@Stdlib; @Lists; @List; @nth_error_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @eb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @FLE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @outU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @lfa_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @lfa_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @cpf_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_F]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @G; @CPS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @cpf_all]; [@Stdlib; @Lists; @List; @nth_error_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @region_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @UREGS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @expr_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @SRL3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @SBz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FLR]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FLE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @shadow_blk_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_bottom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @BLKW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @xfoot_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @ENC_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LITCL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @FLF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FRM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @LEAFK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @sh_apart2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ps_set_win]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @PS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @out]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @u64_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @u32_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @u8_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @lstr_short_nil_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @bytes_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ILV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @shadow_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AGFIX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @STR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @str_long_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @shadow_blk_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STATIC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @LS0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @ls_ok_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STATIC_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PTKF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @ec_at_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PH0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @EC_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @LS_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PHA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PH0_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PHS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @F0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @FRM3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CPF_N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CPF_NM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CPF_MM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @MORE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CPF_E]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CPF_X]; [@Stdlib; @Lists; @List; @nth_error_Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @len_cps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @G; @BLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @blv_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @den_agree]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ext_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @blob_val]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @subst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @is_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @TAGS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TGoto]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @tag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_PSS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @G; @TAGS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @leaf_chkA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @GT; @NF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @G; @HDECL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @heap_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @foot_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @bsubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @frames_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @fsubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_over]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @den_bsubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @leaf_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @GBLK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @BLKAG]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @slook]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @Env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @prove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @fact_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @PsKitA; @PPVA; @prove3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSound; @APS; @fact_ok_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @PsKitA; @PPVA; @prove3_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KDecl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @AtV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @over_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @POSTP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ESVP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KEntry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KRetx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KPushb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KAppend]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KConvert]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KAtc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PROVE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ecv_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KErrh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KSetec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KEsv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFEOUT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @AGFIX_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STR_eqv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STR_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @POUT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OUT_N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @leaf_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @goto_common]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @NCUT]; [@Corelib; @Init; @Datatypes; @orb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @kind_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @goto_decl_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @goto_retx_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @regions_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @cpf_of_kind]; [@Corelib; @Init; @Datatypes; @negb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @regions_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @DECL_CORE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @kind_eqb_eq]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @bytes_le_Z_to_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u64_full]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @kword64_elim]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAutoX; @CAX; @cell_at]; [@Stdlib; @Lists; @List; @find]; [@Stdlib; @Lists; @List; @find_some]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ESC_NEED]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @exit_ok0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @exit_err]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CUR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @isSome]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @G; @RETS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ret_of_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @RETS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_SM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_PUSHB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_APPEND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_CONVERT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_ATC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_ERRH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_SETEC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CUR0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @WEND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @BX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @amb_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LYB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5LazyA; @L5LZ; @sbm_ahid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @lfa_sbm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @RD64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @cell_at_has]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @U64INJ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UVR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @edenot_agree_AP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @lfa_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FRAME00]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @PDEFM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uv_esub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SUBR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @cur_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @progress_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @bound_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @RD8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uv_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uv_eaddz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @uv_eadd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @esc_need_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @MODB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @sst_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @parser_sh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WINOK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @not_retreated]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @consumed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @win_exhausted]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @key_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PSX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @shadow_cont]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @shadow_cont_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WF_mk]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @key_inv_same]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFE2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @win_okA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFEOUT2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OUT_E]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @u8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @def_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @key_inv_setwin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XKEEP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @XOUT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @EOUT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @ECINJ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @XRNG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @XK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OUT_0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PA_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @ambX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCertA; @CCA; @leaf_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @AMBX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @leaf_okV_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @vis_off_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @cutn_is']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SZC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SIM_same]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WBUFZ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @b256_eq_of_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @wf_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @u8_at_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @u64_at_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @b256_eq_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3s]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @r_code]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @estate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @es_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @r_evs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @r_allow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmEncSpecs; @PMES; @g_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @ind_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRefXA; @PMRXA; @rm_matchA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @r_ctrl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @r_used]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXAW; @PMXAW; @win_bytesA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @w_after]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRefXA; @PMRXA; @the_rmA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @rm_core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @u8v]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @u8_init]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @u32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @u8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u32_full]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @kword32_elim]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @tagcP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @cellv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @cellv_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @u8_at_b256]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @row]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_sid]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_j]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_i]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ROWS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @RETPC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @PC_ESV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TOther]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @leaf_okV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @exit_base_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @reg_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @call_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @find_row]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @row_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KZB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @KZT]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @find_row_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @rows_ok2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @LEAFV_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @rows_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LYI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LYR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LYN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @STKF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SCRP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WINC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WOKV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WRS_OK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @WLEN]; [@Corelib; @Init; @Datatypes; @comparison]; [@Corelib; @Init; @Datatypes; @Lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShB; @CSL1; @site_chk1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_rd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_rs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @sites_ok_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @sites]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShA; @CSL; @shl_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_cur]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_a]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @goto_amb_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @r_tab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @tab_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutShC; @CSLR; @text_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @GXD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rows_kinds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_csl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @wl_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WSAME]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @LBVE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @LEAF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @KRETX28]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @retx_nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @CP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @PS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @region]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_D; @cp28]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @ambXV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @meas]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @IHV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutRtA; @CRA; @exit_retire]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @DEF0V]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @EV0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @is_ret_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ret_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @retire_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @retx_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FLV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @regs_preserved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @ahpres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @ahpres_rebase]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OUT_X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @POSTP_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @lits_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @enc_sync]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WWX]; [@Corelib; @Classes; @Morphisms; @flip2]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @iff_flip_impl_subrelation]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @pcredit_bufcred]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @reg_of_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @w3s_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFE0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @in_shadow_mono]; [@Stdlib; @Lists; @List; @filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ret_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @cinfo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @custom_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @GT; @SCELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @GT; @GLO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @GT; @GHI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @sm_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_nx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_csp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @phase0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @callee]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @NEWS_F]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @SETEC_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @EE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ATC_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ATC_NEWS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @gof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @STR_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @STR_NEWS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @size_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @CONV_NEWS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @JV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ESV_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @WENC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ESV_NEWS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @VE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ret_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @IMGHI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @PsSmA; @CRX; @smalloc_leaf_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @CRSV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @IMG_OK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @DEFUPV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ISHL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @SMUSER]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_scr_stack_malloc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_stack_malloc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @static_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutRtA; @CRA; @smalloc_fact_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutRtA; @CRA; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutRtA; @CRA; @sm_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @aly_scr_sm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_SM]; [@Stdlib; @Lists; @List; @filter_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLK0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BLK29]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @cell_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @aheap_pres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx_a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx_ghost]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @ISH2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @ACL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SAFEOUT0]; [@Stdlib; @Lists; @List; @incl_tl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @K29]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @XOUT0]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @fs_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_flagptr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @wf_fs_def]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @vis_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @stksh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @stksh_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmAsanKit; @PtKitA; @PTA; @stksh_ag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KSTK]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @find_segment]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @seg_readable]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @segment_read_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @seg_bytes]; [@Stdlib; @ZArith; @BinInt; @Z; @to_N]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @seg_base]; [@Stdlib; @NArith; @BinNat; @N; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @find_segment1_none_above]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @STCL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @CSET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OSET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FIX_CSET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PHS_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PHA_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @flc_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @retbls_k]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PHASE_X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @KEEP_PH]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @RETBLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @auxp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @aux_ok]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @PHASE0_X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @callee_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @common_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutBridgeA; @CBA; @cps_asanG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reglist]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @NCS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @ra_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @ffrs]; [@Stdlib; @ZArith; @Zdiv; @Z_div_mult]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @a1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @ainfr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @estart_srl3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @u8_byte_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @U8DEF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @RBLK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @ACLI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @KEEP_FS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OSET_CSET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_errh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @G; @RETS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @oeqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @size_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @NEWSF]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FL64]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRA]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @fobj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @stksh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @SETEC_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @ls_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @ec_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STKSH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @OSET_OUT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @GD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @AXT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_setec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KSetEc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @allb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @admlist]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @BV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @sim_stepping]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WINB_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @WBYTE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @sim_serr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @allb_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RelLeaf; @RLF; @byte_adm_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @common_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @regs_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sr_fresh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @caller_saved]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blk_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @frames_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @frm_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapA; @CHA; @kept_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @a2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @a3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @ATC_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswSpecsXB; @PSWS; @sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_atc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @hexst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @V]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @cparg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @cpin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @CPL_sameN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFL_sameN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @TAGL_sameN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSound; @APS; @ext_list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retE_a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @hex_some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @sx32_eqm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U5]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U4]; [@Corelib; @Init; @Datatypes; @option_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @EXT4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U6]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @uv_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmParseSW; @UvZ; @UVZ; @sx32]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @sx32_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @uv_ext04]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @sx32_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @hex_none]; [@Stdlib; @ZArith; @Zbitwise; @Z; @add_lor_land]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_mono]; [@Stdlib; @ZArith; @BinInt; @Z; @div_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @lor7]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @grow_cap]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_compat_l]; [@Stdlib; @ZArith; @BinInt; @Z; @div_div]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_lower_bound]; [@Stdlib; @micromega; @EnvRing; @Pinj]; [@Stdlib; @micromega; @EnvRing; @PX]; [@Stdlib; @ZArith; @BinInt; @Z; @log2_le_mono]; [@Stdlib; @ZArith; @BinInt; @Z; @log2_double]; [@Stdlib; @ZArith; @BinInt; @Z; @succ]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_div_le]; [@Stdlib; @micromega; @RingMicromega; @PsatzLet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @acredit_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @adebit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @grow_cap_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @log2_halves]; [@Stdlib; @micromega; @RingMicromega; @PsatzSquare]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg_l]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_le_mono_nonneg_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_succ_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @retbls_s]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PsAuxXBW; @PSX; @sng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @STRS_mv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UV_esub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UV_eaddz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @str_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @STR_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @str_grownA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @bufcredA_push]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSound; @APS; @know_ok_agree']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UV_mul2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @ACLX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @FIX_OUT224]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL5]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL6]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL7]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL9]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL10]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL11]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL12]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL13]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL14]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL15]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL16]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL17]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL18]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL19]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL20]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL21]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL22]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL23]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL24]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL25]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL26]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL27]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_T; @BL28]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL29]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL30]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL31]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL33]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL34]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL35]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p0; @BL36]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL37]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL38]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL39]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL40]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL41]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL42]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL43]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p1; @BL44]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL45]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL46]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL47]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL48]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL49]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL50]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL51]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p2; @BL52]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL53]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL54]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL55]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL56]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL57]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL58]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL59]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p3; @BL60]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R1p4; @BL61]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL62]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL63]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL65]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL66]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL67]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL68]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p0; @BL69]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL70]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL71]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL72]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL73]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL74]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL75]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL76]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p1; @BL77]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @Cut_ps_xbothw_R2p2; @BL78]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_push]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_ESC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @retcells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @UKeep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WBUFID]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @xrun_o_inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFB_norm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xstep_inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun_snoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @firstn_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @is_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @zalu_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @unlin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lmerge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ladd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lscale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @shamt_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @size_of_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFB_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @BUFB_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @bytes_at_b256]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @USet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @UHex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UV_escale2]; [@Stdlib; @Lists; @List; @length_skipn]; [@Stdlib; @Lists; @List; @nth_skipn]; [@Stdlib; @Lists; @List; @nth_firstn]; [@Corelib; @Init; @Datatypes; @list_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @sr_vars_lt_forallb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reg]; [@Stdlib; @Lists; @List; @in_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @str_src_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @aacc]; [@Corelib; @Program; @Basics; @flip]; [@Corelib; @Classes; @RelationClasses; @flip_Reflexive]; [@Corelib; @Classes; @RelationClasses; @impl_Reflexive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @bytes_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5A; @CL5A; @defined_same]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutRtCpsA; @CRC; @aacc_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @nodup_notin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @REGV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @RUNS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @RUNL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @RUNL1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @exh_fact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UV_eadd]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Stdlib; @ZArith; @Zdiv; @Z; @mod_mod_divide]; [@Stdlib; @micromega; @Tauto; @TT]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @zlb_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @u32_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @CONVERT_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_conv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KRet4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @cellb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @PAIRX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @cellb_cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @ORE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @SRLE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @MULE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @ANDE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @cellv_cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @utf8_of_inb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @pair_sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @pair_cp_low]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @atom_pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @atom_t1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SU8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SErr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @E_INVALID_UESC]; [@Stdlib; @Lists; @List; @Forall_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @rm_ctrl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @callee_leafV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @DEF0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @text_inA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_esv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KEsv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @someb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @hasr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SEnd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @skipn_nth_cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @xrun_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @TOK0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @of_text]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @Forall_firstn_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @Forall_skipn_Z]; [@Stdlib; @Lists; @List; @app_nil_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @tokn_tok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @bytes_at_first]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @bytes_at_skip]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @uv_add]; [@Stdlib; @Lists; @List; @Forall_impl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @set_tok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @TAGC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @end_string_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @q_code]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @q_c]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @evk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @q_evs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @q_al]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @q_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @cres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @r_of0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @rm_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @FEndStringValue]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @a4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @ESVXA_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @VIS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @parser_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @parser_sh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @wf_ps_stale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @win_okA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @buf_bound_stale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @vis_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @rm_stale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXAW; @PMXAW; @wroomr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @inp_aux]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_EXPECT_COLON]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @ST_ACCEPT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @rm_match]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @vis_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefs; @PML; @wf_ps_stale_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @VT_VISITOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @KSQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXAW; @PMXAW; @wroom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @RR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @ex_u32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @S2E]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringChkXBW; @PSA; @LITLO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @EVW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @VIEWM]; [@Stdlib; @Lists; @List; @skipn_skipn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @ACLP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @VIEWB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @u32_at_eqm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @kdecl_lab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @over_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_KIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @xkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @RD32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @KRetx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_SRC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_goto_step]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @keep_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @needs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @JM1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @tag_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @buf_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @sboform]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @upd_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @KD_retx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @kstep_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @has]; [@Stdlib; @Lists; @List; @firstn_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @UVO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @VIEW_RM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @CPC]; [@Corelib; @Init; @Datatypes; @andb_true_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3_exh]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3_err]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_goto_atc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @fe_hs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @katc_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @is_ctl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @E_ILLEGAL_CTL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @E_CHAR_IN_STRING]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SGo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @E_ILLEGAL_ESC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SU4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @E_SURR_PAIR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @SNone]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U3]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_SP2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmRef; @PMR; @SS_U7]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @rb_goto_other]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @core_eq_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3_ret]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @WINSFX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @cfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @ckind_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @KENTRY29]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @BUFL29]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @lab_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @u32_at_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @oeqb_some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @hexval_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @hs_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringBitsXBW; @PSBT; @f_hs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @uv_JM1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @TGT_BUFL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @TGT_TAGL]; [@Stdlib; @Bool; @Bool; @andb_false_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @sdesc_hex]; [@Stdlib; @Bool; @Bool; @orb_false_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswConvKitXB; @PCVK; @lit_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @NEG]; [@Corelib; @Classes; @RelationClasses; @iff_Transitive]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @KEEPC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @NEEDS57]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @NEEDS58]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @sboform_val]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub_diag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @sdesc_text]; [@Stdlib; @Lists; @List; @forallb_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabRXB; @PSWR; @sdesc_keep]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3_end]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @wl_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @ckind_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @lres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @goto_other_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @goto_step_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @goto_atc_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_ENTRYX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_EXH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_ATCX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_RET4X]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_SETECX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_ESVX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @LBad]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @LOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_ENTRY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_STEP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @AmbV; @SG_ATC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswTabXB; @PSW; @tagc_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @UVBP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XINV0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @cert_soundV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @plan_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @plans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @tags_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @GK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @G_CRED]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @GX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @G_DECL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @G_RETX_ESV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @G_RETX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @S_GOTO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_EXIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_SM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_ERRH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_SETEC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_ATC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_PUSHB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_APPEND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_CONVERT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_ESV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @L_CSL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @G; @cp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @At0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @ambV_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeapV; @CHV; @okV_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5LazyA; @L5LZ; @sbm_model_rt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @ffs_0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @XI0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PsMain; @SIM0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @ScfgP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asan_layout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asan_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asan_statics_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asan_iface]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @icpt_layout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @asan_iface_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm5L5DefsA; @L5A; @as0_layout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @rt_img_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @icl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibDefsA; @PMLA; @in_footx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswSpecsXB; @PSWS; @atc_specXAW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_ATC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswSpecsXB; @PSWS; @convert_specXAW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_CONVERT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @str_push_back_specA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_PUSHB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @str_append_specA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_APPEND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @errh_specA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_ERRH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @set_ec_specA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_SETEC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @enc_agreeP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @bencP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXAW; @PMXAW; @end_string_value_specXAW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGen; @XKitXA; @XKA; @VISD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @PSA0; @PC_ESV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @PFXA_SCR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @DPSXA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsA; @PMSA; @cur_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @FParseString]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsW; @PMW; @inp_win]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @key_ok_of_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXA; @PMXA; @key_ok]; [@Stdlib; @ZArith; @BinInt; @Z; @le_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @ex_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @ex_u8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @ParseStringXBW; @main]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutGenW; @PswRefKitXB; @PSKW; @w3s_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmLibSpecsXAW; @PMXAW; @parse_string_specXAW]].
      (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module GT := PSA.GT.
Module G := PSA.G.
Abbreviation RSEGS := Pm5PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).

Module PSA0.
Definition PC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_001 ())).         (* [comment removed for export] *)
Definition PC_SM : Z := 420020.      (* [comment removed for export] *)
Definition PC_ATC : Z := 922968.     (* [comment removed for export] *)
Definition PC_CONVERT : Z := 923544. (* [comment removed for export] *)
Definition PC_PUSHB : Z := 1056004.   (* [comment removed for export] *)
Definition PC_APPEND : Z := 1055420.  (* [comment removed for export] *)
Definition PC_SETEC : Z := 842884.   (* [comment removed for export] *)
Definition PC_ESV : Z := 919748.     (* [comment removed for export] *)
Definition PC_ERRH : Z := 852452.    (* [comment removed for export] *)
Definition RETPC : Z := 900692.      (* [comment removed for export] *)
Definition SBz : Z := 2147450880.
Definition IMGHI : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_002 ())).     (* [comment removed for export] *)
Definition SLOT2 : Z := 1436240.     (* [comment removed for export] *)
Definition ISH2 : Z := 2147630410.   (* [comment removed for export] *)
Definition GD : Z := 6946368.        (* [comment removed for export] *)
Definition AXT : Z := 7084256.       (* [comment removed for export] *)
Definition SCR : Z := 16896.         (* [comment removed for export] *)
Definition S2E := EVar 49.           (* [comment removed for export] *)
Definition LITLO : Z := 6946376.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PE := EVar 10. Definition CUR0 := EVar 11. Definition VE := EVar 12. Definition EE := EVar 13.
Definition WLEN := EVar 32. Definition BX := EVar 33. Definition K0 := EVar 34. Definition SIZE0 := EVar 35. Definition P0 := EVar 36. Definition SBX := EVar 37. Definition SLEN := EVar 38.
Definition SCAP := EVar 39. Definition LVL := EVar 40. Definition SST0 := EVar 41. Definition NST := EVar 42. Definition DONE := EVar 43. Definition CP0 := EVar 44. Definition CP20 := EVar 45.
Definition POS0 := EVar 46. Definition CH := EVar 47. Definition ESC0 := EVar 48. Definition FLE := EVar 50. Definition FE := EVar 55.
Definition WEND : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_003 ())).
End PSA0.
Import PSA0.

Definition hid (P : Prop) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_004 ())).
(* [comment removed for export] *)
Lemma kword32_intro : forall segs E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at segs M A z -> kentry_ok segs E M (KWord a 4 v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_005 ())).
Qed.

(* [comment removed for export] *)
Section Ex.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Lemma ex_un : forall (M : mem) a (n : nat), (n <= 8)%nat -> L5.defined M a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists v, 0 <= v < 2 ^ (8 * Z.of_nat n) /\ rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_006 ())).
Qed.
Lemma ex_u32 : forall (M : mem) a, L5.defined M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 32 /\ L5.u32_at segs M a v.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_007 ())).
Qed.
Lemma ex_u64 : forall (M : mem) a, L5.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_008 ())).
Qed.
Lemma ex_u8 : forall (M : mem) a, L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists v, 0 <= v < 2 ^ 8 /\ L5.u8_at segs M a v.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_009 ())).
Qed.
End Ex.

Section PsMain.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL0 : icpt_layout.
Abbreviation IC := PMLA.C_xboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis ISH : rt_img_shadow L IL0 HI.
Hypothesis POI2 : Forall (fun r : Z * Z => SLOT2 + 8 <= fst r \/ snd r <= SLOT2) (icl_poison IL0).
Hypothesis FOOTXC : forall a, PMLA.in_footx IC a -> ~ hl_rt_static L a.            (* [comment removed for export] *)
Lemma FOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_010 ())).
Qed.
Hypothesis SM1 : hl_stack_malloc L 1 = PC_SM.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis ATC_OKW : PSWS.atc_specXAW L ar HI IC PC_ATC.              (* [comment removed for export] *)
Hypothesis CONVERT_OKW : PSWS.convert_specXAW L ar HI IC PC_CONVERT.      (* [comment removed for export] *)
Let ATC_OK : PMSA.append_to_codepoint_specA L ar HI IC PC_ATC := PSWS.atc_x_of_w L ar HI IC PC_ATC ATC_OKW.
Let CONVERT_OK : PMSB.convert_specA L ar HI IC PC_CONVERT := PSWS.convert_x_of_w L ar HI IC PC_CONVERT CONVERT_OKW.   (* [comment removed for export] *)
Hypothesis PUSHB_OK : PMSA.str_push_back_specA L ar HI PC_PUSHB.
Hypothesis APPEND_OK : PMSA.str_append_specA L ar HI PC_APPEND.
Hypothesis ERRH_OK : PMSA.errh_specA L ar HI PC_ERRH.
Hypothesis SETEC_OK : PMSA.set_ec_specA L ar HI IC PC_SETEC.
(* [comment removed for export] *)
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variable benc : PMES.eghost -> Z.
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.
Hypothesis ENC_AGREE : PMXA.enc_agreeP enc_invA.                                  (* [comment removed for export] *)
Hypothesis BENC0 : PMXA.bencP benc.                                               (* [comment removed for export] *)
Variable CLA : Z.                                                                   (* [comment removed for export] *)
Hypothesis ESV_OKW : PMXAW.end_string_value_specXAW L ar HI IC enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PC_ESV.     (* [comment removed for export] *)

(* [comment removed for export] *)
Variables (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P V E SQ B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate) (eg : PMES.eghost).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet).
Variables (p e : Z).
Let LB := PML.ps_blocks ps ++ LBo.
Let LBG := LB ++ PMES.g_lbv eg.      (* [comment removed for export] *)
Hypothesis HH : ri_inv HI LBG FF LK cr A M (vml_of model).
Hypothesis Hmo : CHA.amodel_ok A model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PMSA.fp_ok fx.
Hypothesis Hra : getr R 1%bv = Z_to_bv 64 r.
Hypothesis Hraok : L5.ra_ok r.
Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 sp.
Hypothesis Htp : getr R 4%bv = Z_to_bv 64 (hl_tp L).
Hypothesis Hstk : CHA.astk ar M sp SCR.
Hypothesis Hroom : CHA.ffroom FF LK 10.      (* [comment removed for export] *)
Hypothesis Hffrs : CHA.ffrs FF sp.
Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 P.
Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 p.
Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 V.
Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 E.
Hypothesis Hwin : PML.ps_win ps = Some (p, e).
Hypothesis HMORE : PML.ps_more ps = true.
Hypothesis HST : PML.ps_st ps = PML.ST_STRING.
Hypothesis HKEY : PMXA.key_ok ps.      (* [comment removed for export] *)
Hypothesis Hsp32 : sp mod 32 = 0.
Hypothesis Hstksh : PMLA.stksh ar M sp SCR.
Hypothesis HPA : PMLA.parser_at (hl_segs L) IC M P ps.
Hypothesis HPSH : PMLA.parser_sh M ps.
Hypothesis HWF : PML.wf_ps ps.
Hypothesis HWIN : PMLA.win_okA M LBo ps.
Hypothesis HBB : PML.buf_bound ps B.
Hypothesis HBM : B <= Z.of_nat (length (PML.ps_buf ps)) + PML.winlen ps + PML.buf_need ps.      (* [comment removed for export] *)
Hypothesis HVIS : PMLA.vis_at (hl_segs L) IC M V.
Hypothesis HEC : PMLA.ec_at (hl_segs L) IC M E 0.
Hypothesis HLS : PMLA.ls_ok (hl_segs L) IC g M.
Hypothesis HG : g <> PML.LS0.
(* [comment removed for export] *)
Hypothesis HINV : enc_invA M V SQ eg.
Hypothesis HLIT : PMXA.lits_ok L IC M.
Hypothesis HSYNC : PMXA.enc_sync ps eg.
Hypothesis Hkx : 0 <= kx.
Hypothesis Hbx : 0 <= bx.
Hypothesis HPC : PMLA.pcredit_xA L cr ps (kx + PMXA.kenc L eg) (bx + benc eg).
(* [comment removed for export] *) Remark HROOMS_gone : True. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_011 ())).
Qed.      (* [comment removed for export] *)
Hypothesis OP : PMLA.fobj M FF P 272.
Hypothesis OVX : PMLA.fobj M FF V 408.
Hypothesis OE : PMLA.fobj M FF E 16.
Hypothesis OS2 : PMLA.fobj M FF SQ 24.
Hypothesis AP1X : PMLA.apart P 272 V 408.
Hypothesis AP2 : PMLA.apart P 272 E 16.
Hypothesis AP3X : PMLA.apart V 408 E 16.
Hypothesis AP4 : PMLA.apart P 272 SQ 24.
Hypothesis AP5 : PMLA.apart V 408 SQ 24.
Hypothesis AP6 : PMLA.apart SQ 24 E 16.
(* [comment removed for export] *)
Lemma OV : PMLA.fobj M FF V 8.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_012 ())).
Qed.
Lemma AP1 : PMLA.apart P 272 V 8. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_013 ())).
Qed.
Lemma AP3 : PMLA.apart V 8 E 16. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_014 ())).
Qed.
Definition KXG (g1 : PMES.eghost) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_015 ())).      (* [comment removed for export] *)
Definition BXG (g1 : PMES.eghost) : Z := bx + benc g1.
Lemma KENC0 : forall g1, 0 <= PMXA.kenc L g1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_016 ())).
Qed.
Lemma KXG0 : forall g1, kx <= KXG g1 /\ bx <= BXG g1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_017 ())).
Qed.
(* [comment removed for export] *)
Variables (cp0 cp20 pos0 esc0 ch : Z) (winb : list Z).
Hypothesis Hcp0 : L5.u32_at (hl_segs L) M (P + 148) cp0.
Hypothesis Hcp20 : L5.u32_at (hl_segs L) M (P + 152) cp20.
Hypothesis Hpos0 : L5.u64_at (hl_segs L) M (P + 168) pos0.
Hypothesis Hesc0 : L5.u8_at (hl_segs L) M (P + 220) esc0.
Hypothesis Hcpr : 0 <= cp0 < 2 ^ 32 /\ 0 <= cp20 < 2 ^ 32 /\ 0 <= pos0 < 2 ^ 64 /\ 0 <= esc0 < 2 ^ 8.
Hypothesis Hwinb : L5.bytes_at (hl_segs L) M p winb /\ Z.of_nat (length winb) = e - p.
Hypothesis HCH : In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384.
(* [comment removed for export] *)
Hypothesis Hwinr : Forall (fun b => 0 <= b <= 255) winb.
Variable cw : PMR.ctrl.
Hypothesis HRM : PMRXA.rm_matchA L cw M P ps.
Hypothesis Hesc01 : 0 <= esc0 <= 1.
Definition RR : PMW.cres PMR.ctrl := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_018 ())).
Hypothesis HW4 : PMXAW.wroom CLA eg (PMW.r_evs RR) (PMW.r_allow RR).
(* [comment removed for export] *)
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
   (LK' : list fframe) (A' : list (Z * Z)),
   PMSA.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
      PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win ps' (PML.ps_win ps)) /\ PMLA.parser_sh M' ps' /\ PML.wf_ps ps' /\ PMLA.win_okA M' LBo ps' /\ PML.buf_bound ps' B /\
      PMLA.ec_at (hl_segs L) IC M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
      PMLA.ls_ok (hl_segs L) IC g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
      enc_invA M' V SQ eg' /\ PMXA.lits_ok L IC M' /\ (code = 0 -> PMXA.enc_sync ps' eg') /\
      LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = LBo /\ W = PMLA.W_parA IC P E ++ PMXA.W_encA IC V SQ /\ PMLA.pcredit_xA L cr' ps' (kx + PMXA.kenc L eg') (bx + benc eg') /\
      (PMSA.not_retreated ps ps' /\ (exists p' e', PML.ps_win ps' = Some (p', e') /\ getr R' 10%bv = Z_to_bv 64 p') /\
       (code <> 0 \/ PMSA.consumed ps ps' \/ PMSA.win_exhausted ps) /\ (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps)) /\
      PSKW.w3s L cw winb M' P ps ps' eg eg' code) ->                                                                                       (* [comment removed for export] *)
   regs_preserved R R' -> CHA.ahpres L ar LBk FF sp SCR W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
   ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
   srealizes (hl_segs L) SCFG (@PMSA.cfg L fx' R' r M' model') K.

(* [comment removed for export] *)
Let LEAFOK : forall i c k ps0 t, CH2.is_leaf G.CPS G.TAGS i c k ps0 t -> PSA.leaf_chk i c k ps0 t = true := PSL.LEAFOK_all.

(* [comment removed for export] *)
Let wlen := e - p.
Let bcap := PML.ps_bcap ps.
Let k0 := bcap / 2.
Let bptr := PML.ps_bptr ps.
Let buf := PML.ps_buf ps.
Let size0 := Z.of_nat (length (PML.ps_buf ps)).
Let sb := PML.ps_sb ps.
Let scap := PML.ps_scap ps.
Let stack := PML.ps_stack ps.
Let slen := Z.of_nat (length (PML.ps_stack ps)).
Let level := PML.ps_level ps.
Let sst0 := PML.ps_sst ps.
Let nst := PML.ps_nst ps.
Let done := PML.b2z (PML.ps_done ps).

(* [comment removed for export] *)
Definition E0 : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [wlen; B; k0; size0; bptr; sb; slen; scap; level; sst0; nst; done; cp0; cp20; pos0; ch; esc0; SQ] 0)))      (* [comment removed for export] *)
      (fun id => match id with 0%nat => map (Z_to_bv 8) stack | 1%nat => map (Z_to_bv 8) winb | _ => [] end).
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

(* [comment removed for export] *)
Lemma PAR : L5.u64_at (hl_segs L) M P (PMLA.VT_PARSER IC) /\ L5.u32_at (hl_segs L) M (P + 8) 1024 /\
  L5.u8_at (hl_segs L) M (P + 12) 0 /\ L5.u8_at (hl_segs L) M (P + 13) 1 /\ L5.u8_at (hl_segs L) M (P + 14) 0 /\ L5.u8_at (hl_segs L) M (P + 15) 1 /\
  L5.u8_at (hl_segs L) M (P + 16) 0 /\ L5.u8_at (hl_segs L) M (P + 17) 0 /\ L5.u8_at (hl_segs L) M (P + 18) 0 /\
  L5.lstr_short (hl_segs L) M (P + 24) [] /\ L5.lstr_short (hl_segs L) M (P + 48) [] /\ L5.lstr_short (hl_segs L) M (P + 72) [] /\
  L5.u64_at (hl_segs L) M (P + 96) (PMLA.VT_FUNC IC) /\ L5.u64_at (hl_segs L) M (P + 128) (P + 96) /\ L5.u32_at (hl_segs L) M (P + 144) level /\
  (L5.u64_at (hl_segs L) M (P + 200) p /\ L5.u64_at (hl_segs L) M (P + 192) e /\ p <= e) /\
  L5.u8_at (hl_segs L) M (P + 208) 15 /\ L5.u8_at (hl_segs L) M (P + 209) sst0 /\ L5.u8_at (hl_segs L) M (P + 210) nst /\ L5.u8_at (hl_segs L) M (P + 211) 1 /\
  L5.u8_at (hl_segs L) M (P + 212) done /\ L5.u8_at (hl_segs L) M (P + 213) 0 /\ L5.u32_at (hl_segs L) M (P + 216) 0 /\
  PMLA.str_at (hl_segs L) M (P + 224) (PML.SLong bcap bptr buf) /\ 264 <= bcap /\
  L5.u64_at (hl_segs L) M (P + 248) sb /\ L5.u64_at (hl_segs L) M (P + 256) (sb + slen) /\ L5.u64_at (hl_segs L) M (P + 264) (sb + scap) /\
  L5.bytes_at (hl_segs L) M sb stack /\ slen <= scap /\ L5.defined M P 272.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_019 ())).
Qed.

Lemma PDEFM : L5.defined M P 272.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_020 ())).
Qed.
(* [comment removed for export] *)
Lemma WFX : 0 <= sst0 <= 11 /\ 0 <= nst <= 7 /\ 1 <= slen <= 1027 /\ In scap [66; 132; 264; 528; 1056] /\ 66 <= scap <= 1056 /\ slen <= scap /\ 0 <= level <= 1024 /\ 0 <= done <= 1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_021 ())).
Qed.
Lemma ESCN : 0 <= PML.esc_need sst0 <= 3.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_022 ())).
Qed.
Lemma BBX : size0 + wlen + PML.esc_need sst0 <= B /\ B < 2 ^ 26 /\ 0 <= wlen /\ p <= e.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_023 ())).
Qed.
Lemma BCX : bcap mod 8 = 0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ bcap = 2 * k0 /\ 132 <= k0 <= 2 ^ 26.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_024 ())).
Qed.

(* [comment removed for export] *)
Ltac pose_facts :=
  pose proof (L5A.aly_segs L C LAY) as LS; pose proof (L5A.aly_img_lo L C LAY) as ILO; pose proof (L5A.aly_img_hi L C LAY) as IHI;
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WFT; pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WFT) as RFxG;
  assert (IBG : incl LB LBG) by (intros y Hy; unfold LBG; apply in_or_app; left; exact Hy);
  assert (RFx : CHA.rng_facts L ar LB FF) by (apply (CHA.rng_incl L ar LBG FF); [exact RFxG | exact IBG | apply incl_refl]);
  pose proof (CHA.rf_ceil _ _ _ _ RFx) as RC; destruct RC as (CL & C8); pose proof (CHA.rf_sptop _ _ _ _ RFx) as RS; destruct RS as (SP1 & SP16);
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WFT) as STOP;
  pose proof Hstk as Hstk'; destruct Hstk' as (S1 & S2 & S3 & S4 & S5 & S6); unfold SCR in S2, S5;
  pose proof OP as OP'; destruct OP' as (Pfr & P8 & Psh); pose proof OE as OE'; destruct OE' as (Efr & E8 & Esh); pose proof OV as OV'; destruct OV' as (Vfr & V8 & Vsh);
  pose proof (CL5A.infr_rng L ar LB FF P 272 RFx Pfr ltac:(clear; lia)) as OO; destruct OO as (O1 & O2 & O3 & O4 & O5 & O6 & O7);
  pose proof (CL5A.infr_rng L ar LB FF E 16 RFx Efr ltac:(clear; lia)) as QQ; destruct QQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7);
  pose proof (CL5A.infr_rng L ar LB FF V 8 RFx Vfr ltac:(clear; lia)) as VRR; destruct VRR as (VR1 & VR2 & VR3 & VR4 & VR5 & VR6 & VR7);
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in O1, O2, O3, O4, O5, O6, O7, Q1, Q2, Q3, Q4, Q5, Q6, Q7, VR1, VR2, VR3, VR4, VR5, VR6, VR7;
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5; change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7;
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in Q5; change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in Q7;
  change (hid (V + 8 <= 2147446784 \/ 17594333495296 <= V)) in VR5; change (hid (V + 8 <= hl_img_lo L \/ hl_img_hi L <= V)) in VR7;
  assert (FSLO : 7094272 <= ar_fs ar) by (destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [unfold FS_BYTES in A4; rewrite ILO in A4; clear - A0' A4; lia | rewrite IHI in A4; exact A4]);
  assert (INB : In (bptr, bcap) LB) by (unfold LB, PML.ps_blocks; left; reflexivity);
  assert (INS : In (sb, scap) LB) by (unfold LB, PML.ps_blocks; right; left; reflexivity);
  assert (INC : In (ch, 16384) LB) by (unfold LB; apply in_or_app; right; exact (proj1 HCH));
  pose proof OVX as OVX'; destruct OVX' as (VfrX & _ & VshX); pose proof OS2 as OS2'; destruct OS2' as (S2fr & S28 & S2sh);
  pose proof (CL5A.infr_rng L ar LB FF V 408 RFx VfrX ltac:(clear; lia)) as VQQ; destruct VQQ as (VQ1 & VQ2 & VQ3 & VQ4 & VQ5 & VQ6 & VQ7);
  pose proof (CL5A.infr_rng L ar LB FF SQ 24 RFx S2fr ltac:(clear; lia)) as SRR; destruct SRR as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7);
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in VQ1, VQ2, VQ3, VQ4, VQ5, VQ6, VQ7, SR1, SR2, SR3, SR4, SR5, SR6, SR7;
  change (hid (V + 408 <= 2147446784 \/ 17594333495296 <= V)) in VQ5; change (hid (V + 408 <= hl_img_lo L \/ hl_img_hi L <= V)) in VQ7;
  change (hid (SQ + 24 <= 2147446784 \/ 17594333495296 <= SQ)) in SR5; change (hid (SQ + 24 <= hl_img_lo L \/ hl_img_hi L <= SQ)) in SR7;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (bptr, bcap) (IBG _ INB)) as KBB; destruct KBB as ((KB0 & KB1 & KB16 & KB3 & KB4 & (KB5 & KB6 & KB7)) & KBdef & KBsha & KBbap & KBfap);
  cbn [fst snd] in KB0, KB1, KB16, KB3, KB4, KB5, KB6, KB7, KBdef, KBsha, KBbap, KBfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (sb, scap) (IBG _ INS)) as KSS; destruct KSS as ((KS0 & KS1 & KS16 & KS3 & KS4 & (KS5 & KS6 & KS7)) & KSdef & KSsha & KSbap & KSfap);
  cbn [fst snd] in KS0, KS1, KS16, KS3, KS4, KS5, KS6, KS7, KSdef, KSsha, KSbap, KSfap;
  pose proof (CHA.wf_blk _ _ _ _ _ _ _ _ WFT (ch, 16384) (IBG _ INC)) as KCC; destruct KCC as ((KC0 & KC1 & KC16 & KC3 & KC4 & (KC5 & KC6 & KC7)) & KCdef & KCsha & KCbap & KCfap);
  cbn [fst snd] in KC0, KC1, KC16, KC3, KC4, KC5, KC6, KC7, KCdef, KCsha, KCbap, KCfap;
  unfold BIGSHADOW_LO, BIGSHADOW_HI in KB6, KS6, KC6;
  change (hid (bptr + bcap <= 2147446784 \/ 17594333495296 <= bptr)) in KB6; change (hid (sb + scap <= 2147446784 \/ 17594333495296 <= sb)) in KS6;
  change (hid (ch + 16384 <= 2147446784 \/ 17594333495296 <= ch)) in KC6;
  pose proof (CHA.mod8_of_16 _ KB16) as KB8; pose proof (CHA.mod8_of_16 _ KS16) as KS8; pose proof (CHA.mod8_of_16 _ KC16) as KC8;
  pose proof WFX as WFX'; destruct WFX' as (WF1 & WF2 & WF3 & WF4 & WF5 & WF6 & WF7 & WF8);
  pose proof BBX as BBX'; destruct BBX' as (BB1 & BB2 & BB3 & BB4);
  pose proof BCX as BCX'; destruct BCX' as (BC8 & BC1 & BLT & BK0 & BK1);
  pose proof HCH as HCH'; destruct HCH' as (_ & CH1 & CH2 & WDEF & CHSH);
  pose proof ESCN as EN.

(* [comment removed for export] *)
Lemma EV0 : forall y : reg, ev E0 (ridx y) = getr R y.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_025 ())).
Qed.
Lemma VV : ev E0 2 = Z_to_bv 64 sp /\ ev E0 4 = Z_to_bv 64 (hl_tp L) /\ ev E0 10 = Z_to_bv 64 P /\ ev E0 11 = Z_to_bv 64 p /\ ev E0 12 = Z_to_bv 64 V /\ ev E0 13 = Z_to_bv 64 E
  /\ ev E0 32 = Z_to_bv 64 wlen /\ ev E0 33 = Z_to_bv 64 B /\ ev E0 34 = Z_to_bv 64 k0 /\ ev E0 35 = Z_to_bv 64 size0 /\ ev E0 36 = Z_to_bv 64 bptr /\ ev E0 37 = Z_to_bv 64 sb
  /\ ev E0 38 = Z_to_bv 64 slen /\ ev E0 39 = Z_to_bv 64 scap /\ ev E0 40 = Z_to_bv 64 level /\ ev E0 41 = Z_to_bv 64 sst0 /\ ev E0 42 = Z_to_bv 64 nst /\ ev E0 43 = Z_to_bv 64 done
  /\ ev E0 44 = Z_to_bv 64 cp0 /\ ev E0 45 = Z_to_bv 64 cp20 /\ ev E0 46 = Z_to_bv 64 pos0 /\ ev E0 47 = Z_to_bv 64 ch /\ ev E0 48 = Z_to_bv 64 esc0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_026 ())).
Qed.
Lemma UU : bv_unsigned (ev E0 2) = sp /\ bv_unsigned (ev E0 10) = P /\ bv_unsigned (ev E0 11) = p /\ bv_unsigned (ev E0 12) = V /\ bv_unsigned (ev E0 13) = E
  /\ bv_unsigned (ev E0 32) = wlen /\ bv_unsigned (ev E0 33) = B /\ bv_unsigned (ev E0 34) = k0 /\ bv_unsigned (ev E0 35) = size0 /\ bv_unsigned (ev E0 36) = bptr
  /\ bv_unsigned (ev E0 37) = sb /\ bv_unsigned (ev E0 38) = slen /\ bv_unsigned (ev E0 39) = scap /\ bv_unsigned (ev E0 40) = level /\ bv_unsigned (ev E0 41) = sst0
  /\ bv_unsigned (ev E0 42) = nst /\ bv_unsigned (ev E0 43) = done /\ bv_unsigned (ev E0 44) = cp0 /\ bv_unsigned (ev E0 45) = cp20 /\ bv_unsigned (ev E0 46) = pos0
  /\ bv_unsigned (ev E0 47) = ch /\ bv_unsigned (ev E0 48) = esc0 /\ bv_unsigned (ev E0 49) = SQ.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_027 ())).
Qed.

Ltac pose_U :=
  pose proof UU as UU'; destruct UU' as (U2 & U10 & U11 & U12 & U13 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44 & U45 & U46 & U47 & U48 & U49).
Lemma uv_add_lit : forall (E1 : env) (F k : Z) (v : nat), bv_unsigned (ev E1 v) = F -> 0 <= F -> 0 <= k -> F + k < 2 ^ 64 -> CL5A.uv E1 (EAlu Instr.ALU_ADD (EVar v) (ELit k)) = F + k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_028 ())).
Qed.
Lemma UVPK : forall k, 0 <= k <= 272 -> CL5A.uv E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k)) = P + k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_029 ())).
Qed.
Lemma UVP : CL5A.uv E0 (EVar 10) = P. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_030 ())).
Qed.
Lemma UVE : CL5A.uv E0 (EVar 13) = E. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_031 ())).
Qed.
Lemma UVV : CL5A.uv E0 (EVar 12) = V. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_032 ())).
Qed.
Lemma UVC : CL5A.uv E0 (EVar 11) = p. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_033 ())).
Qed.
Lemma UVCH : CL5A.uv E0 (EVar 47) = ch. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_034 ())).
Qed.
Lemma UVBP : CL5A.uv E0 (EVar 36) = bptr. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_035 ())).
Qed.
Lemma UVS2 : CL5A.uv E0 (EVar 49) = SQ. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_036 ())).
Qed.
Lemma UBC : bv_unsigned (edenot E0 (EMd Instr.M_MUL (ELit 2) (EVar 34))) = bcap.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_037 ())).
Qed.
Lemma UWL : bv_unsigned (edenot E0 (EVar 32)) = wlen. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_038 ())).
Qed.

(* [comment removed for export] *)
Lemma SCRV : CH.hd_scr GT.HDECL = 16896. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_039 ())).
Qed.
Lemma STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr GT.HDECL <= sp /\ sp <= ar_sptop ar.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_040 ())).
Qed.
Lemma SCRP : 0 <= CH.hd_scr GT.HDECL. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_041 ())).
Qed.
Lemma NF32 : (32 <= GT.NF)%nat. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_042 ())).
Qed.
Definition WW : list L5.range := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_043 ())).      (* [comment removed for export] *)
Lemma WWX : WW = PMLA.W_parA IC P E ++ PMXA.W_encA IC V SQ. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_044 ())).
Qed.
Definition Wo : list L5.range := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_045 ())).
Lemma WINC : incl Wo WW. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_046 ())).
Qed.
Lemma WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_047 ())).
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_048 ())).
Qed.
Lemma SHR : forall q n0 a, 0 <= q -> 0 < n0 -> q + n0 <= 2 ^ 47 -> in_shadow_of q n0 a -> 2147450880 <= a < 17594333495296.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_049 ())).
Qed.
(* [comment removed for export] *)
Lemma BLKC : forall u n a, In (u, n) LB -> u <= a < u + n -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_050 ())).
Qed.
Lemma BLKS : forall u n a, In (u, n) LB -> in_shadow_of u n a -> CHA.sclientA L ar LB FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_051 ())).
Qed.
(* [comment removed for export] *)
Lemma shreg_sub : forall o n q gr a, o mod 8 = 0 -> q mod 8 = 0 -> o <= q -> q + 8 * gr <= o + n -> 0 < gr -> q / 8 + SB <= a < q / 8 + SB + gr -> in_shadow_of o n a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_052 ())).
Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp GT.HDECL a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_053 ())).
Qed.

(* [comment removed for export] *)
Lemma RFO : CHA.rng_facts L ar LBo FF.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_054 ())).
Qed.
Lemma WOKo : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_055 ())).
Qed.
Lemma BLKCo : forall u n a, In (u, n) LBo -> u <= a < u + n -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_056 ())).
Qed.
Lemma BLKSo : forall u n a, In (u, n) LBo -> in_shadow_of u n a -> CHA.sclientA L ar LBo FF sp GT.HDECL a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_057 ())).
Qed.
(* [comment removed for export] *)
Lemma CRS_OKo : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBo FF sp GT.HDECL a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_058 ())).
Qed.

Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img GT.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_059 ())).
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr GT.HDECL) (CH.hd_scr GT.HDECL). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_060 ())).
Qed.
(* [comment removed for export] *)
Lemma LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_061 ())).
Qed.
Lemma LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_062 ())).
Qed.
Lemma LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_063 ())).
Qed.
Lemma LYN : wx_segs_nowrap (hl_segs L). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_064 ())).
Qed.
Lemma LYH : hl_img_hi L = IMGHI. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_065 ())).
Qed.
Lemma SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_066 ())).
Qed.
Lemma GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_067 ())).
Qed.
Lemma AL8 : sp mod 8 = 0 /\ (sp - 16896) mod 8 = 0 /\ (sp - 288) mod 32 = 0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_068 ())).
Qed.
(* [comment removed for export] *)
Definition inW (a : Z) : Prop := exists w, In w (PMLA.W_parA IC P E) /\ L5.in_rng w a.      (* [comment removed for export] *)
Lemma FOOTCL : forall a, PMLA.in_foot IC a -> 65536 <= a < 7094272 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_069 ())).
Qed.
Lemma NLIT : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> ~ (6946376 <= a < 6946448).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_070 ())).
Qed.
Lemma LITCL : forall a, 6946376 <= a < 6946448 -> 65536 <= a < 7094272 /\ forall LB1 sp' scr', aclient L ar LB1 FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_071 ())).
Qed.
Lemma WCL : forall a, inW a -> 0 <= a /\ a < ahl_ceil ar /\ (a < 2147446784 \/ 17594333495296 <= a) /\ (forall sp' scr', aclient L ar LB FF sp' scr' a)
                           /\ ((P <= a < P + 272 \/ E <= a < E + 16) \/ (6946368 <= a < 6946370 \/ 7084256 <= a < 7084800)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_072 ())).
Qed.
Lemma INWP : forall y, P <= y < P + 272 -> inW y. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_073 ())).
Qed.
Lemma INWE : forall y, E <= y < E + 16 -> inW y. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_074 ())).
Qed.

(* [comment removed for export] *)
Lemma uv_eaddz : forall Ex e0 z, CL5A.uv Ex (APC.eaddz e0 z) = (CL5A.uv Ex e0 + z) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_075 ())).
Qed.
Lemma uv_eadd : forall Ex a b, CL5A.uv Ex (APC.eadd a b) = (CL5A.uv Ex a + CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_076 ())).
Qed.
Lemma uv_esub : forall Ex a b, CL5A.uv Ex (APC.esub a b) = (CL5A.uv Ex a - CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_077 ())).
Qed.
Lemma uv_escale : forall Ex c e0, CL5A.uv Ex (APC.escale c e0) = (c * CL5A.uv Ex e0) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_078 ())).
Qed.
Lemma uv_lit : forall Ex z, 0 <= z < 2 ^ 64 -> CL5A.uv Ex (ELit z) = z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_079 ())).
Qed.
(* [comment removed for export] *)
Lemma ind_val : forall Ex x c v, bv_unsigned (edenot Ex x) = v -> 0 <= c < 2 ^ 64 ->
  bv_unsigned (edenot Ex (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB x (ELit c)) (ELit 1))) = if Z.eqb v c then 1 else 0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_080 ())).
Qed.
Lemma ind_valn : forall (w : word) d v, bv_unsigned w = v -> - 2 ^ 64 < d < 0 ->
  bv_unsigned (Sem.alu64 Instr.ALU_SLTU (Sem.alu64 Instr.ALU_ADD w (Z_to_bv 64 d)) (Z_to_bv 64 1)) = if Z.eqb v (- d) then 1 else 0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_081 ())).
Qed.
Lemma ESCV : forall n : nat, (n <= 11)%nat ->
  (if Z.of_nat n =? 3 then 1 else 0) + 2 * (if Z.of_nat n =? 4 then 1 else 0) + 3 * (if Z.of_nat n =? 5 then 1 else 0) + (if Z.of_nat n =? 9 then 1 else 0)
  + 2 * (if Z.of_nat n =? 10 then 1 else 0) + 3 * (if Z.of_nat n =? 11 then 1 else 0) = PML.esc_need (Z.of_nat n).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_082 ())).
Qed.

Lemma ESCV2 : forall z, 0 <= z <= 11 ->
  (if z =? 3 then 1 else 0) + 2 * (if z =? 4 then 1 else 0) + 3 * (if z =? 5 then 1 else 0) + (if z =? 9 then 1 else 0) + 2 * (if z =? 10 then 1 else 0) + 3 * (if z =? 11 then 1 else 0)
  = PML.esc_need z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_083 ())).
Qed.
(* [comment removed for export] *)
Lemma KIMG : forall Ex lo hi, L5.img_clear M 65536 1466368 -> 65536 <= lo -> hi <= 1466368 -> kentry_ok (hl_segs L) Ex (CCA.vis A model M) (KImg lo hi).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_084 ())).
Qed.

Lemma At0 : CC.At (hl_segs L) GT.t0 E0 R (CCA.vis A model M).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_085 ())).
Qed.

(* [comment removed for export] *)
Lemma KSHO : forall o n a, CL5A.ainfr FF o n -> 0 < n -> o + n <= 2 ^ 47 -> in_shadow_of o n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_086 ())).
Qed.
Lemma KV : forall a, V <= a < V + 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_087 ())).
Qed.
Lemma KSQ : forall a, in_shadow_of V 408 a \/ in_shadow_of SQ 24 a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_088 ())).
Qed.
Lemma KLB : forall u n a, In (u, n) LBo -> u <= a < u + n \/ in_shadow_of u n a -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_089 ())).
Qed.
Lemma KSTK : forall a, S (sp - 16896) <= a < S (sp - 16896) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 16896)) / 8 -> CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_090 ())).
Qed.
(* [comment removed for export] *)
Lemma DECW : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> inW a \/ L5.outside WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_091 ())).
Qed.
Lemma IMGOUT : forall a, 65536 <= a < 1466368 -> L5.outside WW a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_092 ())).
Qed.
Lemma PTKF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
                 \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
                 \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> PMLA.in_foot IC a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_093 ())).
Qed.
Lemma IMGCL : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 65536 <= a < 7094272 /\ forall sp' scr', aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_094 ())).
Qed.
(* [comment removed for export] *)
Lemma SXW : forall a w, inW a -> In w (PMXA.W_encA IC V SQ) -> L5.in_rng w a -> False.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_095 ())).
Qed.
Lemma STCL : forall a LB' FF' sp' scr', PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> aclient L ar LB' FF' sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_096 ())).
Qed.
(* [comment removed for export] *)
Lemma WFR : forall a F n, inW a -> ar_fs ar <= F -> fframes_apart F n FF -> 0 < n -> ~ (F <= a < F + n).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_097 ())).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bptrI (i : nat) (E1 : env) : Z := CL5A.uv E1 (fst (PSA.blk0 i)).
Definition bcapI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 (ParseStringXBW_blobs1.kr_b_098 ())).
Definition sbI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 (ParseStringXBW_blobs1.kr_b_099 ())).
Definition scapI (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 (ParseStringXBW_blobs1.kr_b_100 ())).
(* [comment removed for export] *)
Definition stk_kx (sc : Z) : Z := Z.log2 (1056 / sc) * hl_k_per_malloc L.
Definition stk_bx (sc : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_101 ())).
Definition Cred (g1 : PMES.eghost) (i : nat) (E1 : env) (cr1 : credit) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 4 (ParseStringXBW_blobs1.kr_b_102 ())).      (* [comment removed for export] *)
Lemma stk_pot_nonneg : forall sc, In sc [66; 132; 264; 528; 1056] -> 0 <= stk_kx sc /\ 0 <= stk_bx sc.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_103 ())).
Qed.
Lemma pcredit_bufcred : forall g1 cr1 ps1, In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  PMLA.pcredit_xA L cr1 ps1 (KXG g1) (BXG g1) <-> PMSA.bufcredA L cr1 (PML.ps_bcap ps1) (stk_kx (PML.ps_scap ps1) + KXG g1) (stk_bx (PML.ps_scap ps1) + BXG g1).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_104 ())).
Qed.
(* [comment removed for export] *)
Definition FLF (E1 : env) : Prop := ar_fs ar <= CL5A.uv E1 (EVar 50) < ar_fs ar + 11571200 /\ ~ aclient L ar LBo FF sp (CH.hd_scr GT.HDECL) (CL5A.uv E1 (EVar 50)).
(* [comment removed for export] *)
Definition FIXA (a : Z) : Prop :=
     (P <= a < P + 148 \/ P + 156 <= a < P + 168 \/ P + 176 <= a < P + 209 \/ a = P + 210 \/ P + 212 <= a < P + 220 \/ P + 221 <= a < P + 224 \/ P + 248 <= a < P + 272)
  \/ (sb <= a < sb + scap) \/ in_shadow_of sb scap a \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a.
Definition AGFIX (M1 : mem) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_105 ())).
(* [comment removed for export] *)
Definition STR (i : nat) (E1 : env) (M1 : mem) : Prop :=
  exists s', PMLA.str_at (hl_segs L) M1 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s') /\ shadow_blk M1 (bptrI i E1) (bcapI i E1) /\ bcap <= bcapI i E1 <= 2 ^ 27 /\ size0 <= Z.of_nat (length s')
  /\ sbI i E1 = sb /\ scapI i E1 = scap.
(* [comment removed for export] *)
Definition PH0 (M1 : mem) : Prop := PMLA.ec_at (hl_segs L) IC M1 E 0 /\ L5.u8_at (hl_segs L) M1 (P + 211) 1 /\ PMLA.ls_ok (hl_segs L) IC g M1.
(* [comment removed for export] *)
Definition PHA (v : Z) (M1 : mem) : Prop := (v = 0 /\ PH0 M1) \/ (v = 17 /\ PMLA.ec_at (hl_segs L) IC M1 E 17 /\ L5.u8_at (hl_segs L) M1 (P + 211) 0 /\ PMLA.ls_ok (hl_segs L) IC PML.LS2 M1).
Definition ECV (i : nat) (E1 : env) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 (ParseStringXBW_blobs1.kr_b_106 ())).
Definition PHS (M1 : mem) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_107 ())).
(* [comment removed for export] *)
Definition WINOK (M1 : mem) (ps' : PML.pstate) : Prop :=
  match PML.ps_win ps' with Some (p', e') => ch <= p' /\ e' <= ch + 16384 /\ L5.defined M1 p' (e' - p') /\ shadow_blk M1 ch 16384 | None => True end.
(* [comment removed for export] *)
Definition POSTP (M1 : mem) (q pp cc ss sc : Z) : Prop :=
  exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
    PMLA.parser_at (hl_segs L) IC M1 P (PML.ps_set_win ps' (PML.ps_win ps)) /\ PMLA.parser_sh M1 ps' /\ PML.wf_ps ps' /\ WINOK M1 ps' /\ PML.buf_bound ps' B /\
    PMLA.ec_at (hl_segs L) IC M1 E code /\ (code <> 0 -> PML.ps_more ps' = false) /\ PMLA.ls_ok (hl_segs L) IC g' M1 /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
    PML.ps_blocks ps' = [(pp, cc); (ss, sc)] /\ In sc [66; 132; 264; 528; 1056] /\
    PMSA.not_retreated ps ps' /\ (exists p' e', PML.ps_win ps' = Some (p', e') /\ q = p' /\ e' = e) /\ (code <> 0 \/ PMSA.consumed ps ps' \/ PMSA.win_exhausted ps) /\      (* [comment removed for export] *)
    (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps) /\ (code = 0 -> PMXA.key_inv ps').      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ESVP (i : nat) (E1 : env) (M1 : mem) : Prop :=
  exists (ps3 : PML.pstate) (g' : PML.ls_state), let code := ECV i E1 in let qc := CL5A.uv E1 PSA.CUR in
    PMLA.parser_at (hl_segs L) IC M1 P (PML.ps_set_win ps3 (PML.ps_win ps)) /\ PMLA.parser_sh M1 ps3 /\ PML.wf_ps ps3 /\ PML.ps_win ps3 = Some (qc, e) /\ p <= qc < e /\
    PMLA.win_okA M1 LBo ps3 /\ PML.buf_bound ps3 B /\ PMLA.ec_at (hl_segs L) IC M1 E code /\ (code <> 0 -> PML.ps_more ps3 = false) /\
    PMLA.ls_ok (hl_segs L) IC g' M1 /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
    PML.ps_blocks ps3 = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] /\
    (code = 0 -> PML.ps_more ps3 = true /\ PML.ps_level ps3 = PML.ps_level ps) /\ 0 <= code <= 31 /\ (code = 0 -> PMXA.key_inv ps3).      (* [comment removed for export] *)
Definition XIj (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop :=
  ((1 <= i)%nat -> FLF E1) /\
  match PSA.kind_of i with
  | PSA.KEsv => ESVP i E1 M1
  | PSA.KRetx => POSTP M1 (CL5A.uv E1 (EVar 78)) (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1)
  | PSA.KAtc => AGFIX M1 /\ STR i E1 M1 /\ PHA (ECV i E1) M1
  | PSA.KSetec => AGFIX M1 /\ STR i E1 M1 /\ PHS M1
  | _ => AGFIX M1 /\ STR i E1 M1 /\ PH0 M1
  end.
(* [comment removed for export] *)
Definition xinv : mem -> PMES.eghost -> Prop := XKA.xinv L IC enc_invA V SQ.
Definition xfoot : PMES.eghost -> Z -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_108 ())).
Definition GF (i : nat) (E1 : env) (M1 : mem) (g1 : PMES.eghost) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 4 (ParseStringXBW_blobs1.kr_b_109 ())).
Definition XI (g1 : PMES.eghost) (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 6 (ParseStringXBW_blobs1.kr_b_110 ())).
Lemma XINV0 : xinv M eg. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_111 ())).
Qed.
Lemma XKEEP : forall (M1 M2 : mem) g1, (forall a, xfoot g1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> xinv M1 g1 -> xinv M2 g1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_112 ())).
Qed.
(* [comment removed for export] *)
Definition LBV (g1 : PMES.eghost) : list (Z * Z) := LBo ++ PMES.g_lbv g1.
Lemma LBVE : forall g1, CHV.LBr LBo PMES.eghost PMES.g_lbv g1 = LBV g1. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_113 ())).
Qed.
Lemma ILV : forall g1, incl LBo (LBV g1). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_114 ())).
Qed.
Definition OKVt : mem -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_115 ())).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUFB (o : list Z) : list Z := PMR.b256 buf ++ o.
Definition NOF (E1 : env) (n : nat) (c : Z) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 3 (ParseStringXBW_blobs1.kr_b_116 ())).
Definition CPL (i : nat) (E1 : env) (c0 : PMR.ctrl) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 3 (ParseStringXBW_blobs1.kr_b_117 ())).
Definition BUFL (i : nat) (E1 : env) (M1 : mem) (o : list Z) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 4 (ParseStringXBW_blobs1.kr_b_118 ())).
Definition TAGL (i : nat) (E1 : env) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 2 (ParseStringXBW_blobs1.kr_b_119 ())).
(* [comment removed for export] *)
Definition SSTEP (i : nat) (sst c : Z) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0,
  NOF E1 n c /\ (n <= length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = sst /\ CPL i E1 c0 /\ BUFL i E1 M1 o0 /\ TAGL i E1.
(* [comment removed for export] *)
Definition STEXT (i : nat) (E1 : env) (M1 : mem) : Prop := exists (n nb : nat) cb ob,
  NOF E1 n 0 /\ Z.of_nat nb = CL5A.uv E1 (EVar 61) /\ (nb <= n <= length winb)%nat /\ PSKW.xrun cw (firstn nb winb) = Some (cb, ob) /\ PMR.c_sst cb = 0 /\
  forallb PSKW.plain (firstn (n - nb) (skipn nb winb)) = true /\ BUFL i E1 M1 ob /\ TAGL i E1.
(* [comment removed for export] *)
Definition cpin (sst : Z) (c0 : PMR.ctrl) : Z := if ((sst =? 2) || (sst =? 8))%bool then 0 else if sst <=? 5 then PMR.c_cp c0 else PMR.c_cp2 c0.
(* [comment removed for export] *)
Definition SATC (i : nat) (sst : Z) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0 b,
  NOF E1 n 0 /\ (n < length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = sst /\ CPL i E1 c0 /\ BUFL i E1 M1 o0 /\ TAGL i E1 /\
  nth n winb 0 = b /\ CL5A.uv E1 (EVar 82) = b /\
  ((CL5A.uv E1 (PSW.ECVX i) = 0 /\ exists d, PMR.hexval b = Some d /\ CL5A.uv E1 (PSW.A0X i) = PSWS.sx32 (PSKW.hexv (cpin sst c0) d)) \/
   (CL5A.uv E1 (PSW.ECVX i) = 17 /\ PMR.hexval b = None)).
(* [comment removed for export] *)
Definition SU4C (i : nat) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0 b d,
  NOF E1 n 0 /\ (n < length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = PMR.SS_U4 /\ BUFL i E1 M1 o0 /\ TAGL i E1 /\
  nth n winb 0 = b /\ PMR.hexval b = Some d /\ PMR.is_high_surr (PSKW.hexv (PMR.c_cp c0) d) = false /\ CL5A.uv E1 (EVar 57) mod 2 ^ 32 = PSKW.hexv (PMR.c_cp c0) d.
(* [comment removed for export] *)
Definition SU8C (i : nat) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0 b d,
  NOF E1 n 0 /\ (n < length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = PMR.SS_U8 /\ BUFL i E1 M1 o0 /\ TAGL i E1 /\
  nth n winb 0 = b /\ PMR.hexval b = Some d /\ CL5A.uv E1 (EVar 57) mod 2 ^ 32 = PMR.c_cp c0 mod 2 ^ 32 /\ CL5A.uv E1 (EVar 66) = PSWS.sx32 (PSKW.hexv (PMR.c_cp2 c0) d).
(* [comment removed for export] *)
Definition SRET4 (i : nat) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0 b d,
  NOF E1 n 0 /\ (n < length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = PMR.SS_U4 /\ TAGL i E1 /\
  nth n winb 0 = b /\ PMR.hexval b = Some d /\ PMR.is_high_surr (PSKW.hexv (PMR.c_cp c0) d) = false /\ BUFL i E1 M1 (o0 ++ PMR.utf8_of (PSKW.hexv (PMR.c_cp c0) d)).
(* [comment removed for export] *)
Definition SERR (code : Z) : Prop := exists c1 w1, PMR.parse_string cw winb = PMR.err c1 w1 code /\ code <> 0.
(* [comment removed for export] *)
Definition EVW (g1 : PMES.eghost) : Prop :=
  PMES.g_es g1 = PMW.es_run (PMES.g_es eg) (PMW.r_evs RR) /\
  exists pay, 0 <= pay <= PMW.r_allow RR /\ PMES.g_len g1 = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMW.r_evs RR) + pay.
(* [comment removed for export] *)
Definition SESV (g1 : PMES.eghost) (i : nat) (E1 : env) (M1 : mem) : Prop := exists (n : nat) c0 o0,
  Z.of_nat n = CL5A.uv E1 PSA.CUR - p /\ (n < length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\
  PMR.parse_string cw winb = PMR.end_string c0 (skipn n winb) /\ EVW g1 /\ ECV i E1 = PMR.q_code (PMR.end_string c0 (skipn n winb)) /\
  (ECV i E1 = 0 -> forall ps3, PMLA.parser_at (hl_segs L) IC M1 P (PML.ps_set_win ps3 (PML.ps_win ps)) -> PML.wf_ps ps3 -> PML.ps_more ps3 = true ->
     PML.ps_level ps3 = PML.ps_level ps -> PML.ps_blocks ps3 = [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] ->
     PMR.rm_core (PMR.q_c (PMR.end_string c0 (skipn n winb))) ps3 /\ PML.ps_st ps3 <> PML.ST_STRING /\ PML.ps_st ps3 <> PML.ST_NUMBER) /\
  (ECV i E1 = 0 -> L5.bytes_at (hl_segs L) M1 (p + Z.of_nat (Datatypes.S n)) (skipn (Datatypes.S n) winb)).
(* [comment removed for export] *)
Definition SRETX (g1 : PMES.eghost) (E1 : env) (M1 : mem) : Prop :=
  forall ps' code, PMLA.parser_at (hl_segs L) IC M1 P (PML.ps_set_win ps' (PML.ps_win ps)) -> PML.wf_ps ps' -> PMLA.ec_at (hl_segs L) IC M1 E code ->
    PML.ps_win ps' = Some (CL5A.uv E1 (EVar 78), e) -> PML.ps_blocks ps' = [(bptrI 28 E1, bcapI 28 E1); (sbI 28 E1, scapI 28 E1)] -> PML.ps_bcap ps' < 2 ^ 63 ->
    (code = 0 -> PML.ps_more ps' = true /\ PML.ps_level ps' = PML.ps_level ps) ->
    PSKW.w3s L cw winb M1 P ps ps' eg g1 code.
Definition SIM (g1 : PMES.eghost) (i : nat) (E1 : env) (M1 : mem) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 4 (ParseStringXBW_blobs1.kr_b_120 ())).
Definition XIW (g1 : PMES.eghost) (i : nat) (E1 : env) (A1 : list (Z * Z)) (M1 : mem) (m1 : Model) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 6 (ParseStringXBW_blobs1.kr_b_121 ())).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUFZ (i : nat) (E1 : env) (a : Z) : Prop :=
  exists eS eP, PSW.SIZX i = Some eS /\ PSW.PTRX i = Some eP /\ CL5A.uv E1 eP <= a < CL5A.uv E1 eP + CL5A.uv E1 eS.
Lemma uvA : forall n E1 E2 x, env_agree n E1 E2 -> APC.expr_vars_lt n x = true -> CL5A.uv E2 x = CL5A.uv E1 x.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_122 ())).
Qed.
Lemma uvV : forall n E1 E2 (v : nat), env_agree n E1 E2 -> (v < n)%nat -> CL5A.uv E2 (EVar v) = CL5A.uv E1 (EVar v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_123 ())).
Qed.
Lemma LOWC : forall i, PSW.lowcells i = true ->
  (forall x, PSW.CPX i = Some x -> APC.expr_vars_lt 62 x = true) /\ (forall x, PSW.CP2X i = Some x -> APC.expr_vars_lt 62 x = true) /\
  (forall x, PSW.SIZX i = Some x -> APC.expr_vars_lt 62 x = true) /\ (forall x, PSW.PTRX i = Some x -> APC.expr_vars_lt 62 x = true) /\ (forall x, PSW.TAGX i = Some x -> APC.expr_vars_lt 62 x = true).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_124 ())).
Qed.
Lemma CPL_same : forall i j E1 E2 c0, PSW.lowcells i = true -> PSW.CPX j = PSW.CPX i -> PSW.CP2X j = PSW.CP2X i -> env_agree 62 E1 E2 -> CPL i E1 c0 -> CPL j E2 c0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_125 ())).
Qed.
Lemma TAGL_same : forall i j E1 E2, PSW.lowcells i = true -> PSW.TAGX j = PSW.TAGX i -> env_agree 62 E1 E2 -> TAGL i E1 -> TAGL j E2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_126 ())).
Qed.
Lemma BUFL_same : forall i j E1 E2 (M1 M2 : mem) o, PSW.lowcells i = true -> PSW.SIZX j = PSW.SIZX i -> PSW.PTRX j = PSW.PTRX i -> env_agree 62 E1 E2 ->
  (forall a, BUFZ i E1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> BUFL i E1 M1 o -> BUFL j E2 M2 o.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_127 ())).
Qed.
Lemma SIM_same : forall g1 i j E1 E2 (M1 M2 : mem), PSW.lowcells i = true -> PSW.KD j = PSW.KD i -> ((exists sst cc, PSW.KD i = PSW.KStep sst cc) \/ PSW.KD i = PSW.KText) ->
  PSW.same_cells i j = true -> env_agree 62 E1 E2 -> (forall a, BUFZ i E1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  SIM g1 i E1 M1 -> SIM g1 j E2 M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_128 ())).
Qed.

(* [comment removed for export] *)
Lemma UVRw : forall Ex e0, 0 <= CL5A.uv Ex e0 < 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_129 ())).
Qed.
Lemma curform_val : forall E' cc, bv_unsigned (ev E' 11) = p -> bv_unsigned (ev E' 32) = wlen -> 0 <= cc <= 1 ->
  0 <= wlen - CL5A.uv E' (EVar 51) + cc <= wlen + 1 -> CL5A.uv E' (EVar 51) <= wlen + cc -> CL5A.uv E' (PSW.curform cc) = p + (wlen - CL5A.uv E' (EVar 51) + cc).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_130 ())).
Qed.
Lemma WBYTE : forall cells E' (M' : mem) Hh cc (n : nat),
  H_off_segments (hl_segs L) Hh ->
  (forall X0, In X0 cells -> kentry_ok (hl_segs L) E' (mrestrict Hh M') X0) -> bv_unsigned (ev E' 11) = p -> bv_unsigned (ev E' 32) = wlen ->
  PSW.hasb cells cc = true -> Z.of_nat n = wlen - CL5A.uv E' (EVar 51) + cc -> 0 <= cc <= 1 ->
  L5.bytes_at (hl_segs L) M' p winb ->
  (n < length winb)%nat /\ CL5A.uv E' (EVar 82) = nth n winb 0 /\ 0 <= nth n winb 0 <= 255.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_131 ())).
Qed.
(* [comment removed for export] *)
Lemma WINB_of : forall (M1 : mem), (forall a, ch <= a < ch + 16384 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> L5.bytes_at (hl_segs L) M1 p winb.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_132 ())).
Qed.

(* [comment removed for export] *)
Lemma firstn_split : forall (l : list Z) a b, (a <= b)%nat -> (a <= length l)%nat -> firstn b l = firstn a l ++ firstn (b - a) (skipn a l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_133 ())).
Qed.
Lemma sim_stepping : forall g1 i E1 (M1 : mem) sst cc, PSWR.stepping i sst cc -> SIM g1 i E1 M1 ->
  exists (n : nat) c0 o0, NOF E1 n cc /\ (n <= length winb)%nat /\ PSKW.xrun cw (firstn n winb) = Some (c0, o0) /\ PMR.c_sst c0 = sst /\ TAGL i E1 /\
    (PSW.KD i = PSW.KStep sst cc -> CPL i E1 c0 /\ BUFL i E1 M1 o0) /\ 0 <= cc <= 1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_134 ())).
Qed.
Lemma sim_serr : forall sst (n : nat) c0 o0 code, (n < length winb)%nat -> PSKW.xrun cw (firstn n winb) = Some (c0, o0) -> PMR.c_sst c0 = sst ->
  (match PSKW.sdesc sst (nth n winb 0) with PSKW.SErr e' => e' =? code | _ => false end) = true -> code <> 0 -> SERR code.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_135 ())).
Qed.

(* [comment removed for export] *)
Lemma hex_some : forall b, PMSA.is_hex b -> exists d, PMR.hexval b = Some d /\ 0 <= d < 16.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_136 ())).
Qed.
Lemma hex_none : forall b, ~ PMSA.is_hex b -> PMR.hexval b = None.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_137 ())).
Qed.
Lemma CPL_sameN : forall i j E1 E2 c0, (i < 79)%nat -> PSW.CPX j = PSW.CPX i -> PSW.CP2X j = PSW.CP2X i -> env_agree (CC.cp_nx (PSW.cutn i)) E1 E2 -> CPL i E1 c0 -> CPL j E2 c0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_138 ())).
Qed.
Lemma TAGL_sameN : forall i j E1 E2, (i < 79)%nat -> PSW.TAGX j = PSW.TAGX i -> env_agree (CC.cp_nx (PSW.cutn i)) E1 E2 -> TAGL i E1 -> TAGL j E2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_139 ())).
Qed.
Lemma BUFL_sameN : forall i j E1 E2 (M1 M2 : mem) o, (i < 79)%nat -> PSW.SIZX j = PSW.SIZX i -> PSW.PTRX j = PSW.PTRX i -> env_agree (CC.cp_nx (PSW.cutn i)) E1 E2 ->
  (forall a, BUFZ i E1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> BUFL i E1 M1 o -> BUFL j E2 M2 o.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_140 ())).
Qed.

(* [comment removed for export] *)
Lemma BUFB_app : forall o x, BUFB (o ++ x) = BUFB o ++ x.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_141 ())).
Qed.
Lemma BUFB_norm : forall o, Forall PSKW.inb o -> PMR.b256 (BUFB o) = BUFB o.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_142 ())).
Qed.
Lemma winb_inb : forall (n : nat), Forall PSKW.inb (firstn n winb).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_143 ())).
Qed.
Lemma xrun_o_inb : forall (n : nat) c0 o0, PSKW.xrun cw (firstn n winb) = Some (c0, o0) -> Forall PSKW.inb o0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_144 ())).
Qed.
Lemma BUFB_len : forall o, Z.of_nat (length (BUFB o)) = size0 + Z.of_nat (length o).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_145 ())).
Qed.


(* [comment removed for export] *)
Lemma ffs_i : forall i, (1 <= i <= 78)%nat -> nth i PSA.FFS [] = [PSA.FR].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_146 ())).
Qed.
Lemma ffs_0 : nth 0 PSA.FFS [] = []. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_147 ())).
Qed.
Lemma bls_i : forall i, (i <= 78)%nat -> nth i G.BLS [] = [PSA.blk0 i; PSA.blk1 i].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_148 ())).
Qed.
(* [comment removed for export] *)
Lemma BLK0 : PSA.blk0 0 = (EVar 36, EMd Instr.M_MUL (ELit 2) (EVar 34)) /\ PSA.blk1 0 = (EVar 37, EVar 39). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_149 ())).
Qed.
Lemma BLK29 : PSA.blk0 29 = (EVar 36, EMd Instr.M_MUL (ELit 2) (EVar 34)) /\ PSA.blk1 29 = (EVar 37, EVar 39). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_150 ())).
Qed.
Lemma K29 : PSA.kind_of 29 = PSA.KSm. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_151 ())).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AmbV.
Variables (g1 : PMES.eghost) (M0c : mem).
Hypothesis OKV : OKVt M0c.
Lemma DEF0V : L5.defined M0c (sp - CH.hd_scr GT.HDECL) (CH.hd_scr GT.HDECL). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_152 ())).
Qed.
Lemma DEFUPV : L5.defined M0c sp (ar_stack_top ar - sp). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_153 ())).
Qed.
Lemma FRAME00 : forall i E1 A1 M1 m1, CHV.aambV L ar HI GT.NF E0 model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred g1 M0c i E1 A1 M1 m1 ->
  (forall a, CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FF sp 0 a -> M (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_154 ())).
Qed.
Lemma IHV : forall mu, CCA.IH (hl_segs L) G.CPS (CHV.ambV L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred XIW) K PMSA.fp_ok mu ->
  CCA.IH (hl_segs L) G.CPS (CHV.ambXV L ar HI GT.NF E0 model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred XIW g1 M0c) K PMSA.fp_ok mu.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_155 ())).
Qed.
Lemma WOKV : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
  0 <= a < 2 ^ 64 /\ aclientw L ar (LBV g1) FF sp (CH.hd_scr GT.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_156 ())).
Qed.
Lemma CRSV : forall rg : SGP.region, In rg (CH.hd_crs GT.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (LBV g1) FF sp GT.HDECL a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_157 ())).
Qed.
(* [comment removed for export] *)
Lemma FRM : forall i E1 A1 M1 m1, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  let F := CL5A.uv E1 FE in let ob := [(bptrI i E1, bcapI i E1); (sbI i E1, scapI i E1)] in
  CHA.curB (LBV g1) G.BLS i E1 = ob ++ LBV g1 /\ CHA.curF FF sp PSA.FFS i E1 = (F, 1, sp + -288 + 32) :: FF /\ env_agree GT.NF E0 E1 /\
  0 <= F /\ F + 128 <= 140737488355328 /\ F mod 8 = 0 /\ (F + 128 <= 2147446784 \/ 17594333495296 <= F) /\ ar_fs ar <= F /\ F + 128 <= ar_fs ar + 11571200 /\ fframes_apart F 128 FF /\
  (exists crX LKX, ri_inv HI (ob ++ LBV g1) ((F, 1, sp + -288 + 32) :: FF) LKX crX A1 M1 (vml_of m1) /\ Cred g1 i E1 crX).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_158 ())).
Qed.
(* [comment removed for export] *)
Definition outU (E' : env) (a : Z) : Prop :=
  let F := CL5A.uv E' FE in let fl := CL5A.uv E' FLE in
  (a < sp - 16896 \/ sp <= a) /\ ~ (P + 148 <= a < P + 156) /\ ~ (P + 168 <= a < P + 176) /\ a <> P + 209 /\ a <> P + 211 /\ a <> P + 220 /\
  ~ (F <= a < F + 128) /\ ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) /\ a <> fl.
(* [comment removed for export] *)
Lemma LEAFK : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  (forall k, (k < 50)%nat -> ev E' k = ev E0 k) /\ CL5A.uv E' FE = CL5A.uv E1 FE /\ CL5A.uv E' FLE = CL5A.uv E1 FLE
  /\ (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0)
  /\ (forall (q : nat) (e0 : expr) (z : Z), CL.ps_reg_is ps0 q e0 = true -> bv_unsigned (edenot E' e0) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z)
  /\ (forall a, 0 <= a < 2 ^ 64 -> outU E' a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_159 ())).
Qed.

(* [comment removed for export] *)
Lemma BLKW : forall LBX FFX LKX crX AX MX VX u n, ri_inv HI LBX FFX LKX crX AX MX VX -> In (u, n) LBX ->
        (4096 <= u /\ 0 < n /\ u + n <= ahl_ceil ar /\ u mod 16 = 0 /\ (u + n <= 2147446784 \/ 17594333495296 <= u) /\ u + n <= 140737488355328)
        /\ (u + n <= hl_img_lo L \/ hl_img_hi L <= u) /\ fframes_apart u n FFX /\ (u + n <= ar_fs ar \/ ar_fs ar + 11571200 <= u) /\ HeapIface.defined MX u n.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_160 ())).
Qed.
Lemma XRNG : forall LBX FFX LKa cra A1 (M1 : word -> option byte) m1, ri_inv HI LBX FFX LKa cra A1 M1 (vml_of m1) -> incl (PMES.g_lbv g1) LBX ->
          forall b, In b (PMES.g_lbv g1) -> 4096 <= fst b /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar /\ fst b mod 16 = 0 /\ fst b + snd b <= 2 ^ 47 /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + 11571200 <= fst b).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_161 ())).
Qed.
Lemma XK : forall a LBX FFX sp' scr' Wc, xfoot g1 a -> incl (LBV g1) LBX -> incl FF FFX -> (forall x, sp' - scr' <= x < sp' -> sp - 16896 <= x < sp) ->
          (forall w, In w Wc -> (P <= fst w /\ fst w + snd w <= P + 272) \/ (E <= fst w /\ fst w + snd w <= E + 16) \/ w = (PMLA.ERRCAT_GUARD IC, 2) \/ w = (PMLA.ATEXIT_TAB IC, PmIcptIfaceA.ATEXIT_TAB_BYTES) \/ (sp - 16896 <= fst w /\ fst w + snd w <= sp) \/ (6952940 <= fst w /\ fst w + snd w <= 6952944)) ->
          (forall b, In b (PMES.g_lbv g1) -> 4096 <= fst b /\ 0 < snd b /\ fst b + snd b <= ahl_ceil ar /\ fst b mod 16 = 0 /\ fst b + snd b <= 2 ^ 47 /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b) /\ (fst b + snd b <= ar_fs ar \/ ar_fs ar + 11571200 <= fst b)) ->
          CHA.akept L ar LBX FFX sp' scr' Wc a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_162 ())).
Qed.
Lemma FLV : forall LBX FFX LKa cra A1 (M1 : word -> option byte) m1 fl', ri_inv HI LBX FFX LKa cra A1 M1 (vml_of m1) -> incl (PMES.g_lbv g1) LBX ->
          ar_fs ar <= fl' < ar_fs ar + 11571200 -> ~ aclient L ar LBo FF sp (CH.hd_scr G.HDECL) fl' -> ~ aclient L ar (LBV g1) FF sp (CH.hd_scr G.HDECL) fl'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_163 ())).
Qed.
(* [comment removed for export] *)
Lemma XOUT : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 ->
  forall a, xfoot g1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_164 ())).
Qed.

(* [comment removed for export] *)
Lemma PSX : forall (M' : mem) (sst' : Z) (more' : bool) (cc pp q : Z) (s' : list Z),
  (forall a, FIXA a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5.u8_at (hl_segs L) M' (P + 209) sst' -> L5.u8_at (hl_segs L) M' (P + 211) (PML.b2z more') ->
  PMLA.str_at (hl_segs L) M' (P + 224) (PML.SLong cc pp s') -> 264 <= cc ->
  (forall i, 0 <= i < 272 -> M' (Z_to_bv 64 (P + i)) <> None) ->
  PMLA.parser_at (hl_segs L) IC M' P (PML.ps_set_win (PML.PS PML.ST_STRING sst' nst more' (PML.ps_done ps) level stack sb scap cc pp s' (Some (q, e))) (PML.ps_win ps)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_165 ())).
Qed.

(* [comment removed for export] *)
Definition SAFE (i : nat) (E1 : env) (a : Z) : Prop :=
  (0 <= a < 7094272) \/ FIXA a \/ (P + 224 <= a < P + 248) \/ (E <= a < E + 16) \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a.
Lemma SAFEOUT : forall i E1 A1 M1 m1 E' a, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  CL5A.uv E' FE = CL5A.uv E1 FE -> CL5A.uv E' FLE = CL5A.uv E1 FLE -> FLF E1 -> sbI i E1 = sb -> scapI i E1 = scap -> SAFE i E1 a -> 0 <= a < 2 ^ 64 /\ outU E' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_166 ())).
Qed.

(* [comment removed for export] *)
Lemma AGFIX_mv : forall (M1 M2 : mem), (forall a, FIXA a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> AGFIX M1 -> AGFIX M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_167 ())).
Qed.
Lemma STR_mv : forall i E1 (M1 M2 : mem),
  (forall a, (P + 224 <= a < P + 248) \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  0 <= bptrI i E1 -> bptrI i E1 + bcapI i E1 <= 2 ^ 64 -> bptrI i E1 mod 8 = 0 ->
  STR i E1 M1 -> STR i E1 M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_168 ())).
Qed.
Definition STATIC (a : Z) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 (ParseStringXBW_blobs1.kr_b_169 ())).
Lemma STATIC_lo : forall a, STATIC a -> 0 <= a < 7094272.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_170 ())).
Qed.
Lemma LS_mv : forall gl (M1 M2 : mem), (forall a, STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> gl <> PML.LS0 ->
  PMLA.ls_ok (hl_segs L) IC gl M1 -> PMLA.ls_ok (hl_segs L) IC gl M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_171 ())).
Qed.
Lemma EC_mv : forall code (M1 M2 : mem), (forall a, E <= a < E + 16 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_172 ())).
Qed.
Lemma PH0_mv : forall (M1 M2 : mem), (forall a, (E <= a < E + 16) \/ a = P + 211 \/ STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PH0 M1 -> PH0 M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_173 ())).
Qed.
Lemma PHA_mv : forall v (M1 M2 : mem), (forall a, (E <= a < E + 16) \/ a = P + 211 \/ STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PHA v M1 -> PHA v M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_174 ())).
Qed.
Lemma PHS_mv : forall (M1 M2 : mem), (forall a, (E <= a < E + 16) \/ STATIC a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PHS M1 -> PHS M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_175 ())).
Qed.

(* [comment removed for export] *)
Section Out.
Variables (E' : env) (a : Z).
Hypothesis W2 : bv_unsigned (ev E' 2) = sp.
Hypothesis W10 : bv_unsigned (ev E' 10) = P.
Hypothesis Ha : 0 <= a < 2 ^ 64.
Let F := CL5A.uv E' (EVar 55).
Let fl := CL5A.uv E' (EVar 50).
Ltac outgo := unfold PSA.CPF_N, PSA.CPF_NM, PSA.CPF_MM, PSA.CPF_E, PSA.CPF_X; unfold PSA.F0, PSA.FRM3, PSA.FLR, PSA.MORE; unfold PSA.PE, PSA.FE, PSA.FLE, CHA.SRL3, PSA.SBz, SGP.outside; cbn [app];
  repeat (apply Forall_cons); try (apply Forall_nil); rewrite ?CL5A.estart_srl3'; unfold estart, elenZ, CL5A.uv; cbn [a_base a_off edenot]; rewrite ?(L5.unsigned_lit a Ha).
Lemma OUT_0 : (a < sp - 16896 \/ sp <= a) -> ~ (P + 148 <= a < P + 156) -> ~ (P + 168 <= a < P + 176) -> a <> P + 209 -> a <> P + 220 -> SGP.outside E' PSA.F0 (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_176 ())).
Qed.
Lemma OUT_N : (a < sp - 16896 \/ sp <= a) -> ~ (P + 148 <= a < P + 156) -> ~ (P + 168 <= a < P + 176) -> a <> P + 209 -> a <> P + 220 ->
  ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PSA.CPF_N (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_177 ())).
Qed.
Lemma OUT_NM : (a < sp - 16896 \/ sp <= a) -> ~ (P + 148 <= a < P + 156) -> ~ (P + 168 <= a < P + 176) -> a <> P + 209 -> a <> P + 211 -> a <> P + 220 ->
  ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PSA.CPF_NM (Z_to_bv 64 a) /\ SGP.outside E' PSA.CPF_MM (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_178 ())).
Qed.
Lemma OUT_E : (a < sp - 16896 \/ sp <= a) -> ~ (F <= a < F + 128) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> SGP.outside E' PSA.CPF_E (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_179 ())).
Qed.
Lemma OUT_X : (a < sp - 16896 \/ sp <= a) -> ~ (F <= a < F + 24) -> ~ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 16) -> a <> fl -> SGP.outside E' PSA.CPF_X (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_180 ())).
Qed.
Lemma OUT_FL : F + 120 <= a < F + 128 -> F + 128 <= sp - 16896 -> (P + 272 <= F \/ F + 128 <= P) -> (F + 128 <= 2147446784 \/ 17594333495296 <= F) -> F + 128 <= 2 ^ 47 ->
  SGP.outside E' PSA.CPF_N (Z_to_bv 64 a) /\ SGP.outside E' PSA.CPF_NM (Z_to_bv 64 a) /\ SGP.outside E' PSA.CPF_MM (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_181 ())).
Qed.
End Out.

(* [comment removed for export] *)
Lemma BLKAG : forall i c E1 E', nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' ->
  bptrI i E' = bptrI i E1 /\ bcapI i E' = bcapI i E1 /\ sbI i E' = sbI i E1 /\ scapI i E' = scapI i E1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_182 ())).
Qed.
Lemma GBLK : forall i c k ps0 j s E', CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 78)%nat ->
  let E'' := CC.env_over GT.NF s E' in
  bptrI j E'' = bptrI i E' /\ bcapI j E'' = bcapI i E' /\ sbI j E'' = sbI i E' /\ scapI j E'' = scapI i E'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_183 ())).
Qed.
(* [comment removed for export] *)
Lemma G_CRED : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 78)%nat ->
  forall E1 E' R' M1 M' cr1, env_agree GT.NF E0 E1 -> env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps0 E' R' M1 M' -> Cred g1 i E1 cr1 -> Cred g1 j (CC.env_over GT.NF s E') cr1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_184 ())).
Qed.

(* [comment removed for export] *)
Lemma POUT : forall i E1 A1 M1 m1 k, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 -> FLF E1 -> 0 <= k < 272 ->
  let F := CL5A.uv E1 (EVar 55) in
  P + k < sp - 16896 /\ ~ (F <= P + k < F + 128) /\ ~ (F / 8 + 2147450880 <= P + k < F / 8 + 2147450880 + 16) /\ P + k <> CL5A.uv E1 (EVar 50).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_185 ())).
Qed.
(* [comment removed for export] *)
Lemma STR_eqv : forall i j E1 E2 Mx, bptrI j E2 = bptrI i E1 -> bcapI j E2 = bcapI i E1 -> sbI j E2 = sbI i E1 -> scapI j E2 = scapI i E1 -> STR i E1 Mx -> STR j E2 Mx.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_186 ())).
Qed.
(* [comment removed for export] *)
Lemma over_ge : forall s E' v, (50 <= v)%nat -> ev (CC.env_over GT.NF s E') v = edenot E' (CC.slook s v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_187 ())).
Qed.
Lemma over_lt : forall s E' v, (v < 50)%nat -> ev (CC.env_over GT.NF s E') v = ev E' v.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_188 ())).
Qed.
(* [comment removed for export] *)
Lemma PROVE : forall c ps0 E' R' A1 M1 m1 M' m' ex lo hi, CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  PSA.prove (SR.ps_cells ps0) (KRange ex lo hi) = true -> lo <= CL5A.uv E' ex <= hi.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_189 ())).
Qed.

(* [comment removed for export] *)
Lemma DECL_CORE : forall i j s c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 78)%nat -> (j <= 78)%nat -> CC.slook s 50 = PSA.FLE -> CC.cp_F c = PSA.CPF_N -> PSA.kind_of j = PSA.KDecl ->
  (let E'' := CC.env_over GT.NF s E' in bptrI j E'' = bptrI i E' /\ bcapI j E'' = bcapI i E' /\ sbI j E'' = sbI i E' /\ scapI j E'' = scapI i E') ->
  match PSA.kind_of i with PSA.KSm | PSA.KDecl | PSA.KPushb | PSA.KAppend | PSA.KConvert => True | PSA.KAtc => PSA.prove (SR.ps_cells ps0) (KRange (EVar (PSA.ecv i)) 0 0) = true | _ => False end ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIj i E1 A1 M1 m1 -> XIj j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_190 ())).
Qed.

(* [comment removed for export] *)
Lemma G_DECL : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PSA.kind_of j = PSA.KDecl ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIj i E1 A1 M1 m1 -> XIj j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_191 ())).
Qed.

(* [comment removed for export] *)
Lemma UVR : forall Ex e0, 0 <= CL5A.uv Ex e0 < 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_192 ())).
Qed.
Lemma U64INJ : forall (Mx : mem) a v1 v2, L5.u64_at (hl_segs L) Mx a v1 -> L5.u64_at (hl_segs L) Mx a v2 -> 0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_193 ())).
Qed.
(* [comment removed for export] *)
Lemma SUBR : forall x y lo hi, 0 <= x < 2 ^ 62 -> 0 <= y < 2 ^ 62 -> lo <= (x - y) mod 2 ^ 64 <= hi -> 0 <= lo -> hi < 2 ^ 62 -> lo <= x - y <= hi.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_194 ())).
Qed.
Lemma MODB : forall X, 0 <= X <= 2 ^ 28 -> 0 <= (B - X) mod 2 ^ 64 <= 67108864 -> X <= B.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_195 ())).
Qed.
Lemma WF_mk : forall sst' (more' : bool) cc pp bf w, 0 <= sst' <= 11 -> (more' = true -> PML.ps_more ps = true) ->
  PML.wf_ps (PML.PS PML.ST_STRING sst' nst more' (PML.ps_done ps) level stack sb scap cc pp bf w).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_196 ())).
Qed.
(* [comment removed for export] *)
Lemma RD8 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PSA.PE k) 1 v) -> L5.u8_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_197 ())).
Qed.
Lemma RD64 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PSA.PE k) 8 v) -> L5.u64_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_198 ())).
Qed.
(* [comment removed for export] *)
Lemma cell_at_has : forall cells b k w v, CAX.cell_at cells b k w = Some v -> In (KWord (SA b k) w v) cells.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_199 ())).
Qed.
Lemma esc_need_nth : forall z, 0 <= z <= 11 -> nth (Z.to_nat z) PSA.ESC_NEED 0 = PML.esc_need z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_200 ())).
Qed.

(* [comment removed for export] *)
Lemma G_RETX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PSA.kind_of j = PSA.KRetx -> PSA.kind_of i <> PSA.KEsv ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIj i E1 A1 M1 m1 -> XIj j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_201 ())).
Qed.

(* [comment removed for export] *)
Definition SAFE2 (i : nat) (E1 : env) (a : Z) : Prop :=
  (0 <= a < 7094272) \/ (P <= a < P + 272) \/ (E <= a < E + 16)
  \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a
  \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a
  \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a.
Lemma SAFEOUT2 : forall i E1 A1 M1 m1 E' a, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  CL5A.uv E' FE = CL5A.uv E1 FE -> SAFE2 i E1 a ->
  0 <= a < 2 ^ 64 /\ (a < sp - 16896 \/ sp <= a) /\ ~ (CL5A.uv E' (EVar 55) <= a < CL5A.uv E' (EVar 55) + 128) /\ ~ (CL5A.uv E' (EVar 55) / 8 + 2147450880 <= a < CL5A.uv E' (EVar 55) / 8 + 2147450880 + 16)
  /\ (FLF E1 -> a <> CL5A.uv E1 (EVar 50)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_202 ())).
Qed.

Ltac u64 AGS OPS H := apply (PTA.u64_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].
Ltac u32 AGS OPS H := apply (PTA.u32_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].
Ltac u8 AGS OPS H := apply (PTA.u8_ag _ _ _ _ AGS); [apply OPS; clear; lia | exact H].
(* [comment removed for export] *)
Lemma G_RETX_ESV : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PSA.kind_of j = PSA.KRetx -> PSA.kind_of i = PSA.KEsv ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIj i E1 A1 M1 m1 -> XIj j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_203 ())).
Qed.

(* [comment removed for export] *)
Lemma ECINJ : forall (Mx : mem) c1 c2, PMLA.ec_at (hl_segs L) IC Mx E c1 -> PMLA.ec_at (hl_segs L) IC Mx E c2 -> c1 = c2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_204 ())).
Qed.
Lemma EOUT : forall i c ps0 E1 A1 M1 m1 E' R' M' m', (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 ->
  forall a, E <= a < E + 16 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_205 ())).
Qed.
Lemma GX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XI g1 i E1 A1 M1 m1 -> XIj j (CC.env_over GT.NF s E') A1 M' m' -> XI g1 j (CC.env_over GT.NF s E') A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_206 ())).
Qed.

Lemma GXD : forall i j c ps0 E1 A1 M1 m1 E' R' M' m' E2, (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  PSA.kind_of i = PSA.KDecl -> PSA.kind_of j = PSA.KDecl -> XI g1 i E1 A1 M1 m1 -> XIj j E2 A1 M' m' -> XI g1 j E2 A1 M' m'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_207 ())).
Qed.
(* [comment removed for export] *)
Lemma XOUT0 : forall c ps0 E1 A1 M1 m1 E' R' M' m', nth_error G.CPS 0 = Some c ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 0%nat E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> CC.cp_F c = PSA.F0 ->
  forall a, xfoot g1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a) /\ (0 <= a < 2 ^ 64 /\ aclient L ar (PML.ps_blocks ps ++ LBV g1) FF (sp + -288) 512 a).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_208 ())).
Qed.

(* [comment removed for export] *)
Lemma PA_ag : forall (M1 M2 : mem) (S : Z -> Prop) psx, (forall a, S a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, P <= a < P + 272 -> S a) -> (forall a, PML.ps_bptr psx <= a < PML.ps_bptr psx + PML.ps_bcap psx -> S a) ->
  (forall a, PML.ps_sb psx <= a < PML.ps_sb psx + PML.ps_scap psx -> S a) ->
  0 <= PML.ps_bptr psx -> PML.ps_bptr psx + PML.ps_bcap psx <= 2 ^ 64 -> 0 <= PML.ps_sb psx -> PML.ps_sb psx + PML.ps_scap psx <= 2 ^ 64 ->
  PMLA.parser_at (hl_segs L) IC M1 P psx -> PMLA.parser_at (hl_segs L) IC M2 P psx.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_209 ())).
Qed.
Lemma POSTP_mv : forall i E1 A1 M1 m1 (M2 : mem) q, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  (forall a, SAFE2 i E1 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None) ->
  POSTP M1 q (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) -> POSTP M2 q (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_210 ())).
Qed.

(* [comment removed for export] *)
Lemma GK : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j <= 78)%nat /\ (PSA.kind_of j = PSA.KDecl \/ PSA.kind_of j = PSA.KRetx).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_211 ())).
Qed.

(* [comment removed for export] *)
Definition AMBX := CHV.ambXV L ar HI GT.NF E0 model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred XIW g1 M0c.      (* [comment removed for export] *)
Lemma AMBXE : AMBX = CHA.ambX L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 (XIW g1). Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_212 ())).
Qed.
(* [comment removed for export] *)
Definition LEAF (pc : Z) : Prop := forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) ->
  CHV.leaf_okV L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred XIW G.CPS K PMSA.fp_ok g1 M0c i c ps0.
Lemma LEAFV_of : forall i c ps0, CCA.leaf_ok (hl_segs L) G.CPS AMBX K PMSA.fp_ok i c ps0 -> CHV.leaf_okV L ar HI GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSA.FFS 10 PMES.eghost PMES.g_lbv Cred XIW G.CPS K PMSA.fp_ok g1 M0c i c ps0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_213 ())).
Qed.
(* [comment removed for export] *)
Lemma SZC : forall i c E1 R1 A1 M1 m1 s1, (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c -> PSA.szok c = true ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  PMLA.str_at (hl_segs L) M1 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) -> bcapI i E1 <= 2 ^ 27 ->
  CL5A.uv E1 (PSA.szc c) = Z.of_nat (length s1) /\ APC.expr_vars_lt (CC.cp_nx c) (PSA.szc c) = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_214 ())).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma WBUFZ : forall i c E1 R1 A1 M1 m1, (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c -> PSW.bufkind (PSW.KD i) = true ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  STR i E1 M1 -> forall a, BUFZ i E1 a -> bptrI i E1 <= a < bptrI i E1 + bcapI i E1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_215 ())).
Qed.
(* [comment removed for export] *)
Lemma WSAME : forall i j c E1 R1 A1 M1 m1 E2 (M2 : mem), (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c -> PSW.lowcells i = true ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  STR i E1 M1 -> PSW.KD j = PSW.KD i -> ((exists sst cc, PSW.KD i = PSW.KStep sst cc) \/ PSW.KD i = PSW.KText) -> PSW.same_cells i j = true ->
  env_agree 62 E1 E2 -> (forall a, bptrI i E1 <= a < bptrI i E1 + bcapI i E1 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  SIM g1 i E1 M1 -> SIM g1 j E2 M2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_216 ())).
Qed.
(* [comment removed for export] *)
Lemma WBUFID : forall i c E1 R1 A1 M1 m1 s1 o, (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c -> PSW.bufkind (PSW.KD i) = true ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  PMLA.str_at (hl_segs L) M1 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) -> bcapI i E1 <= 2 ^ 27 -> BUFL i E1 M1 o ->
  PMR.b256 s1 = PMR.b256 (BUFB o) /\ Z.of_nat (length s1) = Z.of_nat (length (BUFB o)) /\ CL5A.uv E1 (PSA.szc c) = Z.of_nat (length (BUFB o)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_217 ())).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma VIEWM : forall (Mx : mem) psv w0 (stv ssv nsv : Z) (dn : bool) (sbx : Z) (stk : list Z),
  PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win psv w0) -> PML.wf_ps psv -> PML.ps_more psv = true ->
  L5.u8_at (hl_segs L) Mx (P + 208) stv -> 0 <= stv <= 255 ->
  L5.u8_at (hl_segs L) Mx (P + 209) ssv -> 0 <= ssv <= 11 ->
  L5.u8_at (hl_segs L) Mx (P + 210) nsv -> 0 <= nsv <= 7 ->
  L5.u8_at (hl_segs L) Mx (P + 212) (PML.b2z dn) ->
  PML.ps_sb psv = sbx -> 0 <= sbx -> sbx + 2048 <= 2 ^ 64 ->
  L5.u64_at (hl_segs L) Mx (P + 256) (sbx + Z.of_nat (length stk)) -> L5.bytes_at (hl_segs L) Mx sbx stk -> Forall (fun x => 0 <= x <= 255) stk -> (length stk <= 1027)%nat ->
  PML.ps_st psv = stv /\ PML.ps_sst psv = ssv /\ PML.ps_nst psv = nsv /\ PML.ps_done psv = dn /\ PML.ps_stack psv = stk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_218 ())).
Qed.
Lemma VIEWB : forall (Mx : mem) psv w0 (nx ptr : Z) (lx : list Z),
  PMLA.parser_at (hl_segs L) IC Mx P (PML.ps_set_win psv w0) -> PML.ps_bcap psv < 2 ^ 63 ->
  L5.u64_at (hl_segs L) Mx (P + 232) nx -> Z.of_nat (length lx) = nx -> 0 <= nx < 2 ^ 64 -> L5.bytes_at (hl_segs L) Mx ptr lx -> PML.ps_bptr psv = ptr ->
  PMR.b256 (PML.ps_buf psv) = PMR.b256 lx /\ length (PML.ps_buf psv) = length lx.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_219 ())).
Qed.
(* [comment removed for export] *)
Lemma w3s_ag : forall (M1 M2 : mem) (SS : Z -> Prop) ps' g1' code p' e',
  (forall a, SS a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, P <= a < P + 272 -> SS a) -> (forall a, ch <= a < ch + 16384 -> SS a) ->
  PML.ps_win ps' = Some (p', e') -> ch <= p' -> e' <= ch + 16384 ->
  PSKW.w3s L cw winb M1 P ps ps' eg g1' code -> PSKW.w3s L cw winb M2 P ps ps' eg g1' code.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_220 ())).
Qed.

(* [comment removed for export] *)
Lemma RD32 : forall E' A1 m' (M' : mem) k v, H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P ->
  kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') (KWord (SA PSA.PE k) 4 v) -> L5.u32_at (hl_segs L) M' (P + k) (CL5A.uv E' v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_221 ())).
Qed.
(* [comment removed for export] *)
Lemma TOK0 : PSKW.tok_ok cw (PMR.b256 buf).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_222 ())).
Qed.
(* [comment removed for export] *)
Lemma TAGC : forall i c ps0 E1 E' A1 m' (M' : mem), nth_error G.CPS i = Some c -> (i < 79)%nat -> env_agree (CC.cp_nx c) E1 E' ->
  H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P -> (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0) ->
  PSWR.tagcP i (SR.ps_cells ps0) -> TAGL i E1 -> exists tg, L5.u8_at (hl_segs L) M' (P + 220) tg /\ 0 <= tg <= 1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_223 ())).
Qed.
Lemma Forall_skipn_Z : forall (Pz : Z -> Prop) (n : nat) (l : list Z), Forall Pz l -> Forall Pz (skipn n l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_224 ())).
Qed.
Lemma Forall_firstn_Z : forall (Pz : Z -> Prop) (n : nat) (l : list Z), Forall Pz l -> Forall Pz (firstn n l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_225 ())).
Qed.

Lemma rows_ok2 : forallb (fun rw => expr_eqb (CC.slook (CSLR.r_sid rw) 50) PSA.FLE && Nat.leb (CSLR.r_j rw) 78 && PSA.kind_eqb (PSA.kind_of (CSLR.r_j rw)) PSA.KDecl
                                   && PSA.kind_eqb (PSA.kind_of (CSLR.r_i rw)) PSA.KDecl && Nat.leb 1 (CSLR.r_i rw) && Nat.leb (CSLR.r_i rw) 78)%bool PSA.ROWS = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_226 ())).
Qed.
(* [comment removed for export] *)
Lemma L_CSL : forall pc, pc <> PSA.RETPC -> pc <> PSA.PC_SM -> pc <> PSA.PC_ERRH -> pc <> PSA.PC_SETEC -> pc <> PSA.PC_ATC -> pc <> PSA.PC_PUSHB -> pc <> PSA.PC_APPEND -> pc <> PSA.PC_CONVERT -> pc <> PSA.PC_ESV -> LEAF pc.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_227 ())).
Qed.

(* [comment removed for export] *)
Lemma KRETX28 : forall i, PSA.kind_of i = PSA.KRetx -> i = 28%nat.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_228 ())).
Qed.
Lemma L_EXIT : LEAF PSA.RETPC.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_229 ())).
Qed.

(* [comment removed for export] *)
Definition SAFE0 (a : Z) : Prop :=
  (0 <= a < 7094272) \/ FIXA a \/ (P + 224 <= a < P + 248) \/ (E <= a < E + 16) \/ (bptr <= a < bptr + bcap) \/ in_shadow_of bptr bcap a \/ a = P + 211.
Lemma SAFEOUT0 : forall a, SAFE0 a -> 0 <= a < 2 ^ 64 /\ (a < sp - 16896 \/ sp <= a) /\ ~ (P + 148 <= a < P + 156) /\ ~ (P + 168 <= a < P + 176) /\ a <> P + 209 /\ a <> P + 220.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_230 ())).
Qed.

(* [comment removed for export] *)
Lemma ACL : forall a sp' scr',
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (bptr <= a < bptr + bcap) \/ in_shadow_of bptr bcap a \/ (sb <= a < sb + scap) \/ in_shadow_of sb scap a \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_231 ())).
Qed.

(* [comment removed for export] *)
Lemma L_SM : LEAF PSA.PC_SM.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_232 ())).
Qed.

(* [comment removed for export] *)
Lemma NEWSF : forall E' E2 A1 A2 (M' M2 : mem) m' m2 LKa LKb cra crb LB1 LB2 F fl,
  ri_inv HI LB1 ((F, 1, sp + -288 + 32) :: FF) LKa cra A1 M' (vml_of m') -> ri_inv HI LB2 ((F, 1, sp + -288 + 32) :: FF) LKb crb A2 M2 (vml_of m2) ->
  H_off_segments (hl_segs L) (ahid A1 m') ->
  0 <= F -> F + 128 <= 140737488355328 -> ar_fs ar <= F -> F + 128 <= ar_fs ar + 11571200 -> ar_fs ar <= fl < ar_fs ar + 11571200 ->
  bv_unsigned (ev E' 55) = F -> bv_unsigned (ev E' 50) = fl -> bv_unsigned (ev E2 55) = F -> bv_unsigned (ev E2 50) = fl ->
  L5.u64_at (hl_segs L) M' (F + 120) fl ->
  forall X0, In X0 PSA.NEWS_F -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_233 ())).
Qed.

(* [comment removed for export] *)
Lemma STKSH : forall (M' : mem) scr, (forall a, CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  0 <= scr -> scr mod 8 = 0 -> 288 + scr <= 16896 -> PMLA.stksh ar M' (sp + -288) scr.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_234 ())).
Qed.

(* [comment removed for export] *)
Lemma U8DEF : forall (Mx : mem) a v, L5.u8_at (hl_segs L) Mx a v -> hl_img_hi L <= a -> 0 <= a < 2 ^ 64 -> Mx (Z_to_bv 64 a) <> None.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_235 ())).
Qed.
(* [comment removed for export] *)
Lemma ACLI : forall i E1 A1 M1 m1 a sp' scr', (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a
  \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar (CHA.curB (LBV g1) G.BLS i E1) (CHA.curF FF sp PSA.FFS i E1) sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_236 ())).
Qed.
(* [comment removed for export] *)
Definition CSET (i : nat) (E1 : env) (a : Z) : Prop :=
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a
  \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a.
Lemma FIX_CSET : forall i E1 a, sbI i E1 = sb -> scapI i E1 = scap -> FIXA a -> CSET i E1 a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_237 ())).
Qed.
(* [comment removed for export] *)
Definition OSET (i : nat) (E1 : env) (a : Z) : Prop :=
  FIXA a \/ (P + 224 <= a < P + 248) \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a.
Lemma OSET_CSET : forall i E1 a, sbI i E1 = sb -> scapI i E1 = scap -> OSET i E1 a -> CSET i E1 a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_238 ())).
Qed.
Lemma KEEP_FS : forall i E1 (M' M2 : mem), 0 <= bptrI i E1 -> bptrI i E1 + bcapI i E1 <= 2 ^ 64 -> bptrI i E1 mod 8 = 0 ->
  (forall a, OSET i E1 a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
  (AGFIX M' -> AGFIX M2) /\ (STR i E1 M' -> STR i E1 M2).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_239 ())).
Qed.
Lemma KEEP_PH : forall (M' M2 : mem), (forall a, (E <= a < E + 16) \/ a = P + 211 \/ STATIC a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
  (PH0 M' -> PH0 M2) /\ (PHS M' -> PHS M2) /\ (forall v, PHA v M' -> PHA v M2).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_240 ())).
Qed.
(* [comment removed for export] *)
Lemma OSET_OUT : forall i E1 A1 M1 m1 a, (1 <= i <= 78)%nat ->
  CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 -> sbI i E1 = sb -> scapI i E1 = scap ->
  OSET i E1 a -> ~ (E <= a < E + 16) /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ a <> P + 211.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_241 ())).
Qed.
(* [comment removed for export] *)
Lemma FL64 : forall i c E1 R1 A1 M1 m1 (M' : mem) (V' : vml) LB1 LKa cra Ax, (1 <= i <= 78)%nat -> nth_error G.CPS i = Some c ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  ri_inv HI LB1 ((CL5A.uv E1 FE, 1, sp + -288 + 32) :: FF) LKa cra Ax M' V' ->
  L5.u64_at (hl_segs L) M' (CL5A.uv E1 FE + 120) (CL5A.uv E1 FLE).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_242 ())).
Qed.
(* [comment removed for export] *)
Lemma RBLK : forall i j c E1 E2, nth_error G.CPS i = Some c -> nth j G.BLS [] = nth i G.BLS [] -> env_agree (CC.cp_nx c) E1 E2 ->
  bptrI j E2 = bptrI i E1 /\ bcapI j E2 = bcapI i E1 /\ sbI j E2 = sbI i E1 /\ scapI j E2 = scapI i E1 /\ CHA.curB (LBV g1) G.BLS j E2 = CHA.curB (LBV g1) G.BLS i E1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_243 ())).
Qed.
Lemma RETBLS : forall i k j, CH2.ret_of G.RETS i k = Some j -> (PSA.kind_of j = PSA.KErrh \/ PSA.kind_of j = PSA.KSetec \/ PSA.kind_of j = PSA.KAtc) -> nth j G.BLS [] = nth i G.BLS [].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_244 ())).
Qed.
(* [comment removed for export] *)
Lemma PHASE_X : forall i c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 78)%nat ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 -> STR i E1 M1 ->
  (forall a, SAFE i E1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\
  0 <= bptrI i E1 /\ bptrI i E1 + bcapI i E1 <= 2 ^ 64 /\ bptrI i E1 mod 8 = 0 /\
  (AGFIX M1 -> AGFIX M') /\ STR i E1 M' /\ (PHS M1 -> PHS M') /\
  (forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M' E code) /\
  (forall g1, g1 <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC g1 M1 -> PMLA.ls_ok (hl_segs L) IC g1 M').
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_245 ())).
Qed.
(* [comment removed for export] *)
Lemma PHASE0_X : forall i c ps0 E1 R1 E' R' A1 M1 m1 M' m',
  nth_error G.CPS i = Some c -> (1 <= i <= 78)%nat -> (CC.cp_F c = PSA.F0 \/ CC.cp_F c = PSA.CPF_N) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> FLF E1 -> STR i E1 M1 ->
  (forall a, SAFE i E1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\ M' (Z_to_bv 64 (P + 211)) = M1 (Z_to_bv 64 (P + 211)) /\
  0 <= bptrI i E1 /\ bptrI i E1 + bcapI i E1 <= 2 ^ 64 /\ bptrI i E1 mod 8 = 0 /\
  (AGFIX M1 -> AGFIX M') /\ STR i E1 M' /\ (PH0 M1 -> PH0 M') /\ (PHS M1 -> PHS M') /\ (forall v, PHA v M1 -> PHA v M').
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_246 ())).
Qed.

(* [comment removed for export] *)
Lemma L_ERRH : LEAF PSA.PC_ERRH.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_247 ())).
Qed.
Lemma L_SETEC : LEAF PSA.PC_SETEC.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs1.kr_b_248 ())).
Qed.

(* [comment removed for export] *)
Lemma L_ATC : LEAF PSA.PC_ATC.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_249 ())).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ACLX : forall LBx FFx a sp' scr', incl FF FFx -> In (sb, scap) LBx -> In (ch, 16384) LBx ->
  (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) \/ in_shadow_of P 272 a \/ in_shadow_of E 16 a \/ in_shadow_of V 8 a
  \/ (sb <= a < sb + scap) \/ in_shadow_of sb scap a \/ (ch <= a < ch + 16384) \/ in_shadow_of ch 16384 a \/ STATIC a ->
  0 <= a < 2 ^ 64 /\ aclient L ar LBx FFx sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_250 ())).
Qed.
(* [comment removed for export] *)
Lemma ACLP : forall LBx FFx a sp' scr', incl FF FFx -> (P <= a < P + 272) \/ (E <= a < E + 16) \/ (V <= a < V + 8) -> 0 <= a < 2 ^ 64 /\ aclient L ar LBx FFx sp' scr' a.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_251 ())).
Qed.
(* [comment removed for export] *)
Lemma FIX_OUT224 : forall a, FIXA a -> ~ (P + 224 <= a < P + 248).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_252 ())).
Qed.
(* [comment removed for export] *)
Lemma UV_eaddz : forall Ex ex z, CL5A.uv Ex (APC.eaddz ex z) = (CL5A.uv Ex ex + z) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_253 ())).
Qed.
Lemma UV_eadd : forall Ex a b, CL5A.uv Ex (APC.eadd a b) = (CL5A.uv Ex a + CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_254 ())).
Qed.
Lemma UV_esub : forall Ex a b, CL5A.uv Ex (APC.esub a b) = (CL5A.uv Ex a - CL5A.uv Ex b) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_255 ())).
Qed.
Lemma UV_escale2 : forall Ex ex, CL5A.uv Ex (APC.escale 2 ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_256 ())).
Qed.
Lemma UV_mul2 : forall Ex ex, CL5A.uv Ex (EMd Instr.M_MUL (ELit 2) ex) = (2 * CL5A.uv Ex ex) mod 2 ^ 64.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_257 ())).
Qed.
(* [comment removed for export] *)
Lemma STRS_mv : forall i E1 (M1 M2 : mem) s1,
  (forall a, (P + 224 <= a < P + 248) \/ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) \/ in_shadow_of (bptrI i E1) (bcapI i E1) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  0 <= bptrI i E1 -> bptrI i E1 + bcapI i E1 <= 2 ^ 64 -> bptrI i E1 mod 8 = 0 -> bcap <= bcapI i E1 ->
  PMLA.str_at (hl_segs L) M1 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) -> shadow_blk M1 (bptrI i E1) (bcapI i E1) ->
  PMLA.str_at (hl_segs L) M2 (P + 224) (PML.SLong (bcapI i E1) (bptrI i E1) s1) /\ shadow_blk M2 (bptrI i E1) (bcapI i E1).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_258 ())).
Qed.
(* [comment removed for export] *)
Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_259 ())).
Qed.
Lemma grow_cap_facts : forall cap need, 24 <= cap -> cap mod 8 = 0 -> cap <= 2 ^ 26 -> 0 <= need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in 2 * cap <= c /\ need < c /\ c <= 2 ^ 27 /\ c mod 8 = 0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_260 ())).
Qed.
Lemma log2_halves : forall cap c, 24 <= cap -> 2 * cap <= c -> c <= 2 ^ 27 -> Z.log2 (2 ^ 27 / c) + 1 <= Z.log2 (2 ^ 27 / cap).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_261 ())).
Qed.
Lemma bufcredA_push : forall cr1 cap kx' bx' need, PMSA.bufcredA L cr1 cap kx' bx' -> 24 <= cap -> cap mod 8 = 0 -> cap <= need -> need < 2 ^ 26 ->
  let c := PML.grow_cap cap need in
  acredit_ok L cr1 c /\ PMSA.bufcredA L (adebit L cr1 c) c kx' bx' /\ 2 * cap <= c /\ need < c /\ c mod 8 = 0.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_262 ())).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma L_PUSHB : LEAF PSA.PC_PUSHB.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_263 ())).
Qed.

(* [comment removed for export] *)
Lemma bytes_sub : forall (Mx : mem) q bs kk n, L5.bytes_at (hl_segs L) Mx q bs -> (kk + n <= length bs)%nat -> L5.bytes_at (hl_segs L) Mx (q + Z.of_nat kk) (firstn n (skipn kk bs)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_264 ())).
Qed.
Lemma sr_vars_lt_forallb : forall n l, APC.sr_vars_lt n l = forallb (APC.expr_vars_lt n) l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_265 ())).
Qed.
Lemma REGV : forall ps0 n rg ex, APC.sr_vars_lt n (CA.ps_reglist ps0) = true -> (1 <= rg <= 31)%nat -> PSA.reg_of ps0 rg = ex -> ex <> ELit (-1) -> APC.expr_vars_lt n ex = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_266 ())).
Qed.
Lemma nodup_notin : forall (x : Z) (l : list Z), base.NoDup (x :: l) -> ~ In x l.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_267 ())).
Qed.

(* [comment removed for export] *)
Lemma L_APPEND : LEAF PSA.PC_APPEND.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_268 ())).
Qed.

(* [comment removed for export] *)
Lemma zlb_mod : forall n z, Z_to_le_bytes n z = Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_269 ())).
Qed.
Lemma u32_mod : forall (Mx : mem) a x, L5.u32_at (hl_segs L) Mx a x -> L5.u32_at (hl_segs L) Mx a (x mod 2 ^ 32).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_270 ())).
Qed.

(* [comment removed for export] *)
Lemma L_CONVERT : LEAF PSA.PC_CONVERT.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_271 ())).
Qed.

(* [comment removed for export] *)
Lemma L_ESV : LEAF PSA.PC_ESV.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_272 ())).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma VIEW_RM : forall (M2 : mem) E2 psv c1 o1 sstv tg,
  AGFIX M2 -> PMLA.parser_at (hl_segs L) IC M2 P (PML.ps_set_win psv (PML.ps_win ps)) -> PML.wf_ps psv -> PML.ps_more psv = true -> PML.ps_level psv = PML.ps_level ps ->
  PML.ps_blocks psv = [(bptrI 28 E2, bcapI 28 E2); (sbI 28 E2, scapI 28 E2)] -> sbI 28 E2 = sb -> PML.ps_bcap psv < 2 ^ 63 ->
  PSKW.core_eq cw c1 -> PSKW.tok_ok c1 (BUFB o1) -> Forall PSKW.inb o1 -> PMR.c_sst c1 = sstv ->
  L5.u8_at (hl_segs L) M2 (P + 209) sstv -> 0 <= sstv <= 11 -> L5.u8_at (hl_segs L) M2 (P + 220) tg -> 0 <= tg <= 1 ->
  (3 <= sstv <= 11 -> exists v, L5.u32_at (hl_segs L) M2 (P + 148) v /\ v mod 2 ^ 32 = PMR.c_cp c1 mod 2 ^ 32) ->
  (9 <= sstv <= 11 -> exists v, L5.u32_at (hl_segs L) M2 (P + 152) v /\ v mod 2 ^ 32 = PMR.c_cp2 c1 mod 2 ^ 32) ->
  L5.u64_at (hl_segs L) M2 (P + 232) (Z.of_nat (length (BUFB o1))) -> Z.of_nat (length (BUFB o1)) < 2 ^ 64 -> L5.bytes_at (hl_segs L) M2 (bptrI 28 E2) (BUFB o1) ->
  PMR.rm_core c1 psv /\ PML.ps_st psv = PML.ST_STRING /\ PMR.c_sst c1 = PML.ps_sst psv /\ PSKW.tok_ok c1 (PMR.b256 (PML.ps_buf psv)) /\
  (3 <= PMR.c_sst c1 <= 11 -> PMSA.u32 L M2 (P + 148) (PMR.c_cp c1)) /\ (9 <= PMR.c_sst c1 <= 11 -> PMSA.u32 L M2 (P + 152) (PMR.c_cp2 c1)) /\
  (exists t, PMSA.u8 L M2 (P + 220) t /\ 0 <= t <= 1).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_273 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_KIT : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  nth_error G.CPS i = Some c /\ (i < 79)%nat /\ (1 <= i <= 78)%nat /\ (j < 79)%nat /\
  ((PSA.kind_of j = PSA.KDecl /\ (1 <= j <= 27)%nat) \/ (PSA.kind_of j = PSA.KRetx /\ j = 28%nat)) /\
  bv_unsigned (ev E' 2) = sp /\ bv_unsigned (ev E' 10) = P /\ bv_unsigned (ev E' 11) = p /\ bv_unsigned (ev E' 32) = wlen /\
  H_off_segments (hl_segs L) (ahid A1 m1) /\ H_off_segments (hl_segs L) (ahid A1 m') /\ bv_unsigned (ev E1 10) = P /\
  CL5A.uv (CC.env_over GT.NF s E') (EVar 50) = CL5A.uv E1 (EVar 50) /\ CC.cp_F c = PSA.cpf_of_kind (PSA.kind_of i).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_274 ())).
Qed.
(* [comment removed for export] *)
Lemma UVO : forall s0 E2 (v : nat), (50 <= v)%nat -> CL5A.uv (CC.env_over GT.NF s0 E2) (EVar v) = CL5A.uv E2 (PSW.sub s0 v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_275 ())).
Qed.
Lemma UVOlt : forall s0 E2 (v : nat), (v < 50)%nat -> CL5A.uv (CC.env_over GT.NF s0 E2) (EVar v) = CL5A.uv E2 (EVar v).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_276 ())).
Qed.
(* [comment removed for export] *)
Lemma SG_SRC : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> match PSW.KD i with PSW.KEsv | PSW.KRetx | PSW.KBad => False | _ => True end ->
  AGFIX M1 /\ STR i E1 M1 /\ match PSW.KD i with PSW.KSetEc _ => PHS M1 | PSW.KAtc _ => PHA (ECV i E1) M1 | _ => PH0 M1 end /\ g1 = eg /\ AGFIX M' /\
  (forall a, SAFE i E1 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) /\
  (PSW.bufkind (PSW.KD i) = true -> forall o, BUFL i E1 M1 o -> L5.u64_at (hl_segs L) M' (P + 232) (Z.of_nat (length (BUFB o))) /\ Z.of_nat (length (BUFB o)) < 2 ^ 64 /\ L5.bytes_at (hl_segs L) M' (bptrI i E1) (BUFB o)) /\
  (forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M' E code).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_277 ())).
Qed.
(* [comment removed for export] *)
Lemma CPC : forall i c ps0 E1 E' A1 m' (M' : mem) c0 (off : Z) (getx : nat -> option expr) (getv : PMR.ctrl -> Z) (rng : Z -> Prop),
  nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' ->
  H_off_segments (hl_segs L) (ahid A1 m') -> bv_unsigned (ev E' 10) = P -> (forall X0, In X0 (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0) ->
  (forall ex, getx i = Some ex -> APC.expr_vars_lt (CC.cp_nx (PSW.cutn i)) ex = true) -> (exists ex, getx i = Some ex) ->
  (rng (PMR.c_sst c0) -> forall ex, getx i = Some ex -> CL5A.uv E1 ex mod 2 ^ 32 = getv c0 mod 2 ^ 32) ->
  (rng (PMR.c_sst c0) -> PSW.cellv (SR.ps_cells ps0) off 4 = getx i) ->
  rng (PMR.c_sst c0) -> exists v, L5.u32_at (hl_segs L) M' (P + off) v /\ v mod 2 ^ 32 = getv c0 mod 2 ^ 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_278 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_EXH : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' sst cc (istext : bool),
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> (PSW.KD i = PSW.KStep sst cc /\ istext = false) \/ (PSW.KD i = PSW.KText /\ sst = 0 /\ cc = 0 /\ istext = true) -> PSW.KD j = PSW.KRetx ->
  SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_279 ())).
Qed.
(* [comment removed for export] *)
Lemma WINSFX : forall (M2 : mem) (m : nat) psv, AGFIX M2 -> (m <= length winb)%nat -> PML.ps_win psv = Some (p + Z.of_nat m, e) -> PMXAW.win_bytesA L M2 psv (skipn m winb).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_280 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_SETECX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' code,
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KSetEc code -> PSW.KD j = PSW.KRetx -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_281 ())).
Qed.
Lemma SG_ATCX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' sst,
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KAtc sst -> PSW.KD j = PSW.KRetx -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_282 ())).
Qed.
(* [comment removed for export] *)
Lemma SG_RET4X : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KRet4 -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_283 ())).
Qed.
(* [comment removed for export] *)
Lemma SG_ENTRYX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KEntry -> PSW.KD j = PSW.KRetx -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_284 ())).
Qed.

(* [comment removed for export] *)
Lemma BUFL29 : forall E1 A1 M1 m1, CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 29%nat E1 A1 M1 m1 ->
  L5.bytes_at (hl_segs L) M1 bptr (BUFB []) -> BUFL 29%nat E1 M1 [].
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_285 ())).
Qed.
Lemma KENTRY29 : forall i, (1 <= i <= 78)%nat -> PSW.KD i = PSW.KEntry -> i = 29%nat.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_286 ())).
Qed.
(* [comment removed for export] *)
Lemma SG_ENTRY : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' sstj,
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KEntry -> PSW.KD j = PSW.KStep sstj 0 -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_287 ())).
Qed.
(* [comment removed for export] *)
Lemma TGT_TAGL : forall i c j s0 E1 E', nth_error G.CPS i = Some c -> (i < 79)%nat -> env_agree (CC.cp_nx c) E1 E' -> (1 <= j <= 27)%nat ->
  PSW.tag_ok i (PSW.sub s0 59) = true -> TAGL i E1 -> TAGL j (CC.env_over GT.NF s0 E').
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_288 ())).
Qed.
Lemma TGT_BUFL : forall i c j s0 E1 E' (M1 M2 : mem) o, nth_error G.CPS i = Some c -> (i < 79)%nat -> env_agree (CC.cp_nx c) E1 E' -> (1 <= j <= 27)%nat ->
  PSW.buf_ok i (PSW.sub s0 53) (PSW.sub s0 54) = true -> PSW.bufkind (PSW.KD i) = true -> BUFL i E1 M1 o -> L5.bytes_at (hl_segs L) M2 (bptrI i E1) (BUFB o) ->
  BUFL j (CC.env_over GT.NF s0 E') M2 o.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_289 ())).
Qed.
Lemma uv_JM1 : forall E', 1 <= CL5A.uv E' (EVar 51) -> CL5A.uv E' PSW.JM1 = CL5A.uv E' (EVar 51) - 1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_290 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_ATC : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' sst,
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KAtc sst -> PSW.KD j <> PSW.KRetx -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_291 ())).
Qed.
(* [comment removed for export] *)
Lemma sboform_val : forall E' cc, bv_unsigned (ev E' 32) = wlen -> 0 <= cc <= 1 -> 0 <= wlen - CL5A.uv E' (EVar 51) + cc <= wlen ->
  CL5A.uv E' (PSW.sboform cc) = wlen - CL5A.uv E' (EVar 51) + cc.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_292 ())).
Qed.
(* [comment removed for export] *)
Lemma KEEPC : forall i c E1 E' s0 (var : nat) (getx : nat -> option expr) (getv : PMR.ctrl -> Z) (rng : Z -> Prop) c0 c1 sstj,
  nth_error G.CPS i = Some c -> env_agree (CC.cp_nx c) E1 E' -> (forall ex, getx i = Some ex -> APC.expr_vars_lt (CC.cp_nx (PSW.cutn i)) ex = true) ->
  PSW.keep_ok (getx i) var (PSW.sub s0 var) sstj = true -> (PSW.needs var sstj = true <-> rng sstj) ->
  (rng (PMR.c_sst c0) -> forall ex, getx i = Some ex -> CL5A.uv E1 ex mod 2 ^ 32 = getv c0 mod 2 ^ 32) ->
  getv c1 = getv c0 -> (rng sstj -> rng (PMR.c_sst c0)) ->
  rng sstj -> CL5A.uv E' (PSW.sub s0 var) mod 2 ^ 32 = getv c1 mod 2 ^ 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_293 ())).
Qed.
Lemma NEEDS57 : forall q, PSW.needs 57 q = true <-> 3 <= q <= 11.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_294 ())).
Qed.
Lemma NEEDS58 : forall q, PSW.needs 58 q = true <-> 9 <= q <= 11.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_295 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_STEP : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m' sst cc (istext : bool),
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> (PSW.KD i = PSW.KStep sst cc /\ istext = false) \/ (PSW.KD i = PSW.KText /\ sst = 0 /\ cc = 0 /\ istext = true) -> PSW.KD j <> PSW.KRetx ->
  SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_296 ())).
Qed.

(* [comment removed for export] *)
Lemma SG_ESVX : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> PSW.KD i = PSW.KEsv -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_297 ())).
Qed.
(* [comment removed for export] *)
Lemma S_GOTO : forall i c k ps0 j s E1 R1 E' R' A1 M1 m1 M' m',
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M0c model A (LBV g1) FF LK sp G.HDECL WW G.BLS PSA.FFS (Cred g1) 10 i E1 A1 M1 m1 ->
  env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  XIW g1 i E1 A1 M1 m1 -> SIM g1 j (CC.env_over GT.NF s E') M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_298 ())).
Qed.

Lemma SIM0 : SIM eg 0 E0 M.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_299 ())).
Qed.
Lemma XI0 : XI eg 0 E0 A M model.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_300 ())).
Qed.

End AmbV.

Lemma main : srealizes (hl_segs L) SCFG (@PMSA.cfg L fx R PSA0.PC M model) K.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 (ParseStringXBW_blobs2.kr_b_301 ())).
Qed.

End PsMain.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem parse_string_okw {SCFG_P : ScfgP} (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (IL0 : icpt_layout) :
  PmHeapIfaceA.asan_iface_ok L ar C SCFG HI -> L5A.as0_layout L C -> rt_img_shadow L IL0 HI ->
  Forall (fun r : Z * Z => SLOT2 + 8 <= fst r \/ snd r <= SLOT2) (icl_poison IL0) ->
  (forall a, PMLA.in_footx PMLA.C_xboth a -> ~ hl_rt_static L a) ->
  hl_stack_malloc L 1 = PC_SM ->
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx') ->
  PSWS.atc_specXAW L ar HI PMLA.C_xboth PC_ATC -> PSWS.convert_specXAW L ar HI PMLA.C_xboth PC_CONVERT -> PMSA.str_push_back_specA L ar HI PC_PUSHB ->
  PMSA.str_append_specA L ar HI PC_APPEND -> PMSA.errh_specA L ar HI PC_ERRH -> PMSA.set_ec_specA L ar HI PMLA.C_xboth PC_SETEC ->
  forall (enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop) (benc : PMES.eghost -> Z) (eroomA : PMES.eghost -> PMES.eev -> Prop) (CLA : Z),
  PMXA.enc_agreeP enc_invA -> PMXA.bencP benc ->
  PMXAW.end_string_value_specXAW L ar HI PMLA.C_xboth enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PC_ESV ->
  PMXAW.parse_string_specXAW L ar HI PMLA.C_xboth enc_invA XKA.VIS XKA.VISD benc (PMRXA.the_rmA L) CLA PC.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 6 (ParseStringXBW_blobs2.kr_b_302 ())).
Qed.
Print Assumptions parse_string_okw.

