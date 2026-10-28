(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncBridges_u5 EncBridges2_u5 EncHtrans_u5 EncStrans_u5 EncPure_u5 EncAppendK_u5 EncKit2_u5 EncTail_u5 EncVisitNullB_u5 EncVisitNullHU EncVisitNullNU EncVisitU64B_u5 EncBridgesU EncBridges2U EncHtransU EncStransU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_visit_uint64_nested_xsrc_T_u5 Cut_visit_uint64_nested_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require L5FastLia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Stdlib; @Lists; @List; @Forall_forall]; [@Corelib; @Init; @Datatypes; @list]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @env]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Datatypes; @bool]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmSmall; @SmallPure; @SP; @F_sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @F0N]; [@Corelib; @Init; @Datatypes; @true]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymRun3; @env_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @GT; @NF]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Lists; @ListDef; @Forall]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Datatypes; @prod]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@Corelib; @Init; @Logic; @or]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @estart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @elenZ]; [@Corelib; @Init; @Datatypes; @pair]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmSmall; @SmallPure; @SP; @F_sub_in]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Numbers; @BinNums; @xH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @obj_on_stack]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ENC_SIZE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @apart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_sptop]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Corelib; @Init; @Logic; @or_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EVar]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @ENDE]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibSym; @u64_of_Z]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ev]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @edenot]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_base]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_off]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @estart_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @expr_vars_lt]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @estart_lin]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @uE]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @cons]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @tden]; [@Corelib; @Init; @Datatypes; @snd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @lden]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Logic; @False_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @unsigned_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @outside]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Init; @Datatypes; @option]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @eghost]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ectx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @estate]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_es]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @depth]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_sb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep_blocks]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_rep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @block_range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_scap]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @u64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @enc_inv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @EG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ECtx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ec_arr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ec_nla]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_len]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @Nested; @Stretch; @out_F0]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @agree_on]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @enc_obj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @stack_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @sink_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @len]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep_chars]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @MAX_DEPTH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_STACK]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Datatypes; @length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ctx_at]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Lists; @ListDef; @nth]; [@Corelib; @Init; @Nat; @sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ctx0]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @u32]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @b2z]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @u8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ec_count]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit2_u5; @EK2; @enc_inv_head]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_COLUMN]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_COLON]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @VT_VISITOR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_SINK]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_OPT_VPTR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @VT_ENC_OPTIONS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_FLAGS]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_BIGNUM_FMT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_SPLITS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_INDENT_SIZE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_LINE_LIMIT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_NL_CHARS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_COMMON_VPTR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @VT_ENC_COMMON]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_ENABLE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_MAX_DEPTH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_INDENT_CHAR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_FP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_INDENT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_DEPTH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @sv_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_COLON]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_COMMA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_COMMA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_OBRACE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_OBRACE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_CBRACE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_CBRACE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_OBRACKET]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_OBRACKET]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @O_CBRACKET]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @TXT_CBRACKET]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_lo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_hi]; [@Corelib; @Init; @Logic; @conj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @u32_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @u8_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @LIT_LO]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @LIT_HI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hi_heap]; [@Corelib; @Init; @Datatypes; @app]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @g_lbv]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vmmaps]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @model_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @fp_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @entry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @Nested; @VSCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ev_guard]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @EvU64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @img_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @lits_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ecredit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @objs_enc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @estep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @pay_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @ev_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @W_enc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @regs_preserved]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @hpres]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @model_but_vm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@OssFuzzTheorems; @jsoncons; @fuzz_json_encoder; @images; @Ubsan; @M; @loaded_segments]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @SCFG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @cfg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @PC_VISIT_UINT64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Init; @Logic; @I]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @ra_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @TP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @stk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_segs]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_segs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_img_lo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_img_hi]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_errno]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_errno]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_kpm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_k_per_malloc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit2_u5; @EK2; @depth_cons]; [@Corelib; @Init; @Logic; @ex_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @pow2_10]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hio_wf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@stdpp; @base; @NoDup]; [@Corelib; @Lists; @ListDef; @map]; [@Stdlib; @Lists; @List; @in_or_app]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @or_introl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @hi_heap_perm]; [@Stdlib; @Sorting; @Permutation; @Permutation]; [@Stdlib; @Sorting; @Permutation; @Permutation_sym]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Program; @Basics; @flip]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @flip_Reflexive]; [@Corelib; @Classes; @RelationClasses; @impl_Reflexive]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Stdlib; @Lists; @List; @app_nil_r]; [@Stdlib; @Sorting; @Permutation; @Permutation_middle]; [@Stdlib; @Lists; @List; @app_assoc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncAppendK_u5; @EAK; @bytes_of_defined]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @bytes_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u8_at]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncAppendK_u5; @EAK; @u64_of_defined]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@Corelib; @Init; @Datatypes; @false]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @Env]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @reg_ev]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @ev_reg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ridx]; [@Corelib; @Classes; @Morphisms; @trans_sym_co_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_scr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @HDECL]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_tp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_tp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @in_rng]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @wclient]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_static]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_errno]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_static]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_ro_img]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_crs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @in_reg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @sclient]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_wrs]; [@Corelib; @Init; @Logic; @ex_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_img]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @S2E]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @uv]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @pre_scalar]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @FI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @PA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncBridges_u5; @EB; @CredV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncBridges_u5; @EB; @gB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cutpoint]; [@Stdlib; @Lists; @List; @nth_error]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @CPS]; [@Corelib; @Init; @Datatypes; @Some]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_trans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @NF_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @eb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @den]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @BL1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @mem]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @blocks]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @BLS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @heap_ambV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @model_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @cur]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @LBr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @kept]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @client0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_eqb_eq]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @VmMaps]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @IMG_RO_HI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @kept_static]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @outside]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @post_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @leaf_facts]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @know_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @kentry_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @tag]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @is_leaf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @TAGS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @At]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @has]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all_sound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GN; @CPS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GN; @TAGS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @leaf_chkn]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @leaf_okn]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Corelib; @Init; @Datatypes; @andb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_F]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GNT; @NF]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GN; @BLS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@Corelib; @Init; @Datatypes; @orb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @PC_BEGIN_SCALAR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @RETPC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @subst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @call_j]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GN; @RETS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncHtrans_u5; @EHT; @hcall_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @GN; @HDECL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @BSSCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @NEWS_BS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @PCF]; [@Corelib; @Init; @Datatypes; @negb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncStrans_u5; @EST; @strans_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @FISCR]; [@Stdlib; @Bool; @Bool; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reglist]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @SKE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @exit_base_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is]; [@Stdlib; @Lists; @List; @hd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_PSS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @kword64_elim]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @has_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @Nested; @lits_stretch]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_frame]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @comma]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @nl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @set_nla]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @Nested; @inv_stretch]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_grows]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @img_ro_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @Nested; @out_F0]; [@Stdlib; @micromega; @ZifyClasses; @impl_morph]; [@Stdlib; @micromega; @ZifyClasses; @not_morph]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @lits_ok_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @W_h]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @hpres_kept]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @cp0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @cert_sound3V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @LYI_]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @LYE_]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @plan_sound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @plans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @tags_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @heap_ok3n]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TGoto]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_over]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TOther]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @leaf_okV]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb_le]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ret_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitNullB_u5; @EVNB; @isSome]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @cinfo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncHtrans_u5; @EHT; @hcall_leaf_okV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @G; @RETS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @stack_blocks]; [@Stdlib; @Sorting; @Permutation; @Permutation_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @common_facts_x]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_csp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_know]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @heap_amb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @regs_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_regs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sr_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @kn_vars_lt]; [@Corelib; @Init; @Nat; @add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @NCS]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @meas]; [@Corelib; @Numbers; @BinNums; @positive]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @NEWLINE_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64NU; @EVU64NU; @custom_chk_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @custom_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KUnk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @kword32_intro]; [@Corelib; @Init; @Logic; @eq_sym]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @kword8_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kword64_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kwr_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kunk_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3XV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @IH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @defined_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @enc_inv_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @expr_eqb_eq]; [@Stdlib; @Bool; @Bool; @eqb_prop]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncStrans_u5; @EST; @strans_leaf_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncStrans_u5; @EST; @PAYMAX]; [@Stdlib; @Lists; @List; @incl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @scredit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncStrans_u5; @EST; @kxs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sr_get]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @u_lin]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @FROMINT_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncStrans_u5; @EST; @uv]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Corelib; @Init; @Logic; @proj2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_neq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_keeps]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @CSAVED]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @eaddz]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @uv_eaddz]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @bump]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV_def0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @exit_ret]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncVisitU64B_u5; @EVU64B; @ret_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @hpres_rebase]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is_sound]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @kv_s2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @kv_st]; [@Stdlib; @Sorting; @Permutation; @Permutation_app_comm]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Init; @Logic; @proj1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmGrow; @GrowKit_u5; @GK; @u8_at_mod]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_regs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @regs_ok_id]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KAlign]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KDisj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KImg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @krange_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @elen_lin]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined_sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kalign_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_1_l]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kdisj_intro]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @CP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @PS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @region]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3V_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @model_but_vm_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @cps_heap]].

#[local] Ltac lia ::= L5FastLia.plia.   (* [comment removed for export] *)
Open Scope Z_scope.

Module EVU64NU.
Import PMES.
Import EVNB.
Import EVU64B.
Module G := GN.
Module GT := GNT.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

Definition pow2_10 := EVNHU.pow2_10.  Definition custom_chk_nx := EVNHU.custom_chk_nx.
(* [comment removed for export] *)
Ltac l_disj := eapply CL5.kdisj_intro; [ev_start | ev_len | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | ev_len | unfold hl_ceil in *; lia].

Section Nested.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis BSCALAR_OK : begin_scalar_specU L HI.
Hypothesis FROM_OK : from_integer_u64_x_specU L HI.

(* [comment removed for export] *)
Section Stretch.
Variables (E0 : env) (sp V S2 b dr : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis U10 : bv_unsigned (ev E0 10) = V.
Hypothesis U33 : bv_unsigned (ev E0 33) = dr + 1.
Hypothesis U34 : bv_unsigned (ev E0 34) = b.
Hypothesis SPR : hl_ceil L + 10624 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OBJS : objs_enc L sp V S2.
Hypothesis BR : 4096 <= b /\ 0 <= dr <= 1023 /\ b + 32 * (dr + 1) <= hl_ceil L.
Hypothesis BIMG : b + 32 * (dr + 1) <= 0x10000 \/ 0xfe000 <= b.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F F0N = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 10624 <= a < sp) -> ~ (V + 296 <= a < V + 304) -> ~ (b + 32 * dr + 24 <= a < b + 32 * dr + 32) -> SGP.outside E' F (Z_to_bv 64 a).
Proof using BIMG BR OBJS SPR U10 U2 U33 U34. eapply EVNNU.out_F0; eassumption.
Qed.

(* [comment removed for export] *)
Lemma inv_stretch : forall (F : list SGP.region) E' (M M' : mem) g c r cnt', SP.F_sub F F0N = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' ->
  g_es g = c :: r -> depth r = dr -> g_sb g = b ->
  (forall b0, In b0 (PML.srep_blocks (g_rep g)) -> block_range L (fst b0) (snd b0) /\ (fst b0 + snd b0 <= b \/ b + 32 * (dr + 1) <= fst b0)) ->
  b + g_scap g <= 2 ^ 64 ->
  PML.u64 M' (b + 32 * dr + 24) cnt' -> 0 <= cnt' < 2 ^ 64 ->
  enc_inv M V S2 g -> enc_inv M' V S2 (EG (ECtx (ec_arr c) cnt' (ec_nla c) :: r) (g_len g) (g_rep g) (g_sb g) (g_scap g)).
Proof using BIMG BR OBJS SPR U10 U2 U33 U34. eapply EVNNU.inv_stretch; eassumption.
Qed.
(* [comment removed for export] *)
Lemma lits_stretch : forall (F : list SGP.region) E' (M M' : mem), SP.F_sub F F0N = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> forall a, PML.LIT_LO <= a < PML.LIT_HI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof using BIMG BR OBJS SPR U10 U2 U33 U34. eapply EVNNU.lits_stretch; eassumption.
Qed.
End Stretch.

Definition VSCR := EVNHU.VSCR.

Theorem visit_uint64_nested_ok : forall (v : Z) (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost) (c0 : ectx) (r0 : estate),
  g_es g = c0 :: r0 ->
  PML.cps_heap L HI PC_VISIT_UINT64 r sp VSCR (LBo ++ g_lbv g) cr
    (fun R M => PML.entry L R M sp r VSCR /\ PML.a0 R V /\ (PML.a1 R v /\ 0 <= v < 2 ^ 64) /\ enc_inv M V S2 g /\ ev_guard (g_es g) EvU64 /\ eroomU g EvU64 /\ PML.img_ro M /\ PML.lits_ok M /\
                ecreditU L cr g kx bx /\ objs_enc L sp V S2)
    (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (pay : Z),
        PML.a0 R' 1 /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) EvU64 /\ pay_ok EvU64 pay /\ g_len g' = g_len g + ev_ind (g_es g) EvU64 + pay /\
        PML.lits_ok M' /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_enc V S2 /\ ecreditU L cr' g' kx bx).
Proof using BSCALAR_OK FPM FROM_OK HIok LAY.
  intros v LBo cr sp r V S2 kx bx g c0 r0 Hes. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & [Ha1 VR] & Hinv & _ & Hroom & Himg & Hlits & Hcred & Hobjs) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  assert (VS : VSCR = EVNB.SCRW) by reflexivity. rewrite VS in S2', S5. unfold EVNB.SCRW in S2'.
  pose proof Hobjs as ((OV1 & OV2 & OV3) & (OS1 & OS2 & OS3) & OAP). unfold ENC_SIZE, PML.apart in OV2, OAP.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER. pose proof (PmLayout.ly_kpm L LAY) as KPM.
  destruct g as [es len0 rep b cb]. cbn [g_es g_len g_rep g_sb g_scap] in *. subst es. destruct c0 as [arr cnt nla0].
  assert (RM : len0 + fst (pre_scalar (ECtx arr cnt nla0 :: r0)) + 20 <= CLU) by (unfold eroomU, kmax in Hroom; cbn [ev_ind pay_hi quotes g_len g_es] in Hroom; lia).
  set (dr := depth r0).
  assert (DR0 : 0 <= dr) by (unfold dr, depth; lia).
  assert (DES : depth (ECtx arr cnt nla0 :: r0) = dr + 1) by (unfold dr, depth; cbn [length]; lia).
  pose proof Hinv as (I1 & I2 & I3 & I4 & I5). cbn [g_es g_len g_rep g_sb g_scap] in I1, I2, I3, I4, I5. rewrite DES in I1, I5. unfold MAX_DEPTH in I5.
  pose proof I2 as TT. unfold stack_at in TT. destruct TT as (T1 & T2 & T3 & T4 & T5 & T6). rewrite DES in T2, T4.
  assert (CB : 32 <= cb <= 32768).
  { destruct T5 as [(E1 & E2)|(k0 & Hk0 & Ecb)]; [lia|]. pose proof (pow2_10 k0 Hk0). lia. }
  assert (LBV : g_lbv (EG (ECtx arr cnt nla0 :: r0) len0 rep b cb) = PML.srep_blocks rep ++ [(b, cb)]).
  { unfold g_lbv, stack_blocks. cbn [g_rep g_sb g_scap]. destruct (Z.eqb_spec cb 0); [lia | reflexivity]. }
  rewrite LBV in HH.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0).
  assert (INB : In (b, cb) (LBo ++ PML.srep_blocks rep ++ [(b, cb)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  destruct (Hwf _ INB) as ((B0 & B1 & B2 & B3 & B4) & _ & _). cbn [fst snd] in B0, B1, B2, B3, B4.
  assert (HHp : hi_heap HI ((b, cb) :: LBo ++ PML.srep_blocks rep) cr M (m_vmmaps model)).
  { apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH). rewrite app_assoc. apply Permutation_sym, Permutation_cons_append. }
  assert (HC : ctx_at M (b + 32 * dr) (ECtx arr cnt nla0)).
  { pose proof (T6 (length r0) ltac:(cbn [length]; lia)) as X.
    replace (length (ECtx arr cnt nla0 :: r0) - 1 - length r0)%nat with 0%nat in X by (cbn [length]; lia). exact X. }
  pose proof HC as (HQ1 & HQ2 & HQ3 & HQ4 & HQ5 & HQ6). cbn [ec_arr ec_count ec_nla] in HQ1, HQ2, HQ3, HQ4, HQ5, HQ6.
  assert (BRR : 4096 <= b /\ 0 <= dr <= 1023 /\ b + 32 * (dr + 1) <= hl_ceil L) by lia.
  assert (BIMG0 : b + 32 * (dr + 1) <= hl_img_lo L \/ hl_img_hi L <= b) by lia.
  pose proof BIMG0 as BIMG. rewrite ILO, IHI in BIMG.
  destruct (EAK.bytes_of_defined M 1 (b + 32 * dr + 5) ltac:(lia) ltac:(unfold hl_ceil in B4; lia)) as (ibs & Hibl & Hib).
  { intros j Hj. replace (b + 32 * dr + 5 + j) with (b + 32 * dr + (5 + j)) by lia. apply HQ6. lia. }
  destruct ibs as [|ib [|ib2 ibs]]; cbn [length] in Hibl; try discriminate. clear Hibl.
  pose proof (Hib 0%nat ltac:(cbn [length]; lia)) as Hib0. cbn [nth] in Hib0. change (Z.of_nat 0) with 0 in Hib0. rewrite Z.add_0_r in Hib0.
  assert (IB : 0 <= ib mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hib' : PML.u8 M (b + 32 * dr + 5) (ib mod 256)) by exact (proj1 (GK.u8_at_mod M (b + 32 * dr + 5) ib) Hib0).
  assert (DCOL : L5.defined M (V + 296) 8).
  { destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  destruct (EAK.u64_of_defined M (V + 296) DCOL) as (col & Hcol0 & Hcol).
  set (ty := PML.b2z arr). set (nlz := PML.b2z nla0).
  assert (TY : 0 <= ty <= 1) by (unfold ty, PML.b2z; destruct arr; lia).
  assert (NLZ : 0 <= nlz <= 1) by (unfold nlz, PML.b2z; destruct nla0; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; dr + 1; b; cb; cnt; col; ty; ib mod 256; nlz] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 V) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 v) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 (dr + 1)) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 b) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 cb) by reflexivity.
  assert (V36 : ev E0 36 = Z_to_bv 64 cnt) by reflexivity.
  assert (V37 : ev E0 37 = Z_to_bv 64 col) by reflexivity.
  assert (V38 : ev E0 38 = Z_to_bv 64 ty) by reflexivity.
  assert (V39 : ev E0 39 = Z_to_bv 64 (ib mod 256)) by reflexivity.
  assert (V40 : ev E0 40 = Z_to_bv 64 nlz) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = V) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = v) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = dr + 1) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = b) by (rewrite V34; apply u64_of_Z; unfold hl_ceil in B4; lia).
  assert (U35 : bv_unsigned (ev E0 35) = cb) by (rewrite V35; apply u64_of_Z; lia).
  assert (U36 : bv_unsigned (ev E0 36) = cnt) by (rewrite V36; apply u64_of_Z; lia).
  assert (U37 : bv_unsigned (ev E0 37) = col) by (rewrite V37; apply u64_of_Z; lia).
  assert (U38 : bv_unsigned (ev E0 38) = ty) by (rewrite V38; apply u64_of_Z; lia).
  assert (U39 : bv_unsigned (ev E0 39) = ib mod 256) by (rewrite V39; apply u64_of_Z; lia).
  assert (U40 : bv_unsigned (ev E0 40) = nlz) by (rewrite V40; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = EVNB.SCRW) by reflexivity.
  assert (SC2 : hl_ceil L + CH.hd_scr G.HDECL <= sp) by (rewrite SCRV; unfold hl_ceil, EVNB.SCRW; lia).
  assert (SC3 : hl_ceil L + EVNB.SCRW <= sp) by (unfold hl_ceil, EVNB.SCRW; lia).
  pose proof (conj S1 (conj SC2 (conj S3 S4))) as STKF.
  pose proof (conj SC3 (conj S3 S4)) as SPR.
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; unfold EVNB.SCRW; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := W_enc V S2).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[<-|[<-|[<-|[]]]]] Hin; unfold L5.in_rng, O_STACK, O_DEPTH, PML.LIT_LO, PML.LIT_HI in Hin; cbn [fst snd] in Hin; (split; [lia|]); [left; lia | left; lia | left; lia | right].
    unfold in_errno. rewrite ILO, IHI, LER. split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
    split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite ILO, IHI; lia)) as [Y|[Y|Y]]; lia | lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
      rewrite U10 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 40). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
    - rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [right; right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (W_S2 : In (S2, 24) W) by (right; right; left; reflexivity).
  assert (W_COL : forall a, V + O_COLUMN <= a < V + O_COLUMN + 8 -> exists w, In w W /\ L5.in_rng w a).
  { intros a Ha. exists (V + O_STACK, 40). split; [left; reflexivity | unfold L5.in_rng, O_STACK, O_COLUMN in *; cbn [fst snd]; lia]. }
  assert (OADDR : estart E0 (SA EVNB.S2E 0) = S2) by (unfold estart, EVNB.S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  assert (S2ADDR : PB.uv E0 EVNB.S2E = S2) by (unfold PB.uv, EVNB.S2E; cbn [edenot]; exact U32).
  set (ESI := fun i : nat => if Nat.eqb i 0 then ECtx arr cnt nla0 :: r0 else snd (pre_scalar (ECtx arr cnt nla0 :: r0))).
  set (OFF := fun i : nat => if Nat.eqb i 0 then 0 else fst (pre_scalar (ECtx arr cnt nla0 :: r0))).
  set (PAYOK := fun (i : nat) (pay : Z) => if EVU64B.FI i then 1 <= pay <= 20 else pay = 0).
  set (XIv := fun (g1 : eghost) (i : nat) (E : env) (M1 : mem) =>
                enc_inv M1 V S2 g1 /\ g_es g1 = ESI i /\ g_sb g1 = b /\ g_scap g1 = cb /\ (exists pay, PAYOK i pay /\ g_len g1 = len0 + OFF i + pay) /\
                (i <> 0%nat -> arr = EVU64B.PA i) /\ PML.lits_ok M1 /\ True).
  assert (OFFB : forall i, 0 <= OFF i <= fst (pre_scalar (ECtx arr cnt nla0 :: r0))).
  { assert (PS0 : 0 <= fst (pre_scalar (ECtx arr cnt nla0 :: r0))).
    { cbn [pre_scalar ec_arr]. destruct arr; cbn [fst]; [|lia]. unfold comma, nl. rewrite DES. cbn [ec_count]. destruct (0 <? cnt); lia. }
    intros i. unfold OFF; cbv beta. destruct (Nat.eqb i 0); lia. }
  set (CredV := EBU.CredV L kx bx).
  set (gB := EBU.gB []).
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (DEN : forall E1, env_agree GT.NF E0 E1 -> CH2.den E1 EVNB.BL1 = [(b, cb)]).
  { intros E1 Hag. unfold CH2.den, EVNB.BL1. cbn [map fst snd].
    fold (PB.uv E1 (EVar 34)). fold (PB.uv E1 (EVar 35)).
    rewrite (PB.uv_agree GT.NF E0 E1 (EVar 34) Hag eq_refl), (PB.uv_agree GT.NF E0 E1 (EVar 35) Hag eq_refl).
    unfold PB.uv. cbn [edenot]. rewrite U34, U35. reflexivity. }
  assert (HEAP : forall g1 M0c i E (M1 : mem) m1, CH2.blocks_eqb (nth i G.BLS []) EVNB.BL1 = true ->
                   CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 ->
                   env_agree GT.NF E0 E /\ exists cr1, hi_heap HI ((b, cb) :: LBo ++ PML.srep_blocks (g_rep g1)) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 HB (_ & _ & HagE & (cr1 & HH1 & HCr) & _). split; [exact HagE|]. exists cr1. split; [|exact HCr].
    apply CH2.blocks_eqb_eq in HB. unfold CH2.cur, CH2V.LBr in HH1. rewrite HB, (DEN E HagE) in HH1. unfold gB, EBU.gB in HH1. rewrite app_nil_r in HH1. exact HH1. }
  assert (BLKS : forall g1 cr1 (M1 : mem) VM, hi_heap HI ((b, cb) :: LBo ++ PML.srep_blocks (g_rep g1)) cr1 M1 VM ->
                   forall b0, In b0 (PML.srep_blocks (g_rep g1)) -> block_range L (fst b0) (snd b0) /\ (fst b0 + snd b0 <= b \/ b + 32 * (dr + 1) <= fst b0)).
  { intros g1 cr1 M1 VM HH1 b0 Hb0. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf1 & _).
    assert (In0 : In b0 ((b, cb) :: LBo ++ PML.srep_blocks (g_rep g1))) by (right; apply in_or_app; right; exact Hb0).
    destruct (Hwf1 _ In0) as (BR0 & _). split; [exact BR0|].
    destruct (Hwf1 (b, cb) (or_introl eq_refl)) as (_ & _ & AP). cbn [fst snd lb_remove] in AP. rewrite Z.eqb_refl in AP.
    destruct (AP b0 ltac:(apply in_or_app; right; exact Hb0)) as [A1|A1]; lia. }
  assert (IMGC : forall g1 M0c i E (M1 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
                   CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> PML.img_ro M1).
  { intros g1 M0c i E M1 m1 (O1 & _) (_ & _ & _ & _ & Hfr & _) a Ha.
    assert (KA : forall LBx, L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
    { intros LBx. unfold PML.IMG_RO_HI in Ha.
      apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
      intros w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng, O_STACK, O_DEPTH, PML.LIT_LO, PML.LIT_HI; cbn [fst snd]; unfold hl_ceil in *; lia. }
    rewrite (Hfr a (KA _)). rewrite (O1 a (KA _)). exact (Himg a Ha). }
  assert (WEND : edenot E0 EVNB.ENDE = Z_to_bv 64 (b + 32 * (dr + 1))).
  { assert (UU : bv_unsigned (edenot E0 EVNB.ENDE) = b + 32 * (dr + 1)).
    { apply CL5.u_lin; [|unfold hl_ceil in *; lia]. unfold EVNB.ENDE. lin_eval. rewrite U33, U34. lia. }
    rewrite <- UU. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (ENDV : forall E' o, env_agree GT.NF E0 E' -> estart E' (SA EVNB.ENDE o) = b + 32 * (dr + 1) + o).
  { intros E' o Hag. rewrite (PB.estart_agree GT.NF E0 E' EVNB.ENDE o Hag eq_refl). unfold estart. cbn [a_base a_off].
    rewrite WEND. rewrite u64_of_Z by (unfold hl_ceil in *; lia). lia. }
  assert (HK' : forall c ps E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps)).
  { intros c ps E' R' M1 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
  assert (HESI : forall i, ECtx arr cnt (ec_nla (hd ctx0 (ESI i))) :: r0 = ESI i).
  { intros i. unfold ESI; cbv beta. destruct (Nat.eqb i 0); [reflexivity|]. cbn [pre_scalar ec_arr snd hd ec_nla set_nla]. destruct arr; reflexivity. }
  assert (GETA : forall g1 i, g_es g1 = ESI i -> g_sb g1 = b -> g_scap g1 = cb -> EG (ECtx arr cnt (ec_nla (hd ctx0 (ESI i))) :: r0) (g_len g1) (g_rep g1) b cb = g1).
  { intros g1 i H1 H2 H3. rewrite HESI. destruct g1 as [es1 l1 rp1 sb1 sc1]. cbn [g_es g_sb g_scap g_len g_rep] in *. rewrite H1, H2, H3. reflexivity. }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem) cnte cnt',
     CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 -> CH2V.okV L M LBo sp G.HDECL W M0c ->
     CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS eghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
     env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
     PB.has (SR.ps_cells ps) (KWord (SA EVNB.ENDE (-8)) 8 cnte) = true -> PB.uv E' cnte = cnt' ->
     enc_inv M' V S2 (EG (ECtx arr cnt' (ec_nla (hd ctx0 (ESI i))) :: r0) (g_len g1) (g_rep g1) b cb) /\ env_agree GT.NF E0 E' /\
     PML.img_ro M' /\ PML.lits_ok M' /\ True).
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' cnte cnt' IL HAt OKV HA HX Hag HLF HCN HCV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okn _ _ _ _ _ IL) as X. unfold leaf_chkn in X.
    apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X XB].
    apply andb_prop in X as [XF _].
    destruct (HEAP g1 M0c i E M1 m1 XB HA) as (HagE & cr1 & HH1 & _).
    destruct IL as (tags & Hc & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    destruct HX as (HX1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
    pose proof (HK' c ps E' R' M1 M' HLF) as HK.
    pose proof (PB.has_ok E' M' _ _ HK HCN) as Y.
    assert (Hcnt : L5.u64_at RSEGS M' (b + 32 * dr + 24) cnt').
    { rewrite <- HCV. apply (CL5.kword64_elim RSEGS E' M' _ _ (b + 32 * dr + 24) (PB.uv E' cnte) Y); [rewrite (ENDV E' (-8) HagE'); lia | reflexivity]. }
    assert (CR : 0 <= cnt' < 2 ^ 64).
    { rewrite <- HCV. unfold PB.uv. pose proof (bv_unsigned_in_range _ (edenot E' cnte)) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. }
    assert (LAG : forall a, PML.LIT_LO <= a < PML.LIT_HI -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { exact (lits_stretch E0 sp V S2 b dr U2 U10 U33 U34 SPR Hobjs BRR BIMG (CC.cp_F c) E' M1 M' XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF)). }
    split; [|split; [exact HagE'|split; [|split; [exact (PML.lits_ok_agree M1 M' LAG X7) | exact I]]]].
    - assert (HG : exists ch, ESI i = ch :: r0 /\ ec_arr ch = arr).
      { unfold ESI; cbv beta. destruct (Nat.eqb i 0); [exists (ECtx arr cnt nla0); split; reflexivity|]. cbn [pre_scalar ec_arr snd]. destruct arr; cbn [snd]; eexists; split; reflexivity. }
      destruct HG as (ch & Hch & Harr). rewrite Hch. cbn [hd]. rewrite <- Harr. rewrite <- X3, <- X4.
      apply (inv_stretch E0 sp V S2 b dr U2 U10 U33 U34 SPR Hobjs BRR BIMG (CC.cp_F c) E' M1 M' g1 ch r0 cnt' XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF));
        [rewrite X2; exact Hch | reflexivity | exact X3 | exact (BLKS g1 cr1 M1 _ HH1) | rewrite X4; unfold hl_ceil in *; lia | exact Hcnt | exact CR | exact HX1].
    - apply (EK.img_ro_agree M1 M'); [|exact (IMGC g1 M0c i E M1 m1 OKV HA)]. intros a Ha. unfold PML.IMG_RO_HI in Ha.
      apply (CC.lf_frame _ _ _ _ _ _ _ HLF). apply (out_F0 E0 sp V S2 b dr U2 U10 U33 U34 SPR Hobjs BRR BIMG (CC.cp_F c) E' a XF HagE'); unfold hl_ceil in *; lia. }
  assert (HPLIT : forall LBk spc scr (M1 M2 : mem), L5C.hpres L LBk spc scr (W_h V S2) M1 M2 -> forall a, PML.LIT_LO <= a < PML.LIT_HI -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros LBk spc scr M1 M2 HP a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). unfold PML.LIT_LO, PML.LIT_HI in Ha.
    apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X0; pose proof (PmLayout.ly_static L LAY a X0); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[<-|[]]]; unfold L5.in_rng, O_COLUMN; cbn [fst snd]; unfold hl_ceil in *; lia. }
  assert (HPLIT2 : forall LBk spc scr (M1 M2 : mem), L5C.hpres L LBk spc scr [(S2, 24)] M1 M2 -> forall a, PML.LIT_LO <= a < PML.LIT_HI -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros LBk spc scr M1 M2 HP a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). unfold PML.LIT_LO, PML.LIT_HI in Ha.
    apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X0; pose proof (PmLayout.ly_static L LAY a X0); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; unfold hl_ceil in *; lia. }
  assert (HEADC : forall (M2 : mem) g' a1 n1 l1, enc_inv M2 V S2 g' -> g_es g' = ECtx a1 n1 l1 :: r0 -> g_sb g' = b ->
            ctx_at M2 (b + 32 * dr) (ECtx a1 n1 l1)).
  { intros M2 g' a1 n1 l1 (J1 & J2 & _) Jes Jsb. unfold stack_at in J2. rewrite Jes, Jsb in J2. destruct J2 as (_ & _ & _ & _ & _ & J6).
    pose proof (J6 (length r0) ltac:(cbn [length]; lia)) as Y.
    replace (length (ECtx a1 n1 l1 :: r0) - 1 - length r0)%nat with 0%nat in Y by (cbn [length]; lia). exact Y. }
  unfold PML.cfg. change PC_VISIT_UINT64 with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3n.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC'. exact HC'.
  - intros g1 M0c OKV i c kk ps j sg IL. exfalso.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okn _ _ _ _ _ IL) as X. unfold leaf_chkn in X. apply andb_prop in X as [_ X]. discriminate X.
  -
    intros i c kk ps pc IL g1 M0c OKV.
    pose proof IL as (tags0 & Hc0 & _).
    pose proof (CH2.leaves_all_sound _ _ _ leaf_okn _ _ _ _ _ IL) as X. unfold leaf_chkn in X.
    apply andb_prop in X as [X Xm]. apply andb_prop in X as [X XCNT]. apply andb_prop in X as [X XTY]. apply andb_prop in X as [X XB]. apply andb_prop in X as [XF XN].
    apply Nat.leb_le in XN. pose proof XB as XB'. apply CH2.blocks_eqb_eq in XB'.
    assert (LEAFV : forall E', env_agree GT.NF E0 E' -> PB.uv E' (EVar 36) = cnt /\ PB.uv E' (EVar 38) = ty /\ PB.uv E' (EVar 40) = nlz /\ PB.uv E' (EVar 10) = V /\ PB.uv E' (EVar 2) = sp).
    { intros E' Hag.
      rewrite (PB.uv_agree GT.NF E0 E' (EVar 36) Hag eq_refl), (PB.uv_agree GT.NF E0 E' (EVar 38) Hag eq_refl), (PB.uv_agree GT.NF E0 E' (EVar 40) Hag eq_refl),
        (PB.uv_agree GT.NF E0 E' (EVar 10) Hag eq_refl), (PB.uv_agree GT.NF E0 E' (EVar 2) Hag eq_refl).
      unfold PB.uv. cbn [edenot]. rewrite U36, U38, U40, U10, U2. repeat split. }
    assert (TYV : forall E' (M' : mem) kv, env_agree GT.NF E0 E' -> know_ok RSEGS E' M' (SR.ps_cells ps) -> PB.has (SR.ps_cells ps) (KRange (EVar 38) kv kv) = true -> ty = kv).
    { intros E' M' kv Hag HK HH0. pose proof (PB.has_ok E' M' _ _ HK HH0) as Y. cbn [kentry_ok edenot] in Y.
      destruct (LEAFV E' Hag) as (_ & Y38 & _). unfold PB.uv in Y38. cbn [edenot] in Y38. lia. }
    assert (ARRTY : forall kv, ty = kv -> arr = (kv =? 1)) by (intros kv <-; unfold ty, PML.b2z; destruct arr; reflexivity).
    destruct (Z.eqb_spec pc PC_BEGIN_SCALAR) as [->|Hne1].
    {
      apply andb_prop in Xm as [Xm X40]. apply andb_prop in Xm as [Xm XCJ]. apply andb_prop in Xm as [Xi Xpc]. apply Nat.eqb_eq in Xi. subst i. apply Z.eqb_eq in Xpc.
      unfold EVNB.call_j in XCJ. destruct (CH2.ret_of G.RETS 0 kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in XCJ as [XCJ Xcond]. apply andb_prop in Xcond as [Xj Xnx]. apply Nat.eqb_eq in Xj. subst j. apply Nat.leb_le in Xnx.
      destruct (EHT.hcall_chk GT.NF G.HDECL EVNB.S2E EVNB.BSSCR EVNB.NEWS_BS c ps cj (nth 0 G.BLS []) (nth 1 G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      assert (XCNT' : PB.has (SR.ps_cells ps) (KWord (SA EVNB.ENDE (-8)) 8 (EVar 36)) = true) by (rewrite Xpc in XCNT; exact XCNT).
      assert (XTY1 : PB.has (SR.ps_cells ps) (KRange (EVar 38) 1 1) = true) by (rewrite Xpc in XTY; exact XTY).
      assert (ESI0 : ESI 0%nat = ECtx arr cnt nla0 :: r0) by reflexivity.
      assert (OFF0 : OFF 0%nat = 0) by reflexivity.
      apply (EHTU.hcall_leaf_okV L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               V S2 Hobjs W_S2 W_COL EVNB.S2E eq_refl S2ADDR U10 PC_BEGIN_SCALAR EVNB.BSSCR EVNB.NEWS_BS 0%nat c kk ps 1%nat cj ci g1 M0c OKV IL Hret Hcj Xpc Hchk).
      - rewrite XB'. reflexivity.
      - intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF.
        destruct (HEAP g1 M0c 0%nat E M1 m1 XB HA) as (HagE & _). pose proof (AGE 0%nat c E E' Hc0 HagE Hag) as HagE'.
        pose proof HX as (_ & _ & Y3 & Y4 & _). rewrite Y3, Y4, XB', (DEN E' HagE'). unfold stack_blocks. destruct (Z.eqb_spec cb 0); [lia|]. cbn [app]. apply Permutation_refl.
      - intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HH1 HC1 HFP Ga0 Hk.
        pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct HA' as (Hmo1 & _).
        destruct (STRETCH g1 M0c 0%nat c kk ps _ E R1 M1 m1 E' R' M' (EVar 36) cnt IL HAt OKV HA HX Hag HLF XCNT' (proj1 (LEAFV E' HagE'))) as (HINV & _ & HIMG & HLITS & _).
        pose proof HX as (_ & Y2 & Y3 & Y4 & (p0 & P0 & Y5) & _). unfold PAYOK in P0. cbn in P0. rewrite (GETA g1 0%nat Y2 Y3 Y4) in HINV.
        rewrite LS in HK.
        pose proof (TYV E' M' 1 HagE' HK XTY1) as TY1. pose proof (ARRTY 1 TY1) as ARR. cbn in ARR.
        apply (BSCALAR_OK LBo cr1 (sp + CH2.ci_csp ci) (CC.cp_pc cj) V S2 kx bx g1 fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        + split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity | exact Hstk']]]]|].
          split; [exact Ga0|]. split; [exact I|]. split; [exact HINV|]. split; [exact I|]. split.
          { rewrite Y5, P0, Y2, ESI0, OFF0. rewrite <- (EK.pre_scalar_arr (ECtx arr cnt nla0) r0 ARR). lia. }
          split; [exact HIMG|]. split; [exact HC1|].
          pose proof Hobjs as ((A1 & A2 & A3) & (B1' & B2' & B3') & C). refine (conj (conj _ (conj A2 A3)) (conj (conj _ (conj B2' B3')) C)); lia.
        + intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (g' & d & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10) HRP HP Hbv2 HH2.
          cbv beta in P2, P5.
          assert (P2' : g_es g' = ECtx arr cnt true :: r0) by (rewrite P2, Y2; reflexivity).
          assert (Pb : g_sb g' = b) by (rewrite P3; exact Y3).
          apply (Hk fx2 R2 M2 model2 LB' cr' LBk Wc g' HFP2 P3 P4 P7 P8 P9 P10 HRP HP Hbv2 HH2).
          * intros X HXn _. rewrite LS.
            set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
            assert (Hcnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 0)%nat).
            { unfold EHT.hcall_chk in Hchk.
              destruct (CH2.blocks_eqb (nth 1 G.BLS []) (nth 0 G.BLS []) && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) (EVar 10))%bool; [|discriminate].
              exact (custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk). }
            assert (HagE2 : env_agree GT.NF E0 E2).
            { eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2) | unfold GT.NF, APC.NCS in *; lia]]. }
            pose proof (HEADC M2 g' arr cnt true P1 P2' Pb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
            destruct (LEAFV E2 HagE2) as (L36 & L38 & _).
            destruct HXn as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
            -- eapply PB.kword32_intro with (A := b + 32 * dr) (z := ty); [rewrite (ENDV E2 (-32) HagE2); lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | apply PB.edenot_of_uv; exact L38 | exact Q1].
            -- eapply PB2.kword8_intro with (A := b + 32 * dr + 4) (z := 0); [rewrite (ENDV E2 (-28) HagE2); lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | reflexivity | lia | exact Q2].
            -- eapply PB2.kword8_intro with (A := b + 32 * dr + 6) (z := 1); [rewrite (ENDV E2 (-26) HagE2); lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | reflexivity | lia | exact Q3].
            -- eapply CL5.kword64_intro with (A := b + 32 * dr + 24) (z := cnt); [rewrite (ENDV E2 (-8) HagE2); lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | apply PB.edenot_of_uv; exact L36 | exact Q4].
            -- eapply CL5.kwr_intro; [apply (ENDV E2 (-8) HagE2) | ev_len | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | eapply (L5.defined_sub _ _ _ _ _ Q6); lia].
            -- eapply CL5.kunk_intro; [apply (ENDV E2 (-32) HagE2) | ev_len | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | unfold hl_ceil in *; lia | eapply (L5.defined_sub _ _ _ _ _ Q6); lia].
          * split; [exact P1|]. split.
            { rewrite P2'. unfold ESI; cbv beta. cbn [Nat.eqb pre_scalar ec_arr snd]. rewrite ARR. reflexivity. }
            split; [rewrite P3; exact Y3|]. split; [rewrite P4; exact Y4|]. split.
            { exists 0. split; [reflexivity|]. rewrite P6, P5, Y5, P0, Y2, ESI0, OFF0. unfold OFF; cbv beta. cbn [Nat.eqb]. rewrite (EK.pre_scalar_arr (ECtx arr cnt nla0) r0 ARR). lia. }
            split; [intros _; rewrite ARR; reflexivity|].
            split; [rewrite P9 in HP; exact (PML.lits_ok_agree M' M2 (HPLIT _ _ _ M' M2 HP) HLITS) | exact I]. }
    destruct (Z.eqb_spec pc PCF) as [->|Hne2].
    {
      apply andb_prop in Xm as [Xm X26]. apply andb_prop in Xm as [Xm Xa1]. apply andb_prop in Xm as [Xm Xa0]. apply andb_prop in Xm as [Xm XCJ]. apply andb_prop in Xm as [Xpc XFI].
      apply Z.eqb_eq in Xpc. apply expr_eqb_eq in Xa0, Xa1. apply negb_true_iff in XFI.
      unfold EVNB.call_j in XCJ. destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in XCJ as [XCJ Xcond].
      apply andb_prop in Xcond as [Xcond XJ0]. apply andb_prop in Xcond as [Xcond Xnx]. apply andb_prop in Xcond as [XPA XFJ].
      apply negb_true_iff in XJ0. apply Nat.eqb_neq in XJ0. apply Nat.leb_le in Xnx. apply Bool.eqb_prop in XPA.
      destruct (EST.strans_chk GT.NF G.HDECL EVNB.S2E 0 FISCR c ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
      assert (XCNT' : PB.has (SR.ps_cells ps) (KWord (SA EVNB.ENDE (-8)) 8 (EVar 36)) = true) by (rewrite Xpc in XCNT; exact XCNT).
      apply (ESTU.strans_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               V S2 Hobjs W_S2 EVNB.S2E 0 eq_refl OADDR PCF FISCR (fun pay => 1 <= pay <= 20) i c kk ps j cj ci g1 M0c OKV IL Hret Hcj Xpc Hchk).
      - intros pay Hp. unfold ESTU.PAYMAX. lia.
      - intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF.
        destruct (HEAP g1 M0c i E M1 m1 XB HA) as (HagE & _). pose proof (AGE i c E E' Hc0 HagE Hag) as HagE'.
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' (EVar 36) cnt IL HAt OKV HA HX Hag HLF XCNT' (proj1 (LEAFV E' HagE'))) as (HINV & _ & _ & _ & _).
        pose proof HX as (_ & Y2 & Y3 & Y4 & _). rewrite (GETA g1 i Y2 Y3 Y4) in HINV.
        split; [exact HINV|].
        rewrite Y3, Y4, XB', (DEN E' HagE'). unfold stack_blocks. destruct (Z.eqb_spec cb 0); [lia|]. intros b0 [<-|[]]. left. reflexivity.
      - intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP Hk.
        pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct HA' as (Hmo1 & _).
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' (EVar 36) cnt IL HAt OKV HA HX Hag HLF XCNT' (proj1 (LEAFV E' HagE'))) as (_ & _ & HIMG & _).
        pose proof HagE' as [AG _].
        assert (Ga0 : getr R' 10%bv = Z_to_bv 64 v).
        { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq, Xa0. cbn [edenot].
          rewrite <- AG by (unfold GT.NF; lia). rewrite <- Ha1. exact (EV 11%bv). }
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 (V + 8)).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq, Xa1.
          assert (UU : bv_unsigned (edenot E' SKE) = V + 8).
          { apply CL5.u_lin; [|lia]. unfold SKE. lin_eval. rewrite <- AG by (unfold GT.NF; lia). rewrite U10. lia. }
          rewrite <- UU. symmetry. apply Z_to_bv_bv_unsigned. }
        pose proof HINV as (J1 & _ & Hsink & Hln & _). pose proof J1 as (_ & HSK & _).
        pose proof HX as (_ & _ & _ & _ & (p0 & P0 & X5) & _). unfold PAYOK in P0. cbv beta in P0. rewrite XFI in P0. cbv iota in P0.
        apply (FROM_OK v (CH2.den E' (nth i G.BLS []) ++ LBo ++ []) cr1 (sp + CH2.ci_csp ci) (CC.cp_pc cj) (V + 8) S2 (ESTU.kxs L kx g1) (ESTU.bxs L bx g1) (g_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        { split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity | unfold FROMINT_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK; exact Hstk']]]]|].
          split; [split; [exact Ga0 | split; [exact VR | exact Ga1]]|].
          split; [unfold O_SINK in HSK; exact HSK|]. split; [lia|]. split; [lia|]. split; [unfold PML.apart; lia|].
          split; [exact Hsink|]. split; [unfold PML.obj_on_stack; lia|]. split; [exact HIMG|]. split; [exact HSC|].
          rewrite Hln, X5, P0. pose proof (OFFB i) as OB. lia. }
        intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 POST HRP HPRES Hbv2 HH2.
        apply (Hk fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 POST HRP HPRES Hbv2 HH2).
      - intros E R1 M1 m1 E' R' M' E2 M2 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HP HINV2 G1 G2 G3 G4 HPay _.
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' (EVar 36) cnt IL HAt OKV HA HX Hag HLF XCNT' (proj1 (LEAFV E' HagE'))) as (_ & _ & _ & HLITS & _).
        pose proof HX as (_ & Y2 & Y3 & Y4 & (p0 & P0 & Y5) & Y6 & _). unfold PAYOK in P0. cbv beta in P0. rewrite XFI in P0. cbv iota in P0.
        pose proof (HK' c ps E' R' M1 M' HLF) as HK.
        assert (JF : arr = EVU64B.PA j /\ ESI j = ESI i /\ OFF j = OFF i).
        { assert (Ej : Nat.eqb j 0 = false) by (apply Nat.eqb_neq; exact XJ0).
          destruct (Nat.eqb_spec i 0) as [Hi0|Hi0].
          - subst i. assert (TY0 : ty = 0) by (apply (TYV E' M' 0 HagE' HK); rewrite Xpc in XTY; exact XTY).
            pose proof (ARRTY 0 TY0) as A0. cbn in A0.
            rewrite XPA. split; [exact A0|]. unfold ESI, OFF; cbv beta. rewrite Ej. cbn [Nat.eqb pre_scalar ec_arr]. rewrite A0. split; reflexivity.
          - assert (Ei : Nat.eqb i 0 = false) by (apply Nat.eqb_neq; exact Hi0).
            rewrite XPA. split; [exact (Y6 Hi0)|]. unfold ESI, OFF; cbv beta. rewrite Ej, Ei. split; reflexivity. }
        destruct JF as (JF1 & JF2 & JF3).
        split; [exact HINV2|]. split; [rewrite G1, Y2; symmetry; exact JF2|]. split; [rewrite G2; exact Y3|]. split; [rewrite G3; exact Y4|].
        split; [exists pay; split; [unfold PAYOK; cbv beta; rewrite XFJ; exact HPay | rewrite G4, Y5, P0, JF3; lia]|].
        split; [intros _; exact JF1|].
        split; [exact (PML.lits_ok_agree M' M2 (HPLIT2 _ _ _ M' M2 HP) HLITS) | exact I]. }
    apply andb_prop in Xm as [Xm X28]. apply andb_prop in Xm as [Xm X32]. apply andb_prop in Xm as [Xm X26]. apply andb_prop in Xm as [Xm X8].
    apply andb_prop in Xm as [Xm XA0]. apply andb_prop in Xm as [Xm X2]. apply andb_prop in Xm as [Xpc XFI]. apply Z.eqb_eq in Xpc. subst pc.
    assert (I0 : Nat.eqb i 0 = false) by (destruct i; [cbn in XFI; discriminate XFI | reflexivity]).
    pose proof X2 as X2c. unfold PB.exit_base_chk in X2c. apply andb_prop in X2c as [X2c _]. apply andb_prop in X2c as [Hpspc _]. apply Z.eqb_eq in Hpspc.
    intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
    destruct (HEAP g1 M0c i E M1 m1 XB HAmb) as (HagE & _). pose proof (AGE i c E E' Hc0 HagE Hag) as HagE'.
    assert (CV : PB.uv E' (EAlu ALU_ADD (EVar 36) (ELit 1)) = (cnt + 1) mod 2 ^ 64).
    { change (EAlu ALU_ADD (EVar 36) (ELit 1)) with (APC.eaddz (EVar 36) 1). rewrite PB.uv_eaddz. rewrite (proj1 (LEAFV E' HagE')). reflexivity. }
    rewrite Hpspc in XCNT.
    destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' (EAlu ALU_ADD (EVar 36) (ELit 1)) ((cnt + 1) mod 2 ^ 64) IL HAt OKV HAmb HX Hag HLF XCNT CV)
      as (HINV & _ & _ & HLITS & _).
    pose proof HX as (_ & Y2 & Y3 & Y4 & (p & P & Y5) & _). unfold PAYOK in P. cbv beta in P. rewrite XFI in P. cbv iota in P.
    set (g' := EG (ECtx arr ((cnt + 1) mod 2 ^ 64) (ec_nla (hd ctx0 (ESI i))) :: r0) (g_len g1) (g_rep g1) b cb) in HINV.
    assert (DEFC : L5.defined M0c (sp - EVNB.SCRW) EVNB.SCRW) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
    apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo eghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
             (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
             EVNB.SCRW ltac:(rewrite SCRV; lia) SC3 DEFC R EV r Hra Hraok heap_ok3n EVU64B.RETPC i c kk ps EVU64B.RETPC EVU64B.ret_at IL X2 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
    intros HRP HP HA' _. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
    assert (HP2 : L5C.hpres L LBo sp EVNB.SCRW W M M').
    { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W eghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
    assert (Ga0 : PML.a0 R' 1).
    { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (ELit 1) HLF XA0) as G10.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). exact G10. }
    apply (Hcont fx' R' M' m1 (LBo ++ g_lbv g') cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
    + exists g', p. split; [exact Ga0|]. split; [exact HINV|]. split.
      { unfold g'. unfold ESI; cbv beta. rewrite I0. destruct arr; reflexivity. }
      split; [exact P|]. split.
      { unfold g'. cbn [g_len]. rewrite Y5. unfold OFF; cbv beta. rewrite I0. cbn [ev_ind quotes]. lia. }
      split; [exact HLITS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold CredV, EBU.CredV in HC1. unfold ecreditU, kenc, benc in *. unfold g'. cbn [g_rep g_scap]. rewrite <- Y4. exact HC1.
    + unfold CH2.cur, CH2V.LBr in HH1. rewrite XB', (DEN E HagE) in HH1. unfold gB, EBU.gB in HH1. rewrite app_nil_r in HH1.
      apply (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH1).
      unfold g', g_lbv, stack_blocks. cbn [g_rep g_sb g_scap]. destruct (Z.eqb_spec cb 0); [lia|].
      cbn [app]. rewrite app_assoc. apply Permutation_cons_append.
  - reflexivity.
  -
    rewrite LS.
    destruct I1 as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                    H24 & H25 & H26 & _).
    unfold O_SINK, O_STACK in *. rewrite ILO, IHI in B1.
    pose proof (fun o => ENDV E0 o (CC.env_agree_refl _ _)) as ES.
    unfold PML.img_ro, L5.img_clear, PML.IMG_RO_HI in Himg. unfold EVNB.SCRW in S5.
    unfold hl_ceil in *.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := V + 8) (z := S2); [ev_start | lia | lia | exact V32 | exact H2].
    + eapply CL5.kword64_intro with (A := V + 296) (z := col); [ev_start | lia | lia | exact V37 | exact Hcol].
    + e_range.
    + eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ DCOL); lia].
    + e_range. + e_align OV3.
    + e_range. + e_align OS3.
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ S5); lia].
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ S5); lia].
    + eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ S5); lia].
    + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
    + cbn [kentry_ok]. split; [lia | split; [lia | intros z Hz; apply Himg; lia]].
    + eapply CL5.kword64_intro with (A := V + 264) (z := b); [ev_start | lia | lia | exact V34 | exact T1].
    + eapply CL5.kword64_intro with (A := V + 272) (z := b + 32 * (dr + 1)); [ev_start | lia | lia | exact WEND | replace (V + 272) with (V + 264 + 8) by lia; exact T2].
    + eapply PB.kword32_intro with (A := b + 32 * dr) (z := ty); [rewrite ES; lia | lia | lia | exact V38 | exact HQ1].
    + e_range.
    + eapply PB2.kword8_intro with (A := b + 32 * dr + 4) (z := 0); [rewrite ES; lia | lia | lia | reflexivity | lia | exact HQ2].
    + eapply PB2.kword8_intro with (A := b + 32 * dr + 5) (z := ib mod 256); [rewrite ES; lia | lia | lia | exact V39 | lia | exact Hib'].
    + eapply PB2.kword8_intro with (A := b + 32 * dr + 6) (z := nlz); [rewrite ES; lia | lia | lia | exact V40 | lia | exact HQ3].
    + e_range.
    + eapply CL5.kword64_intro with (A := b + 32 * dr + 24) (z := cnt); [rewrite ES; lia | lia | lia | exact V36 | exact HQ4].
    + eapply CL5.kwr_intro; [apply ES | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ HQ6); lia].
    + eapply CL5.kunk_intro; [apply ES | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ HQ6); lia].
    + e_range. + e_range. + e_range. + e_range. + e_align B2. + e_range.
    + e_disj. + e_disj. + e_disj.
  -
    apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS eghost gB CredV XIv (EG (ECtx arr cnt nla0 :: r0) len0 rep b cb) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split.
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr. split; [|exact Hcred].
      unfold CH2.cur, CH2V.LBr. change (CH2.den E0 (nth 0 G.BLS [])) with (CH2.den E0 EVNB.BL1). rewrite (DEN E0 (CC.env_agree_refl _ _)).
      unfold gB, EBU.gB. cbn [g_rep app]. rewrite app_nil_r. exact HHp.
    + split; [exact Hinv|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; split; [reflexivity | unfold OFF; cbn; lia]|].
      split; [intros X; exfalso; apply X; reflexivity|]. split; [exact Hlits | exact I].
  - exact Hfp.
Qed.
End Nested.
End EVU64NU.
