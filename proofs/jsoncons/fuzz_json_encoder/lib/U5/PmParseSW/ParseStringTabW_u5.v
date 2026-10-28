(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParseSW Require Import UvZ. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseSW Require Import ParseStringKW_u5 ParseStringBitsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_ps_xsrcw_T_u5 Cut_ps_xsrcw_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Lists; @ListDef; @nth]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cutpoint]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @G; @CPS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @dummy_cp]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_STR_PUSH_BACK]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_STR_APPEND]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_SET_EC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_END_STRING]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAluw]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EExt]; [@Corelib; @Init; @Datatypes; @true]; [@Corelib; @Init; @Datatypes; @O]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @bool]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @CUR0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ADD]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @NEG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @RUNL]; [@Corelib; @Init; @Datatypes; @option]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@Corelib; @Init; @Datatypes; @false]; [@Corelib; @Init; @Datatypes; @list]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @has]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @has]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @rootn]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @root]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fam]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FText]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FEsc]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FU4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FPair]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FU8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @FOther]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @cls]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Corelib; @Init; @Datatypes; @Some]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @CD]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @CL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @CU]; [@Corelib; @Init; @Datatypes; @None]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SLLW]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @EXT4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ORE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ADDW]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @clsk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SRLE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @MULE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @t1_form]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ANDE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @atomA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @pair_form]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @A4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @hex_form]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SLTUE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SUBE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SRLW]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @hasr]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @region]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fe_surr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fe_lt128]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fe_lt2k]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fe_lt64k]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @fe_gt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @RSurr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @R1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @R2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @R3]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @RRep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @R4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @vexp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringKW_u5; @PSKW; @cpu]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ckind]; [@Stdlib; @Bool; @Bool; @eqb]; [@Corelib; @Init; @Logic; @eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ckind_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KEntry]; [@Corelib; @Init; @Logic; @eq_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KStep]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Logic; @False_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KText]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KPush]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KSetEc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KEsv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KDead]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KBad]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @Bool; @Bool; @eqb_prop]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @Lists; @List; @filter]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RelLeaf; @RLF; @byte_adm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @bytes256]; [@Stdlib; @Lists; @List; @forallb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @curform]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ENDE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KBlob]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @jlt_fact]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @oeqb]; [@Corelib; @Init; @Datatypes; @negb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @needs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @keep_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @hexclass]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @lin_form]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @TAGX]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SIZX]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @PTRX]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @subst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @slook]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @reg_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @H4]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @H8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @BV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @post_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @tag]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reglist]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @admlist]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @lres]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @goto_other_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @goto_step_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @RETPC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @exit_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @PUSHB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @push_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @APPEND]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @app_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @SETEC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @setec_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @ESV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @Leaf; @esv_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @LBad]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @LOk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @LPost]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @cutn]; [@Stdlib; @Lists; @List; @nth_error]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_PSS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @G; @TAGS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @leaf_eval]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @KTAB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @build]; [@Corelib; @Init; @Datatypes; @length]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParseSW; @ParseStringTabW_u5; @PSCW; @wl_chk]].

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSCW.
Import PML PMR PSKW.
Module G := Cut_ps_xsrcw_u5.
Module GT := Cut_ps_xsrcw_T_u5.
Definition cutn (i : nat) : CC.cutpoint := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$i;R+0!4'1+2#1'3'4").
Definition RETPC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5|B09710;").
Definition PUSHB : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'6"). Definition APPEND : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'7"). Definition SETEC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'8"). Definition ESV : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'9").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition V (n : nat) : expr := EVar n.
Definition ADD (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,<#2#1").
Definition SUBE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,=#2#1").
Definition ANDE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,>#2#1").
Definition ORE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,?#2#1").
Definition SRLE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,@#2#1").
Definition SLTUE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,;,A#2#1").
Definition MULE (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,B,C#2#1").
Definition ADDW (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,D,<#2#1").
Definition SLLW (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,D,E#2#1").
Definition SRLW (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+:$b;R+:!3,D,@#2#1").
Definition EXT4 (a : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$a;R+:!4,F,G,H}4#1").
Definition NEG (a : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$a;R+:!3,B,C!1,I!1,J,K#1").
(* [comment removed for export] *)
Definition CUR0 : expr := ADD (V 11) (ADD (V 32) (NEG (V 53))).
Definition curform (c : Z) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+L-MRN$~R+M+:!2'N#1,O2'P!2'Q'P!1,I#1").
Definition ENDE : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10};!2'Q!1'R0!1'R}P").
Definition RUNS : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10};!2'Q!1'R0!1'R}^A").
Definition RUNL : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20}P}^8!2'Q!1'R0!2'Q!1'S!1'R1!1'S!1'R}^A").
Definition RUNL1 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'Q'T!1,I!1,5,K").
Definition JM1 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'Q!1'R}^8!1,I!1,J,K").
Definition SBO0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10}P!2'Q!1'R0!1'S!1'R}^8").
(* [comment removed for export] *)
Fixpoint cellv (cells : list kentry) (off : Z) (w : nat) : option expr :=
  match cells with
  | [] => None
  | KWord (SA (EVar 10) o) w' v :: r => if ((o =? off) && Nat.eqb w' w)%bool then Some v else cellv r off w
  | _ :: r => cellv r off w
  end.
Definition CPX (i : nat) := cellv (CC.cp_know (cutn i)) 148 4.
Definition CP2X (i : nat) := cellv (CC.cp_know (cutn i)) 152 4.
Definition TAGX (i : nat) := cellv (CC.cp_know (cutn i)) 220 1.
Definition SIZX (i : nat) := cellv (CC.cp_know (cutn i)) 232 8.
Definition PTRX (i : nat) := cellv (CC.cp_know (cutn i)) 240 8.
Definition oeqb (a : option expr) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R!1+U+:$e;R+:-URN$a;R!1+U+:+M#22$x;R+:!2'V#1#2,W").
Definition has (cells : list kentry) (k : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cells;R!1+X+Y$k;R+Y!2'Z#2#1").
Definition hasr (cells : list kentry) (e : expr) (lo hi : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$cells;R!1+X+Y$e;R+:$lo;R+L$hi;R+L!2'[#4!3,\#3#2#1").
(* [comment removed for export] *)
Definition parent (j : nat) : option (nat * nat) :=
  match find (fun r : nat * nat * nat * Z => let '(j', _, _, _) := r in Nat.eqb j j') G.RETS with Some (_, i, k, _) => Some (i, k) | None => None end.
Fixpoint rootn (fuel : nat) (j : nat) : nat := match fuel with O => j | S f => match parent j with Some (i, _) => rootn f i | None => j end end.
Definition root (j : nat) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$j;R+0!2'^0}<#1").
(* [comment removed for export] *)
Definition BV (i : nat) : nat := if Nat.eqb (root i) 1 then 105%nat else 111%nat.
Inductive fam := FText | FEsc | FU4 | FPair | FU8 | FOther.
Definition famof (i : nat) : fam := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S80}1}2}3}4}7}8}9}:$i;R+0&r;R!1'^1#1+0-MRN$~R+M+^2!2'^3!2'^4#10!2'^4#112,^5-MRN$~R+M+^2!2'^4#122,^6-MRN$~R+M+^2!2'^7!2'^83#1!2'^8#142,^9-MRN$~R+M+^2!2'^7!2'^85#1!2'^8#162,^:-MRN$~R+M+^2!2'^7!2'^87#1!2'^8#1}=2,^;,^<").

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive cls := CD | CL | CU.
Definition clsk (q : cls) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$q;R+^=-^=RN$q;R+^=+L#13!1,5|510;!1,5|617;!1,5|517;").
Definition hexclass (b : Z) : option cls := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1+U+^=|510;$b;R+L-MRN$~R+M0!2'^7!2'^>!1,51#1!2'^>#1!1,5|519;2!2,^?+^=,^@-MRN$~R+M0!2'^7!2'^>!1,5|621;#1!2'^>#1!1,5|626;2!2,^?+^=,^A-MRN$~R+M0!2'^7!2'^>!1,5|601;#1!2'^>#1!1,5|606;2!2,^?+^=,^B!1,^C+^=").
Definition hex_form (q : cls) (ecp eb : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!2'Q#2#1$q;R+^=$ecp;R+:$eb;R+:&sh;R!2'^D!1'^E#2!1,I!1,5|20;+:-^=RN$q;R+^=+:#43!2'^F!2'Q#2!1,I!1,J|510;#1!2'^G0!1,I!1,J|617;!2'^G0!1,I!1,J|517;").
Definition lin_form (q : cls) (eb : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$q;R+^=$eb;R+:!2'Q#1!1,I!1'^H!1'^I#2").
Definition t1_form (ecp : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ecp;R+:!2'^J!2'^K!1,I!1,5|^900000000000000;!1'^E#1!1,I!1,5|50c;").
Definition pair_form (ecp a2 : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$ecp;R+:$a2;R+:!2'Q!2'^F!1'^L#2!2'^M#1!1,I!1,5|91ff;!1,I!1,5|@0000;").
(* [comment removed for export] *)
Definition atomA (f : fam) (q : cls) : expr := match f with FU8 => hex_form q (V 59) (V 111) | _ => hex_form q (V 58) (V 111) end.
Definition holderH (f : fam) (q : cls) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1'^E!2'^N#2#1$f;R+^2$q;R+^=-^2RN$f;R+^2+:#260000!1'^E!2'^O!1'R}^=!2'^N,^;#10").
(* [comment removed for export] *)
Definition A4 (q : cls) : expr := hex_form q (V 58) (V 111).
Definition H4 (q : cls) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$q;R+^=!1'^E!1'^P#1").
Definition H8 (q : cls) : expr := EXT4 (pair_form (V 58) (hex_form q (V 59) (V 111))).
(* [comment removed for export] *)
Definition fe_hs (A : expr) : expr := SLTUE (SUBE (SRLW A (ELit 10)) (ELit 54)) (ELit 1).
Definition fe_lt128 (H : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$H;R+:!2'^R#1!1,I!1,5|700;").
Definition fe_surr (H : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$H;R+:!2'^R!2'^S!2'^K!1,I!1,5|;000;!2'^J#1!1,I!1,5|33;!1,I!1,5|?5800;!1,I!1,5,K").
Definition fe_lt2k (H : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$H;R+:!2'^R!2'^S!2'^T#1!1,I!1,5|33;!1,I,O!1,I!1,5,K").
Definition fe_lt64k (H : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$H;R+:!2'^R!2'^S!2'^T#1!1,I!1,5|40;!1,I,O!1,I!1,5,K").
Definition fe_gt (H : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1,I!1,5|40;$H;R+:!2'^R0!2'^T#10").
Definition lit (cells : list kentry) (e : expr) : option bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!1+U+M!1,5,K$cells;R!1+X+Y$e;R+:-MRN$~R+M0!4'^U#2#1112!2,^?+M,G-MRN$~R+M0!4'^U#2#1,O,O2!2,^?+M,W!1,^C+M").
(* [comment removed for export] *)
Definition ve_and255 (H : expr) : expr := ANDE H (ELit 255).
Definition ve_cont0 (H : expr) : expr := ANDE (ADD (ANDE H (ELit 63)) (ELit (-128))) (ELit 255).
Fixpoint srl6 (n : nat) (H : expr) : expr := match n with O => H | S n1 => EAluw Instr.ALU_SRL (srl6 n1 H) (ELit 6) end.
Definition ve_cont (H : expr) (k : Z) : expr := ANDE (ADD (ANDE (srl6 (Z.to_nat (k / 6)) H) (ELit 63)) (ELit (-128))) (ELit 255).
Definition ve_lead (H : expr) (k m : Z) : expr := ANDE (ADD (ANDE (srl6 (Z.to_nat (k / 6)) H) (ELit (- m - 1))) (ELit m)) (ELit 255).
(* [comment removed for export] *)
Inductive region := R1 | R2 | R3 | R4 | RRep | RSurr.
Definition region_eqb (a b : region) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+^W$b;R+^W-^WRN$a;R+^W+M#26-^WRN$b;R+^W+M#16,G,W,W,W,W,W-^WRN$b;R+^W+M#16,W,G,W,W,W,W-^WRN$b;R+^W+M#16,W,W,G,W,W,W-^WRN$b;R+^W+M#16,W,W,W,G,W,W-^WRN$b;R+^W+M#16,W,W,W,W,G,W-^WRN$b;R+^W+M#16,W,W,W,W,W,G").
Definition klen (r : region) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S30}1}2}3$r;R+^W-^WRN$r;R+^W+0#16012}42,H").
Definition reg_of (cells : list kentry) (H : expr) : option region := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!1+U+M!1+U+^W!1,^C+^W$cells;R!1+X+Y$H;R+:&ls;R!2'^X#2!1'^Y#10&l1;R!2'^X#3!1'^Z#20&l2;R!2'^X#4!1'^[#30&l3;R!2'^X#5!1'^\#40&lg;R!2'^X#6!1'_0#50-URN$ls;R!1+U+M1#52$b;R+M-MRN$b;R+M1#12!2,^?+^W,_1-URN$l1;R!1+U+M1#52$b;R+M-MRN$b;R+M1#12!2,^?+^W,_2-URN$l2;R!1+U+M1#52$b;R+M-MRN$b;R+M1#12!2,^?+^W,_3-URN$l3;R!1+U+M1#52$b;R+M-MRN$b;R+M1#12!2,^?+^W,_4-URN$lg;R!1+U+M1#52$b;R+M-MRN$b;R+M1#12!2,^?+^W,_5!2,^?+^W,_622222").
(* [comment removed for export] *)
Definition vexp (H : expr) (r : region) (idx : nat) : option expr :=
  match r, idx with
  | R1, 0 => Some (ve_and255 H)
  | R2, 0 => Some (ve_lead H 6 192) | R2, 1 => Some (ve_cont0 H)
  | R3, 0 => Some (ve_lead H 12 224) | R3, 1 => Some (ve_cont H 6) | R3, 2 => Some (ve_cont0 H)
  | R4, 0 => Some (ve_lead H 18 240) | R4, 1 => Some (ve_cont H 12) | R4, 2 => Some (ve_cont H 6) | R4, 3 => Some (ve_cont0 H)
  | RRep, 0 => Some (ELit 239) | RRep, 1 => Some (ELit 191) | RRep, 2 => Some (ELit 189)
  | _, _ => None
  end%nat.
Definition vshape_ok (H : expr) (r : region) (idx : nat) (a1 : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$H;R+:$r;R+^W$idx;R+0$a1;R+:-URN$x;R!1+U+:+M!3'_7#4#3#22$e;R+:!2'V#2#1,W").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ckind := KEntry | KStep (sst c : Z) | KText | KPush (u8 : bool) (m : nat) (c : Z) | KSetEc (code : Z) | KEsv | KDead | KBad.
Definition cpu_eqb (a b : cpu) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2'N#2#1$a;R+_8$b;R+_8-_8RN$a;R+_8+M#23-_8RN$b;R+_8+M#13,G$v;R+L,W$d;R+L,W$x;R+L-_8RN$b;R+_8+M#23,W$y;R+L0$d;R+L,W$x;R+L-_8RN$b;R+_8+M#23,W$v;R+L,W$y;R+L0").
Definition ckind_eqb (a b : ckind) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+_9$b;R+_9-_9RN$a;R+_9+M#28-_9RN$b;R+_9+M#18,G$sst;R+L$c;R+L,W,W$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,W,W,W$s1;R+L$c1;R+L-_9RN$b;R+_9+M#38,W$s2;R+L$c2;R+L!2'^7!2'N#4#2!2'N#3#1,W$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,W,W,W-_9RN$b;R+_9+M#18,W$sst;R+L$c;R+L,W,G$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,W,W,W$u1;R+M$m1;R+0$c1;R+L-_9RN$b;R+_9+M#48,W$sst;R+L$c;R+L,W,W$u2;R+M$m2;R+0$c2;R+L!2'^7!2'^7!2'_:#6#3!2'^4#5#2!2'N#4#1$code;R+L,W,W,W,W$x;R+L-_9RN$b;R+_9+M#28,W$sst;R+L$c;R+L,W,W$u8;R+M$m;R+0$c;R+L,W$y;R+L!2'N#2#1,W,W,W-_9RN$b;R+_9+M#18,W$sst;R+L$c;R+L,W,W$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,G,W,W-_9RN$b;R+_9+M#18,W$sst;R+L$c;R+L,W,W$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,W,G,W-_9RN$b;R+_9+M#18,W$sst;R+L$c;R+L,W,W$u8;R+M$m;R+0$c;R+L,W$code;R+L,W,W,W,G").
Lemma ckind_eqb_eq : forall a b, ckind_eqb a b = true -> a = b.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SR0!2,_?#2#1!6'_@+M,W$e;R+M-MRN$b;R+Mw#12+_A+_B,_C,G#1!2,_?#4#3!3,_F#3#2#1!3,_F#5#4#3!1,_G#1!1,_G#3!2,_?#5#4!2,_?#3#2!2,_?#7#6!2'N#8#3!2'N#7#2!3+_;+M:,G!3+_;+M!2'N#9#4,G!3+_;+M!2'N#;#6,G%~R!3+_;+M!2'N#2#1,G!3+_;+L#3#2$n;R+L$m;R+L!5'_M?%~R!3+_;+L#2#1!3+_;+M!2'N#3#2,G%~R!3+_;+M!2'N#2#1,G!3+_;+L#3#2$~R?$~R%~R!3+_;+L#3#2!3+_;+M!2'N#4#3,G#2!2'_N#2#1%n;R+L%m;R+L?!2,_?#=#<!3,_F#6#5#4!3,_F#4#3#2!3,_F#8#7#6!3,_F#:#9#8!2'^7!2'_:#;#4!2'^4#:#3!2'N#9#2!3+_;+M!2'^7!2'_:#<#5!2'^4#;#4,G!2'_:#@#9!2'^4#?#8!3+_;+M!2'_:#A#:,G%~R!3+_;+M!2'^4#2#1,G!3+_;+0#3#2!3,_F#D#C#B!1,_G#4!1,_G#2!1,_G#8$a;R+_9-_9RN$c;R+_9%b;R+_9%~R!3+_;+M!2'_<#2#1,G!3+_;+_9#3#2#18$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<,_=#1,G!3+_;+_9,_=#2#18$H;R!3+_;+M!2'_<,_=,_=,G!2,_>+_9,_=$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<,_=0,G&H0;R1+_A!2'_D!3+_;+_9,_=2#1#2#1$H;R!3+_;+M!2'_<,_=,_E,G&H0;R1+_A!2'_D!3+_;+_9,_=,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<,_=3,G&H0;R1+_A!2'_D!3+_;+_9,_=4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<,_=5,G&H0;R1+_A!2'_D!3+_;+_9,_=6#1#1$H;R!3+_;+M!2'_<,_=,_H,G&H0;R1+_A!2'_D!3+_;+_9,_=,_H#1$H;R!3+_;+M!2'_<,_=,_I,G&H0;R1+_A!2'_D!3+_;+_9,_=,_I#1$H;R!3+_;+M!2'_<,_=,_J,G&H0;R1+_A!2'_D!3+_;+_9,_=,_J#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<2#1,G!3+_;+_97#2#18$H;R!3+_;+M!2'_<8,_=,G&H0;R1+_A!2'_D!3+_;+_97,_=#1$sst;R+L$c;R+L!2$sst0;R+L$c0;R+L$H;R!3+_;+M!2'_<90,G&H;R!3'_K:;#1!2+_L<!3+_;+M;,G!5'_M=<!3+_;+_9!2,_?#9#8!2,_?#4#3$~R=$~R!3+_;+M!2'N#9#4,G!2$H1;R>$H2;R>&H;R@A&H1;R!3#1#>#9#3!3+_;+L#>#9&H;R@A&H2;R!3#1#?#:#4!3+_;+L#?#:!6'_O+L#<$sst;R+L!3+_;+_9!2,_?#1#AB!6'_O+L#;$c;R+L!3+_;+_9!2,_?#=#1B!2,_>+_9!2,_?#<#;#@#1#A#3#2#1#1#2#1$H;R!3+_;+M!2'_<8,_E,G&H0;R1+_A!2'_D!3+_;+_97,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c0;R+L$H;R!3+_;+M!2'_<!2,_?#9#83,G&H0;R1+_A!2'_D!3+_;+_9!2,_?#;#:4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<75,G&H0;R1+_A!2'_D!3+_;+_996#1#1$H;R!3+_;+M!2'_<8,_H,G&H0;R1+_A!2'_D!3+_;+_97,_H#1$H;R!3+_;+M!2'_<8,_I,G&H0;R1+_A!2'_D!3+_;+_97,_I#1$H;R!3+_;+M!2'_<8,_J,G&H0;R1+_A!2'_D!3+_;+_97,_J#1#2#1$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<,_E#1,G!3+_;+_9,_E#2#18$H;R!3+_;+M!2'_<,_E,_=,G&H0;R1+_A!2'_D!3+_;+_9,_E,_=#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<,_E0,G&H0;R1+_A!2'_D!3+_;+_9,_E2#1#2#1$H;R!3+_;+M!2'_<,_E,_E,G!2,_>+_9,_E$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<,_E3,G&H0;R1+_A!2'_D!3+_;+_9,_E4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<,_E5,G&H0;R1+_A!2'_D!3+_;+_9,_E6#1#1$H;R!3+_;+M!2'_<,_E,_H,G&H0;R1+_A!2'_D!3+_;+_9,_E,_H#1$H;R!3+_;+M!2'_<,_E,_I,G&H0;R1+_A!2'_D!3+_;+_9,_E,_I#1$H;R!3+_;+M!2'_<,_E,_J,G&H0;R1+_A!2'_D!3+_;+_9,_E,_J#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<4#1,G!3+_;+_9C#2#18$H;R!3+_;+M!2'_<D,_=,G&H0;R1+_A!2'_D!3+_;+_9C,_=#1$sst;R+L$c;R+L!2$sst;R+L$c0;R+L$H;R!3+_;+M!2'_<E0,G&H0;R1+_A!2'_D!3+_;+_9F2#1#2#1$H;R!3+_;+M!2'_<D,_E,G&H0;R1+_A!2'_D!3+_;+_9C,_E#1$u8;R+M$m;R+0$c;R+L!3$u10;R+M$m0;R+0$c0;R+L$H;R!3+_;+M!2'_<F3,G&H;R!3'_KGH#1!2+_L!3+_;+MG,G!3+_;+MH,G!5'_MI!3+_;+M!2'N#:#3,G!3+_;+_9!3,_F#<#;#:!3,_F#5#4#3$~RI$~R!3+_;+M!2'N#;#4,G!2$H;R!3+_;+M!2'^7!2'_:#>#7!2'^4#=#6,G$H3;R!3+_;+M!2'N#=#6,G&H;R!3'_KJK#2!2+_L!3+_;+MJ,G!3+_;+MK,G!5'_ML!3+_;+M!2'^4#@#9,G!3+_;+_9!3,_F#A#@#?!3,_F#:#9#8$~RL$~R!3+_;+M!2'^4#A#:,G!2$H1;R!3+_;+M!2'_:#C#<,G$H2;R!3+_;+M!2'^4#C#<,G&H1;R!3'_P#E#>#2!3+_;+M#E#>&H;R$n;R+0$m;R+0!5'_MM%~R!3+_;+0#2#1!3+_;+M!2'^4#3#2,G%~R!3+_;+M!2'^4#2#1,G!3+_;+0#3#2$~RM$~R%~R!3+_;+0#3#2!3+_;+M!2'^4#4#3,G#2!2'_Q#2#1%n;R+0%m;R+0M&H2;R!3#1#F#?#3!3+_;+0#F#?&H;R@A&H3;R!3#1#G#@#:!3+_;+L#G#@!6'_O+M#C$u9;R+M!3+_;+_9!3,_F#1#J#IN!6'_O+0#B$m;R+0!3+_;+_9!3,_F#D#1#IN!6'_O+L#A$c;R+L!3+_;+_9!3,_F#D#C#1N!2,_>+_9!3,_F#C#B#A#H#1#I#3#J#5#2#1#1#2#1#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<C5,G&H0;R1+_A!2'_D!3+_;+_9E6#1#1$H;R!3+_;+M!2'_<D,_H,G&H0;R1+_A!2'_D!3+_;+_9C,_H#1$H;R!3+_;+M!2'_<D,_I,G&H0;R1+_A!2'_D!3+_;+_9C,_I#1$H;R!3+_;+M!2'_<D,_J,G&H0;R1+_A!2'_D!3+_;+_9C,_J#1#3#2#1$code;R+L!1$code;R+L$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<6#1,G!3+_;+_9O#2#18$H;R!3+_;+M!2'_<P,_=,G&H0;R1+_A!2'_D!3+_;+_9O,_=#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<!1,_G#60,G&H0;R1+_A!2'_D!3+_;+_9Q2#1#2#1$H;R!3+_;+M!2'_<P,_E,G&H0;R1+_A!2'_D!3+_;+_9O,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<Q3,G&H0;R1+_A!2'_D!3+_;+_9!1,_G#:4#1#3#2#1$code;R+L!1$code0;R+L$H;R!3+_;+M!2'_<O5,G&H0;R@A&H;R!3#1#6#3#2!3+_;+L#6#3!6'_O+L#4$code;R+L!3+_;+_95!1,_G#5!2,_>+_9O#7#1#1$H;R!3+_;+M!2'_<P,_H,G&H0;R1+_A!2'_D!3+_;+_9O,_H#1$H;R!3+_;+M!2'_<P,_I,G&H0;R1+_A!2'_D!3+_;+_9O,_I#1$H;R!3+_;+M!2'_<P,_J,G&H0;R1+_A!2'_D!3+_;+_9O,_J#1#1$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<,_H#1,G!3+_;+_9,_H#2#18$H;R!3+_;+M!2'_<,_H,_=,G&H0;R1+_A!2'_D!3+_;+_9,_H,_=#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<,_H0,G&H0;R1+_A!2'_D!3+_;+_9,_H2#1#2#1$H;R!3+_;+M!2'_<,_H,_E,G&H0;R1+_A!2'_D!3+_;+_9,_H,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<,_H3,G&H0;R1+_A!2'_D!3+_;+_9,_H4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<,_H5,G&H0;R1+_A!2'_D!3+_;+_9,_H6#1#1$H;R!3+_;+M!2'_<,_H,_H,G!2,_>+_9,_H$H;R!3+_;+M!2'_<,_H,_I,G&H0;R1+_A!2'_D!3+_;+_9,_H,_I#1$H;R!3+_;+M!2'_<,_H,_J,G&H0;R1+_A!2'_D!3+_;+_9,_H,_J#1$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<,_I#1,G!3+_;+_9,_I#2#18$H;R!3+_;+M!2'_<,_I,_=,G&H0;R1+_A!2'_D!3+_;+_9,_I,_=#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<,_I0,G&H0;R1+_A!2'_D!3+_;+_9,_I2#1#2#1$H;R!3+_;+M!2'_<,_I,_E,G&H0;R1+_A!2'_D!3+_;+_9,_I,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<,_I3,G&H0;R1+_A!2'_D!3+_;+_9,_I4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<,_I5,G&H0;R1+_A!2'_D!3+_;+_9,_I6#1#1$H;R!3+_;+M!2'_<,_I,_H,G&H0;R1+_A!2'_D!3+_;+_9,_I,_H#1$H;R!3+_;+M!2'_<,_I,_I,G!2,_>+_9,_I$H;R!3+_;+M!2'_<,_I,_J,G&H0;R1+_A!2'_D!3+_;+_9,_I,_J#1$b;R+_9-_9RN$c;R+_9%~R!3+_;+M!2'_<,_J#1,G!3+_;+_9,_J#2#18$H;R!3+_;+M!2'_<,_J,_=,G&H0;R1+_A!2'_D!3+_;+_9,_J,_=#1$sst;R+L$c;R+L!2$sst;R+L$c;R+L$H;R!3+_;+M!2'_<,_J0,G&H0;R1+_A!2'_D!3+_;+_9,_J2#1#2#1$H;R!3+_;+M!2'_<,_J,_E,G&H0;R1+_A!2'_D!3+_;+_9,_J,_E#1$u8;R+M$m;R+0$c;R+L!3$u9;R+M$m;R+0$c;R+L$H;R!3+_;+M!2'_<,_J3,G&H0;R1+_A!2'_D!3+_;+_9,_J4#1#3#2#1$code;R+L!1$code;R+L$H;R!3+_;+M!2'_<,_J5,G&H0;R1+_A!2'_D!3+_;+_9,_J6#1#1$H;R!3+_;+M!2'_<,_J,_H,G&H0;R1+_A!2'_D!3+_;+_9,_J,_H#1$H;R!3+_;+M!2'_<,_J,_I,G&H0;R1+_A!2'_D!3+_;+_9,_J,_I#1$H;R!3+_;+M!2'_<,_J,_J,G!2,_>+_9,_J").
Qed.
Definition ck_c (k : ckind) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1,^C+L!2,^?+L#1$k;R+_9-_9RN$k;R+_9!1+U+L#180$sst;R+L$c;R+L1!2,^?+L,O$u8;R+M$m;R+0$c;R+L1$code;R+L0000").
Definition ck_sst (k : ckind) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S30!1+U+L!1,^C+L|21;$k;R+_9-_9RN$k;R+_90#181$s;R+L$c;R+L!2,^?+L#2!2,^?+L,O$u8;R+M$m;R+0$c;R+L-MRN$u8;R+M0#32!2,^?+L!1,5|33;!2,^?+L!1,52$code;R+L1111").
Definition DSST (j : nat) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S50!1,J,K|10;|11;|20;|21;$j;R+0!4'1+L#1!3,_R+L0!3,_R+L,O!3,_R+L,O!3,_R+L!1,5,K!3,_R+L!1,51!3,_R+L!1,52!3,_R+L!1,53!3,_R+L!1,54!3,_R+L!1,5|22;!3,_R+L!1,5|23;!3,_R+L!1,5|30;!3,_R+L!1,5|31;!3,_R+L!1,5|32;!3,_R+L!1,5|33;!1,_S+L0").
Inductive lres := LBad (why : nat) | LOk | LPost (k : ckind).
(* [comment removed for export] *)
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).
Definition admlist (cells : list kentry) (bv : nat) : list Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cells;R!1+X+Y$bv;R+0!3'_T+L$b;R+L!3'_U#2#3#1'_V").
Definition allb (adm : list Z) (f : Z -> bool) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$adm;R!1+X+L$f;R%~R+L+M!3'_W+L#1#2").
Definition someb (adm : list Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$adm;R!1+X+L-XRN$adm;R!1+X+L+M#12,W$z;R+L$l;R!1+X+L,G").
(* [comment removed for export] *)
Definition exh_fact (cells : list kentry) (c : Z) : bool :=
  hasr cells (V 53) c c || hasr cells (SLTUE (curform c) ENDE) 0 0 || hasr cells (SLTUE (SUBE (curform c) ENDE) (ELit 1)) 1 1.
Definition lt_fact (cells : list kentry) (c : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1,5,K$cells;R!1+X+Y$c;R+L!4'^U#2!2'^R!1'_X#1'_Y00").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition jlt_fact (cells : list kentry) (c : Z) : bool :=
  lt_fact cells c || existsb (fun k => match k with KRange (EVar 53) lo _ => c + 1 <=? lo | _ => false end) cells.
Definition hasb (cells : list kentry) (c : Z) (bv : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S30}1!1'R#1};$cells;R!1+X+Y$c;R+L$bv;R+0!2'^7!2'^7!2'^7!2'[#3!3,_Z!2,_[!1'_X#2,O01!2'[#3!3,_\!2,_[!1'R2,O!1'R}P0!4'^U#31,O!1,5|77f;!2'`0#3#2").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition needs (var : nat) (s : Z) : bool := if Nat.eqb var 58 then (3 <=? s) && (s <=? 11) else (9 <=? s) && (s <=? 11).
Definition keep_ok (cur : option expr) (var : nat) (e : expr) (sstj : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$cur;R!1+U+:$var;R+0$e;R+:$sstj;R+L!2'^3!2'`1#4#2!1'`2!2'`3#3#1").
Definition upd_ok (bv : nat) (cur : option expr) (var : nat) (u : cpu) (b : Z) (e : expr) (sstj : Z) : bool :=
  match u with
  | UKeep => keep_ok cur var e sstj
  | USet v => (expr_eqb e (ELit v) || (Nat.eqb bv 111 && match hexclass b with Some q => expr_eqb e (lin_form q (V 111)) && Z.eqb v (b - clsk q) | None => false end))%bool
  | UHex d => (Nat.eqb bv 111 && match hexclass b with Some q => oeqb cur (V var) && expr_eqb e (hex_form q (V var) (V 111)) && Z.eqb d (b - clsk q) | None => false end)%bool
  end.
Definition tag_ok (i : nat) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$i;R+0$e;R+:!2'^3!2'`1!1'`7#2#1!2'V#1!1,I,O").
Definition buf_ok (i : nat) (esz eptr : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$i;R+0$esz;R+:$eptr;R+:!2'^7!2'`1!1'`8#3#2!2'`1!1'`9#3#1").
Definition sub (s : CC.subst) (n : nat) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$s;R'`:$n;R+0!2'`;#2#1").

Section Leaf.
Variable K : nat -> ckind.
(* [comment removed for export] *)
Definition regq (i : nat) (cells : list kentry) (q : cls) : option region := reg_of cells (holderH (famof i) q).
Definition reg4 (cells : list kentry) (q : cls) : option region := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cells;R!1+X+Y$q;R+^=!2'`<#2!1'`=#1").
Definition reg8 (cells : list kentry) (q : cls) : option region := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cells;R!1+X+Y$q;R+^=!2'`<#2!1'`>#1").
Definition b85 (i : nat) : bool := Nat.eqb (BV i) 111%nat.
(* [comment removed for export] *)
Definition goto_step_chk (i : nat) (sst c : Z) (cells : list kentry) (adm : list Z) (j : nat) (s : CC.subst) : lres :=
  let f := famof i in
  let dj := if expr_eqb (sub s 53) JM1 then Some 1 else if expr_eqb (sub s 53) (V 53) then Some 0 else None in
  match dj, ck_c (K j), ck_sst (K j) with
  | Some dj, Some cj, Some sstj =>
      let delta := cj + dj - c in
      let frame := tag_ok i (sub s 60) && buf_ok i (sub s 55) (sub s 56) &&
                   match K j with KText => if Nat.eqb i 2 then expr_eqb (sub s 62) SBO0 else if Nat.eqb i 1 then expr_eqb (sub s 62) (V 62) else false
                              | KStep _ _ => negb (Nat.eqb i 1) | _ => false end in
      if negb frame then LBad 1
      else if delta =? 0 then
        (if (sstj =? sst) && keep_ok (CPX i) 58 (sub s 58) sstj && keep_ok (CP2X i) 59 (sub s 59) sstj && negb (Nat.eqb i 1) then LOk else LBad 2)
      else if delta =? 1 then
        let text_loop := (Nat.eqb i 1 && Nat.eqb j 1)%bool in
        if someb adm && hasb cells c (BV i) &&
           allb adm (fun b =>
             match sdesc sst b with
             | SGo s' u1 u2 out => (s' =? sstj) && Nat.eqb (length out) (if text_loop then 1%nat else 0%nat) &&
                                   upd_ok (BV i) (CPX i) 58 u1 b (sub s 58) sstj && upd_ok (BV i) (CP2X i) 59 u2 b (sub s 59) sstj
             | SU4 d => match hexclass b with
                        | Some q => b85 i && (sstj =? SS_SP1) && (d =? b - clsk q) && match lit cells (fe_hs (A4 q)) with Some true => true | _ => false end &&
                                    oeqb (CPX i) (V 58) && expr_eqb (sub s 58) (A4 q) && keep_ok (CP2X i) 59 (sub s 59) sstj
                        | None => false end
             | SU8 d => (* [comment removed for export] *)
                        b85 i && match hexclass b with Some q => match reg8 cells q with Some r => negb (region_eqb r R4) | None => false end | None => false end
             | _ => false
             end)
        then LOk else LBad 3
      else LBad 4
  | _, _, _ => LBad 5
  end%bool.
(* [comment removed for export] *)
Definition push_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 : expr) : lres :=
  let f := famof i in
  match ki with
  | KStep sst c =>
      if negb (someb adm && hasb cells c (BV i)) then LBad 10 else
      if sst =? SS_ESC then
        if allb adm (fun b => match sdesc sst b with SGo s' UKeep UKeep [o] => (s' =? SS_TEXT) && expr_eqb a1 (ELit o) | _ => false end)%bool
        then LPost (KStep SS_TEXT (c + 1)) else LBad 11
      else if sst =? SS_U4 then
        if b85 i && allb adm (fun b => match sdesc sst b, hexclass b with
             | SU4 d, Some q => (d =? b - clsk q) && match lit cells (fe_hs (A4 q)) with Some false => true | _ => false end &&
                               oeqb (CPX i) (V 58) && oeqb (cellv cells 148 4) (A4 q) &&
                               match reg4 cells q with Some r => Nat.ltb 0 (klen r) && vshape_ok (H4 q) r 0 a1 | None => false end
             | _, _ => false end)%bool
        then LPost (KPush false 1 c) else LBad 12
      else if sst =? SS_U8 then
        (* [comment removed for export] *)
        if b85 i && allb adm (fun b => match hexclass b with Some q => match reg8 cells q with Some r => negb (region_eqb r R4) | None => false end | None => false end)
        then LPost KDead
        else if b85 i && allb adm (fun b => match sdesc sst b, hexclass b with
             | SU8 d, Some q => (d =? b - clsk q) && oeqb (CPX i) (V 58) && oeqb (CP2X i) (V 59) && oeqb (cellv cells 152 4) (hex_form q (V 59) (V 111)) &&
                               match reg8 cells q with Some R4 => vshape_ok (H8 q) R4 0 a1 | _ => false end
             | _, _ => false end)%bool
        then LPost (KPush true 1 c) else LBad 13
      else LBad 14
  | KPush u8 m c =>
      if negb (someb adm && hasb cells c (BV i) && b85 i) then LBad 15 else
      if allb adm (fun b => match hexclass b with
           | Some q => match (if u8 then reg8 cells q else reg4 cells q) with Some r => (if u8 then region_eqb r R4 else true) && Nat.ltb m (klen r) && vshape_ok (if u8 then H8 q else H4 q) r m a1 | None => false end
           | None => false end)%bool
      then LPost (KPush u8 (S m) c) else LBad 16
  | _ => LBad 17
  end.
(* [comment removed for export] *)
Definition app_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 a2 : expr) : lres :=
  match ki with
  | KText =>
      if negb (expr_eqb a1 RUNS) then LBad 20 else
      if expr_eqb a2 RUNL then
        (if someb adm && hasb cells 0 (BV i) && allb adm (fun b => b =? 92) then LPost (KStep SS_ESC 1)
         else if someb adm && hasb cells 0 (BV i) && allb adm (fun b => b =? 34) then LPost (KStep SS_TEXT 0)
         else LBad 21)
      else if expr_eqb a2 RUNL1 then
        (if someb adm && hasb cells 0 (BV i) && allb adm (fun b => match sdesc SS_TEXT b with SGo s' UKeep UKeep [o] => (s' =? SS_TEXT) && (o =? b) | _ => false end) && exh_fact cells 1
         then LPost (KStep SS_TEXT 1) else LBad 22)
      else LBad 23
  | KStep sst c => if (sst =? SS_TEXT) && expr_eqb a2 (ELit 0) && exh_fact cells c then LPost (KStep SS_TEXT c) else LBad 24
  | _ => LBad 25
  end%bool.
(* [comment removed for export] *)
Definition setec_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 : expr) : lres :=
  match ki, a1 with
  | KStep sst c, ELit code =>
      if negb (code =? 0) && someb adm && hasb cells c (BV i) && allb adm (fun b => match sdesc sst b with SErr e => e =? code | _ => false end) then LPost (KSetEc code) else LBad 30
  | KText, ELit code =>
      if negb (code =? 0) && someb adm && hasb cells 0 (BV i) && allb adm (fun b => match sdesc SS_TEXT b with SErr e => e =? code | _ => false end) then LPost (KSetEc code) else LBad 31
  | _, _ => LBad 32
  end%bool.
(* [comment removed for export] *)
Definition esv_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (a1 a2 : expr) : lres :=
  match ki with
  | KText => if someb adm && hasb cells 0 (BV i) && allb adm (fun b => b =? 34) && expr_eqb a1 RUNS && expr_eqb a2 RUNL && hasr cells (V 55) 0 0 then LPost KEsv else LBad 40
  | KStep sst c => if (sst =? SS_TEXT) && (c =? 0) && someb adm && hasb cells c (BV i) && allb adm (fun b => b =? 34) && oeqb (PTRX i) a1 && oeqb (SIZX i) a2 then LPost KEsv else LBad 41
  | _ => LBad 42
  end%bool.
(* [comment removed for export] *)
Definition exit_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) : lres :=
  let f := famof i in
  match ki with
  | KEntry => match cellv cells 209 1 with Some (ELit s) => if hasr cells (V 41) s s then LOk else LBad 50 | _ => LBad 51 end
  | KStep sst c =>
      if exh_fact cells c then
        (if oeqb (cellv cells 209 1) (ELit sst) && keep_ok (CPX i) 58 (match cellv cells 148 4 with Some e => e | None => ELit (-1) end) sst &&
            keep_ok (CP2X i) 59 (match cellv cells 152 4 with Some e => e | None => ELit (-1) end) sst &&
            tag_ok i (match cellv cells 220 1 with Some e => e | None => ELit (-1) end) then LOk else LBad 52)
      else if (sst =? SS_U4) && lt_fact cells c && oeqb (cellv cells 209 1) (ELit 0) && someb adm && hasb cells c (BV i) && b85 i &&
              allb adm (fun b => match sdesc sst b, hexclass b with
                | SU4 d, Some q => (d =? b - clsk q) && match lit cells (fe_hs (A4 q)), lit cells (fe_surr (H4 q)) with Some false, Some true => true | _, _ => false end &&
                                  oeqb (cellv cells 148 4) (A4 q)
                | _, _ => false end) then LOk
      else LBad 53
  | KPush false m c =>
      if oeqb (cellv cells 209 1) (ELit 0) && someb adm && hasb cells c (BV i) && b85 i &&
         allb adm (fun b => match hexclass b with Some q => match reg4 cells q with Some r => Nat.eqb m (klen r) && oeqb (cellv cells 148 4) (A4 q) | None => false end | None => false end)
      then LOk else LBad 54
  | KSetEc code => if negb (code =? 0) then LOk else LBad 55
  | KEsv => LOk
  | _ => LBad 56
  end%bool.
(* [comment removed for export] *)
Definition goto_other_chk (i : nat) (ki : ckind) (cells : list kentry) (adm : list Z) (j : nat) (s : CC.subst) : lres :=
  match ki with
  | KEntry =>
      if expr_eqb (sub s 53) (V 32) && hasr cells (V 41) (DSST j) (DSST j) && Nat.leb 1 j && Nat.leb j 13 &&
         expr_eqb (sub s 58) (V 44) && expr_eqb (sub s 59) (V 45) && expr_eqb (sub s 60) (V 47) && expr_eqb (sub s 55) (V 35) && expr_eqb (sub s 56) (V 36) &&
         (negb (Nat.eqb j 1) || expr_eqb (sub s 62) (ELit 0)) then LOk else LBad 60
  | KPush true m c =>
      if Nat.eqb j 2 && expr_eqb (sub s 53) JM1 && someb adm && hasb cells c (BV i) && b85 i &&
         allb adm (fun b => match hexclass b with Some q => match reg8 cells q with Some R4 => Nat.eqb m 4 | _ => false end | None => false end) &&
         tag_ok i (sub s 60) && buf_ok i (sub s 55) (sub s 56) then LOk else LBad 61
  | KDead => LOk
  | _ => LBad 62
  end%bool.
Definition leaf_eval (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : lres := ltac2:(Rpl.RP.run_i (rplG ()) 5 "SF0!6'`F#;#4#6#3#2#1!2'N#1'`H!2'N#1'`J};!1,I,O!4'1+:3#44!2'N#1'`L}<!4'1+:7#44!2'N#1'`N!2'N#1'`P!1,`R}^I-`ARN$t;R+`A+`E#52$j;R+0$s;R'`:-_9RN$ki;R+_9+`E#480$sst;R+L$c;R+L!7'`G#=#2#1#8#5#4#3!7'`G#;,O,O#6#3#2#1$u8;R+M$m;R+0$c0;R+L!6'`F#>#7#9#6#5#4$code;R+L!6'`F#<#5#7#4#3#2000$pc;R+L-MRN$~R+M+`E12!4'`I#:#3#5#2-MRN$~R+M+`E22!5'`K#:#3#5#25-MRN$~R+M+`E62!6'`M#:#3#5#258-MRN$~R+M+`E92!5'`O#:#3#5#25-MRN$~R+M+`E:2!6'`Q#:#3#5#258;!6'`F#=#6#8#5#2#1!4'1+:3#64!4'1+:7#64!6'`F#>#7#9#6#2#1!4'1+:3#74!4'1+:7#74!6'`F#<#5#7#4#2#1!4'1+:3#54!4'1+:7#54$i;R+0$c;R+2$k;R+0$ps;R+`@$t;R+`A&cells;R!1'`B#2!1+X+Y&regs;R!1'`C#3!1+X+:&ki;R!1/K;#7+_9&adm;R!2'`D#3!1'`?#8!1+X+L-_9RN$ki;R+_9+`E#28<$sst;R+L$c0;R+L-`ARN$t;R+`A+`E#72$j;R+0$s;R'`:-_9RN$ki;R+_9+`E#68=$sst;R+L$c;R+L!7'`G#?#2#1#:#7#4#3!7'`G#=,O,O#8#5#2#1$u8;R+M$m;R+0$c0;R+L!6'`F#@#9#;#8#5#4$code;R+L!6'`F#>#7#9#6#3#2===$pc;R+L-MRN$~R+M+`E12!4'`I#<#5#7#4-MRN$~R+M+`E22!5'`K#<#5#7#4>-MRN$~R+M+`E62!6'`M#<#5#7#4>?-MRN$~R+M+`E92!5'`O#<#5#7#4>-MRN$~R+M+`E:2!6'`Q#<#5#7#4>?;<$u8;R+M$m;R+0$c0;R+L-`ARN$t;R+`A+`E#82$j;R+0$s;R'`:-_9RN$ki;R+_9+`E#78@$sst;R+L$c;R+L!7'`G#@#2#1#;#8#4#3!7'`G#>,O,O#9#6#2#1$u8;R+M$m;R+0$c0;R+L!6'`F#A#:#<#9#5#4$code;R+L!6'`F#?#8#:#7#3#2@@@$pc;R+L-MRN$~R+M+`E12!4'`I#=#6#8#5-MRN$~R+M+`E22!5'`K#=#6#8#5A-MRN$~R+M+`E62!6'`M#=#6#8#5AB-MRN$~R+M+`E92!5'`O#=#6#8#5A-MRN$~R+M+`E:2!6'`Q#=#6#8#5AB;$code;R+L-`ARN$t;R+`A+`E#62$j;R+0$s;R'`:-_9RN$ki;R+_9+`E#58C$sst;R+L$c;R+L!7'`G#>#2#1#9#6#4#3!7'`G#<,O,O#7#4#2#1$u8;R+M$m;R+0$c0;R+L!6'`F#?#8#:#7#5#4$code;R+L!6'`F#=#6#8#5#3#2CCC$pc;R+L-MRN$~R+M+`E12!4'`I#;#4#6#3-MRN$~R+M+`E22!5'`K#;#4#6#3D-MRN$~R+M+`E62!6'`M#;#4#6#3DE-MRN$~R+M+`E92!5'`O#;#4#6#3D-MRN$~R+M+`E:2!6'`Q#;#4#6#3DE;<-`ARN$t;R+`A+`E#52$j;R+0$s;R'`:,`S$pc;R+L-MRN$~R+M+`E12,`S!1,`T,_I<").
End Leaf.

(* [comment removed for export] *)
Definition decl_kind (j : nat) : ckind := if Nat.eqb j 0 then KEntry else if Nat.eqb j 1 then KText else KStep (DSST j) 0.
Definition post_of (K : nat -> ckind) (i k : nat) : ckind := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$K;R%~R+0+_9$i;R+0$k;R+0&c;R!1'`U#2+2-URN$x;R!1+U+`@+_9!3'`V+`@!1'`W#1#22$ps;R+`@-URN$x;R!1+U+`A+_9!3'`V+`A!4'1!1+X+`A#4'`X!1,_S+`A#32$t;R+`A-`ERN$x;R+`E+_9!6'`Y#6#5#3#4#2#13$why;R+0,_J,_J$kd;R+_9#1,_J,_J").
Fixpoint build (n : nat) (acc : list ckind) : list ckind :=
  match n with
  | O => acc
  | S n' => let j := length acc in
            let kd := if Nat.leb j 13 then decl_kind j else match parent j with Some (i, k) => post_of (fun x => nth x acc KBad) i k | None => KBad end in
            build n' (acc ++ [kd])
  end.
(* [comment removed for export] *)
Definition KTAB : list ckind := [KEntry; KText; KStep 0 0; KStep 1 0; KStep 2 0; KStep 3 0; KStep 4 0; KStep 5 0; KStep 6 0; KStep 7 0; KStep 8 0; KStep 9 0; KStep 10 0; KStep 11 0; KStep 1 1; KStep 0 1; KEsv; KStep 0 0; KStep 0 1; KSetEc 13; KSetEc 7; KStep 0 0; KStep 0 1; KStep 0 1; KSetEc 14; KStep 0 1; KStep 0 1; KSetEc 14; KStep 0 1; KStep 0 1; KSetEc 14; KStep 0 1; KStep 0 1; KSetEc 14; KSetEc 17; KSetEc 17; KSetEc 17; KSetEc 17; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KPush false 1 0; KSetEc 15; KSetEc 15; KSetEc 17; KSetEc 17; KSetEc 17; KSetEc 17; KDead; KDead; KDead; KDead; KPush true 1 0; KDead; KDead; KDead; KDead; KPush true 1 0; KDead; KDead; KDead; KDead; KPush true 1 0; KEsv; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KPush false 2 0; KDead; KDead; KDead; KPush true 2 0; KDead; KDead; KDead; KPush true 2 0; KDead; KDead; KDead; KPush true 2 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KPush false 3 0; KDead; KDead; KPush true 3 0; KDead; KDead; KPush true 3 0; KDead; KDead; KPush true 3 0; KPush false 4 0; KPush false 4 0; KPush false 4 0; KPush true 4 0; KPush true 4 0; KPush true 4 0].
Definition KD (i : nat) : ckind := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$i;R+0!4'1+_9#1'`Z,_J").
(* [comment removed for export] *)
Definition wl_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match leaf_eval KD i c k ps t with
  | LBad _ => false
  | LOk => match t with CC.TGoto j _ => (Nat.leb 1 j && Nat.leb j 13)%bool | _ => true end      (* [comment removed for export] *)
  | LPost kd => match t with CC.TOther _ => match CH2.ret_of G.RETS i k with Some j => ckind_eqb (KD j) kd | None => false end | _ => false end
  end.
Lemma KTAB_ok : build (length G.CPS) [] = KTAB.
Proof. vm_compute. reflexivity.
Qed.
Lemma wl_ok : CH2.leaves_all G.CPS G.TAGS wl_chk = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,_>+M,G!3+_;+M!3'a0'3'`X'a1,G").
Qed.
End PSCW.
