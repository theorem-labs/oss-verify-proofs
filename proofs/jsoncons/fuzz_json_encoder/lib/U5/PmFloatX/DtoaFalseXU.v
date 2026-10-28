(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncPure_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import FxKitX_u5 DumpBufX_u5 FxKitXU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_df_xsrc_T_u5 Cut_df_xsrc_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Zpos]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EVar]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Corelib; @Init; @Logic; @eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @heap_chk3]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @GT; @NF]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @HDECL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @BLS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @CPS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @TAGS]; [@Corelib; @Init; @Logic; @ex_intro]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Datatypes; @option]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@OssFuzzTheorems; @jsoncons; @fuzz_json_encoder; @images; @Ubsan; @M; @loaded_segments]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @RETPC]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Corelib; @Numbers; @BinNums; @xH]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Decode; @f_rd]; [@LinuxProcessSemantics; @Riscv; @Decode; @f_rs1]; [@LinuxProcessSemantics; @Riscv; @Decode; @imm_i]; [@Corelib; @Init; @Logic; @conj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @is_ret_at]; [@Corelib; @Init; @Datatypes; @nat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ret_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @RETS]; [@Corelib; @Init; @Datatypes; @O]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cutpoint]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @post_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @blocks]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reglist]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Nat; @sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @NCS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @cinfo]; [@Corelib; @Init; @Datatypes; @andb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@Corelib; @Lists; @ListDef; @nth]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @BUFE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @XCE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @has_cell]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_cells]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @custom_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @DEC_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @ERRNO]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@Corelib; @Init; @Nat; @add]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KUnk]; [@Corelib; @Init; @Datatypes; @None]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @strans_chkN]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @S2E]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @DB_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @ret_cut]; [@Corelib; @Init; @Datatypes; @negb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@Stdlib; @Lists; @List; @nth_error]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @isSome]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @inlF_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @LV]; [@Corelib; @Init; @Datatypes; @S]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @tag]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmSmall; @SmallPure; @SP; @F_sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_F]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @F0]; [@Corelib; @Init; @Datatypes; @orb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @F1]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @needs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @subst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @kind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_STR_PUSH_BACK]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @sinkj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @pushb_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @PC_SNPRINTF]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @snp_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_DECSTR_DOUBLE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @dec_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @PC_DUMP_BUFFER]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @db_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @fp_site]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @inlj]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @exit_base_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @leaf_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DumpBufX_u5; @DBX; @uv_lit1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @env]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ev]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSound; @APS; @ext_list]; [@Corelib; @Lists; @ListDef; @map]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @caller_saved]; [@Corelib; @Init; @Logic; @I]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSound; @APS; @ext_list_at]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Datatypes; @length]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add_0_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hdecl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @common_chk_x]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @regs_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_regs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sr_upd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sr_fresh]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_regs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_nx]; [@Stdlib; @Lists; @List; @forallb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blk_in]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @kept_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @ci_csp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_know]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @Init; @Logic; @eq_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @split_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @foot_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @all_regs_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sr_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @kn_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_pc]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_meas]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @esub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @MB]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @expr_vars_lt]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_scr]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @CI]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @False_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @TXT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @uv]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @agree_on]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@Corelib; @Init; @Logic; @ex_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @gtext]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @len]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @bytes_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @u8]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@Corelib; @Init; @Logic; @and_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @bytes_at_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @agree_sub]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @u8_agree]; [@Stdlib; @Lists; @List; @Forall_forall]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hi_heap]; [@Corelib; @Init; @Datatypes; @app]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep_blocks]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vmmaps]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @model_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @fp_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @entry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXTu_u5; @PMFXT; @DF_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @STRTOD_SCR_V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a1]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @u64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_sptop]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @apart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @sink_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @obj_on_stack]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @img_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @scredit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @srep_chars]; [@Corelib; @Init; @Datatypes; @snd]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @regs_preserved]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @hpres]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @model_but_vm]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @SCFG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @cfg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @PC_DTOA_FALSE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @ra_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @TP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @stk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_segs]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_segs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_img_lo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_lo]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_img_hi]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_img_hi]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_errno]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_errno]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @Env]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @reg_ev]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @ev_reg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ridx]; [@Corelib; @Classes; @Morphisms; @trans_sym_co_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @Equivalence_PER]; [@Corelib; @Classes; @RelationClasses; @eq_equivalence]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibSym; @u64_of_Z]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_tp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_tp]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Logic; @or_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @in_rng]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @wclient]; [@Corelib; @Init; @Logic; @not]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_static]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hl_alloc_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_errno]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Corelib; @Init; @Logic; @or_introl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_crs]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @in_reg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @sclient]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_wrs]; [@Corelib; @Init; @Datatypes; @fst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap; @CH; @hd_img]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_static]; [@Stdlib; @micromega; @Tauto; @NOT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @edenot]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_base]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_off]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @estart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @sghost]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @sink_inv]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @phase]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @s_len]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @text]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @CredV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @gB]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @s_rep]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymRun3; @env_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_trans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @NF_le]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @mem]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @heap_ambV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @model_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @cur]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @LBr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @kept]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @client0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @block_range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @den]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @hio_wf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@stdpp; @base; @NoDup]; [@Stdlib; @Lists; @List; @in_or_app]; [@Corelib; @Init; @Logic; @or_intror]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @IMG_RO_HI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @kept_static]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @outside]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @client_addr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV_def0]; [@Corelib; @Lists; @ListDef; @Forall]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @elenZ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmSmall; @SmallPure; @SP; @F_sub_in]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @estart_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @unsigned_lit]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @outside]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @sink_at_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @SShort]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @SLong]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @is_leaf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @At]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @leaf_facts]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all_sound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @leaf_ok]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_PSS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_frame]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_grows]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncKit_u5; @EK; @img_ro_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @DtoaFalseOk; @TXT_agree]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @uv_agree]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @know_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @kentry_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @lf_cells]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @cp0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @cert_sound3V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @LYI_]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @LYE_]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_ro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @plan_sound]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @plans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @G; @tags_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @heap_ok3]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TGoto]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_over]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @TOther]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @leaf_okV]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb_le]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @pushb_leaf_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3XV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @IH]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3V]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @meas]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @FMT_G]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @SNP_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @expr_eqb_eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @custom_chk_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncPure_u5; @EPU; @pure_leaf_okV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @common_facts_x]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @frame_but]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncPure_u5; @EPU; @wfree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @heap_amb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @regs_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @eb]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sr_get]; [@stdpp; @tactics; @f_equal_help]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @u_lin]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_of]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @uE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @tden]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @lden]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@Corelib; @Init; @Logic; @eq_sym]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @uv_range]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @uv]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_materialized]; [@Corelib; @Init; @Logic; @proj2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXSpecs_u5; @PMFX; @SNPRINTF_SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @a3]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @regs_preserved_kept]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @alloc_private]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Program; @Basics; @flip]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @flip2]; [@Corelib; @Classes; @Morphisms; @iff_flip_impl_subrelation]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Stdlib; @ZArith; @BinInt; @Z; @Proper_instance_0]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @retEx0_a0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kunk_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @retEx_agree]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLayout_u5; @PmLayout; @ly_ro_img]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@Corelib; @Init; @Datatypes; @comparison]; [@Corelib; @Init; @Datatypes; @Eq]; [@Corelib; @Init; @Datatypes; @Gt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_sub64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @u_sltu64]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @retEx0_a1]; [@Stdlib; @micromega; @ZifyClasses; @not_morph]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @strans_leaf_okN]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kword64_elim]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @has_ok]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXTu_u5; @PMFXT; @rd_buf]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXTu_u5; @PMFXT; @len]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXTu_u5; @PMFXT; @DB_SCR]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @fp_site_step]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @inlF_step]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @FxKitX_u5; @FXK; @inl_leaf_okV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @exit_ret]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatX; @DtoaFalseXU; @DFXU; @ret_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @hpres_rebase]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutLib; @CL; @ps_reg_is_sound]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@Stdlib; @micromega; @Tauto; @EQ]; [@Stdlib; @micromega; @Tauto; @isBool]; [@Stdlib; @micromega; @Tauto; @TT]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @ridx_roundtrip]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3Sound; @AX2S; @ridx_range]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KAlign]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KDisj]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kword64_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @krange_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kalign_intro]; [@Stdlib; @ZArith; @BinInt; @Z; @mul_1_l]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kwr_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @elen_lin]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined_sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutL5; @CL5; @kdisj_intro]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @CP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @PS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @region]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @amb3V_intro]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEnc; @EncSinkBridges_u5; @ESB; @SG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2V; @CH2V; @okV_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Core; @L5C; @model_but_vm_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @env_agree_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @cps_heap]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmEncSpecs_u5; @PMES; @strans]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmFloatXTu_u5; @PMFXT; @dtoa_false_x_spec]].

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFXU.
Import PMES.
Module G := Cut_df_xsrc_u5.
Module GT := Cut_df_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,0|B058c4;").
Definition S2E : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,1}P").
Definition F0 : list SGP.region := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S50!2+3+4+5!2+30+4!1,1}2|=03f0;|30;!3,21!4,60+4!4,6+4+52!1,73!1,8!1,03!3,21!4,60+4!4,6+4+52!1,7|720;!1,8!1,04!1,91").
Definition F1 : list SGP.region := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+3+4+5!2+30+4!3,21!4,60+4!4,6+4+5!1,1}2!1,7|720;!1,8!1,0|30;!1,91").      (* [comment removed for export] *)
Definition BUFE : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-148)).      (* [comment removed for export] *)
Definition XCE : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-160)).       (* [comment removed for export] *)
Definition ERRNO : Z := 0xdcf6c.
Definition SNP_SCR : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,0|<800;").  Definition DEC_SCR : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,0|=0350;").  Definition DB_SCR : Z := 112 + PMFXT.STRX_SCR.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,:+;,<!3+=+;!5'>'?'@'A'B'C,<").
Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SU0|500;!1,F0!1+E1!1,F|21;!1+E3!1,F|34;!1+E5!1+I2|600;!2'J'K!2'L!1,F8'M!2+3+Q+5!1+I:|20;!1,0<!2,N:!4,6+Q+5!3,S#3#2#1=!1,0,V!3+=+5!2'T5#1,U!2+H!3+=+5!2'T3#2?@!2+H!3+=+5!2'T3#3,UA!1,0|?0067;!3,W1C!2'X1C!2,N2D!3+=79E!3+=+;!1'OD,P!1'RD!1'YD!3+=+5!2'T3I,U!1'ZD!3+=+5!2'T3K?!1'[D!2,N:!4,6+Q+5!3,SIKM=!3+=;HN!3+=+5!2'T5M,U!2+HLP!2+HJQ!2+HOR!2,:+5,Uvd!4,D2$w;R2!2+G4$rd;R4!2+G4$rs1;R4!2+G6$imm;R6!2+H!3+=79!2,N2#4!2+H!3+=+;!1'O#4,P!2+H!3+=;!1'R#4>BD!4,D4$rd;R4!2+G4$rs1;R4!2+G6$imm;R6!2+HF!2+HG!2+H!3+=;H>BI!4,D4$rs1;R4!2+G6$imm;R6!2+HF!2+HG!2+H!3+=;H!2,N:!4,6+Q+5!3,SI#2#1=!2+HJAK!4,D6$imm;R6!2+HF!2+HG!2+H!3+=;H!2,N:!4,6+Q+5!3,SIK#1=!2+HJ!2+HL@M!4,\F!2+HGSvv!2,:7EF!4,\GS!2,:+;,P!4,\OR!2,:;N!4,\JQT!4,\LP!2,:+5?T!2'^0'K'M").
Qed.

Definition isSome {A} (o : option A) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S01<scd;$A;R{cd;$o;R!1+I#1-IRN$o;R!1+I#2+;#12$a;R#2,<,P").
Definition ret_cut (i k : nat) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$i;R+^1$k;R+^1-IRN$x;R!1+I+^1+^1!3'^2'^3#2#12$j;R+^1#1,^4").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LV (i : nat) : nat := match i with 3%nat | 5%nat | 8%nat => 55%nat | 11%nat => 88%nat | _ => 0%nat end.
(* [comment removed for export] *)
Definition snp_chk (lvj : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let nx := (CC.cp_nx cj - APC.NCS)%nat in
  if (Nat.eqb (nx + 4) lvj && CH2.blocks_eqb BLj BLi && expr_eqb (nth 10 regs (ELit 0)) BUFE && expr_eqb (nth 11 regs (ELit 0)) (ELit 100) && expr_eqb (nth 12 regs (ELit 0)) (ELit PMFX.FMT_G) &&
      (expr_eqb (nth 13 regs (ELit 0)) (ELit 15) || expr_eqb (nth 13 regs (ELit 0)) (ELit 17)) && expr_eqb (nth 14 regs (ELit 0)) (EVar 48) && expr_eqb (nth 2 regs (ELit 0)) XCE)%bool
  then CH2.custom_chk GT.NF G.HDECL SNP_SCR 0 BLi [(EVar 2, -148, ELit 100)] [KRange (EVar (nx + 4)) 1 25; KUnk (SA (EVar 2) (-148)) (ELit 100)] None c ps cj BLi
  else None.
Definition dec_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S@0}:!1,8,U};}<}2!1,14!1,7|720;!2,^G56}8!2+3+4+5!2+39+4|30;!1,8!1,0;|20;}5!1,1!2'^P#1>$c;R+^5$ps;R+^6$cj;R+^5$BLi;R'^7$BLj;R'^7&regs;R!1'^8#4!1+^9+4&nx;R!2'^:!1'^;#4'^<+^1-;RN$~R+;!1+I+^=!2'^>!2'^>!2'^>!2'^>!2'^>!2'^?#3#4!2'^@!4'^A+40#21'^B!2'^@!4'^A+42#21!1,1}^:!2'^@!4'^A+43#21'^C!2'^@!4'^A+44#21'^C!2'^D!1'^E#6!3,^F7812!<'^H'?'@'^I,^4#4!3,2:!4,69+4!4,6+4+556<!3,2:!4,69+4!4,6+4+51'^J!1,8!1,0=!1,9:!3,2+^K!3,^L!3,^M,^N!3,^M,^O?!1,8!1,0|46;!1,8!1,0,V,U,U!3,2+^K!3,^L?,U!1,0|502;!3,2+^K!2,^Q7<!1,9+^K!1,^R+4#7#6#5#4!1,^R+^=").
Definition db_chk (lv : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S80}:!1,8,U};}<}=!1,12}2}8$lv;R+^1$c;R+^5$ps;R+^6$cj;R+^5$BLi;R'^7$BLj;R'^7&regs;R!1'^8#4!1+^9+4-;RN$~R+;!1+I+^=!2'^>!2'^>!2'^>!2'^>!2'^>!2'^@!4'^A+40#11'^B!2'^@!4'^A+42#11!1,1#7!2'^@!4'^A+43#11!1,10!2'^@!4'^A+44#115!2'^@!4'^A+46#11'^C!2'^D!1'^E#5!3,^F!2,^G5,U7!1,1}P2!;'^S'?'@'^T,U'^U!1,^R+5#6#5#4#3#2!1,^R+^=").
Definition sinkj (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S10!1,9!2+3+4+4$f;R%~R+^5%~R+^6%~R+^5%~R'^7%~R'^7!1+I+^=$i;R+^1$k;R+^1$c;R+^5$ps;R+^6&j;R!2'^V#4#3+^1!2'^>!1'^W!2'^X#1,^4-IRN$x;R!1+I+^5+;!3'^Y+^5'B#12$cj;R+^5!2'^Z+^=!5#7#4#3#1!4'^A'^7#6'A0!4'^A'^7#2'A0,P").
Definition inlj (i k : nat) (hv : list nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1,9!2+3+4+4!4'^A'^7#7'A0$i;R+^1$k;R+^1$hv;R!1+^9+^1$c;R+^5$ps;R+^6&j;R!2'^V#5#4+^1!2'^>!1'^W!2'^X#1,^4-IRN$x;R!1+I+^5+;!3'^Y+^5'B#12$cj;R+^5!2'^>!2'^>!6'^['?#4#3#1!1,0|20;#5!2'^?!4'^A'^7#2'A01!2'^\!1'^;#41,P").
Definition needs (i : nat) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$i;R+^1-^1RN$x;R+^1+^1!1'_0#12}^3$n;R+^1!1,_1!1,_1#1").
(* [comment removed for export] *)
Definition kind (i k : nat) : nat :=
  (match i, k with
   | 0, 0 | 2, 0 | 4, 0 | 6, 0 | 5, 0 => 1 | 4, 1 | 7, 0 | 10, 0 => 2 | 1, 0 | 8, 0 => 3 | 3, 0 => 4 | 8, 1 | 11, 0 => 5 | 12, 0 | 13, 0 | 14, 0 => 6 | 9, 0 => 7 | _, _ => 0
   end)%nat.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S@0!1'_4#5!2'_;#8#6}7}1!2'_<!1'_>#4#1!2'_;#7#5}2!1'_0!2'^V#7#5}3}4!1'_0#7}5!1+^9+^1|20;|10;}6$i;R+^1$c;R+^5$k;R+^1$ps;R+^6$t;R+_2&cells;R!1'^E#2!1+^9+^K!2'^>!2'^>!2'^>!2'_30'_5!2'_6!2'^X!1'_0#6,^4!2'_30'_7!2'_8!1'_9#6!1'^;#5-_2RN$t;R+_2+;#22$j;R+^1$s;R'_:!2'^>!2'^X12!2'^X#23$pc;R+5-;RN$~R+;+;!2'_<#1'_=2!2'^>!2'^>4!5'_?!4'_@'?'@'^T,U#7#5#6#4!2'^X56-;RN$~R+;+;!2'_<#1'_A2!2'^>!2'^>4!5'_?!1'_B7#7#5#6#4!2'^X58-;RN$~R+;+;!2'_<#1'_C2!2'^>!2'^>!2'^>4!5'_?'_D#7#5#6#4!2'^X59!2'^X7:-;RN$~R+;+;!2'_<#1'_E2!2'^>!2'^>4!5'_?!1'_F:#7#5#6#4!2'^X5;-IRN$x;R!1+I<+;!2'_G'K#12$hv;R<!2'^>!2'^>!2'^>!2'^>!2'^>!2'_<!1'_>#5#2!5'_H#8#6#1#7#5!2'^X13!2'^X!1'_0!2'^V#8#6!1'_0#8!2'_I,U#2!2'_J!2'_K#2!1,0=!2'_L!1,0>!1,0|600;!2'^>!2'^>!4'_M'?'M#6#4!3'_N#4}:!1,8!1,0,V!2'^X5?").
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,:+;,<!3+=+;!3'_O'B'C'_P,<").
Qed.

(* [comment removed for export] *)
Definition phase (i : nat) (p : Z) : Prop :=
  match i with 7%nat => p = 1 | 10%nat => p = 2 | 13%nat => p = 3 | 12%nat | 14%nat => 1 <= p <= 27 | _ => p = 0 end.

Lemma uv_lit1 : forall E z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'_Q").
Qed.
(* [comment removed for export] *)
Lemma retEx0_a0 : forall E' nx R2, ev (CH2.retEx E' nx [] R2) (nx + 4)%nat = getr R2 10%bv.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SF0|21;!1,F0!1,F|600;!1+E2!1,93!2'L1!1'_Y#1}4!1,0|32;!3,W17,_[!2'_X#28!4'_W+^13$r;R+^1!2'_X#25'_Z!4'^A36:!2'L2,U!2'_X#18!3'_V#3#24!2'^P#26}@|20;!1,0@|40;!1,0B!2'`2AC!1+`9+5$E';R+_R$nx;R+^1$R2;R!2'_S13vdvd!6'_T+^1#2$n;R+^1!3+=3!2'_U!3'_V!3'_V#4#34#1!4'_W+^13$r;R+^1!2'_X#35'_Z!2'^P#369!6'_T3;$b;R3!3+=3#19vd!2,:3<!3+=3;<!2'_U!3'_V=#2:>!5'_\=#2:6vd!4'`0!2'`16?D!<'`3+^1+5'`1'_Y'`2'`46A!2,:+5A?C!2,:+5C&__arith;R&__wit;R!1,9+`5!1+^9+`5&__varmap;R!1,`6+5!1+`7+5&__ff;R!7,`8E'`:+`;+`;,`<!4,`=+5!2,`>+5A,`?!2,`>+5C,`@!2'`AE,`<!4'`B#1#3vv!2,:+;,<!3+=+;!2'`C#1#3,<!3'`D+5,U#2D#1!2'`16!2'`E3:!2'`F#2,^4!1'`G#2!3+=3!2'_U!3'_V=!2'^P#2!2'`E34:><!3+=3!2'_U!4'`H#3#24#1>!2'_X#1!3,W17vv,_[!2'`I17").
Qed.
Lemma retEx0_a1 : forall E' nx R2, ev (CH2.retEx E' nx [] R2) (nx + 5)%nat = getr R2 11%bv.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SE0|21;!1,F0!1,F|600;!1+E2!1,93!2'L1!1'_Y#1}5!1,0|33;!3,W17,_[!2'_X#28!4'_W+^13$r;R+^1!2'_X#25'_Z!4'^A36:!2'L2,U!2'_X#18!3'_V#3#24!2'^P#26}@!1,00|40;!1,0A!2'`2@B!1+`9+5$E';R+_R$nx;R+^1$R2;R!2'_S13vdvd!6'_T+^1#2$n;R+^1!3+=3!2'_U!3'_V!3'_V#4#34#1!4'_W+^13$r;R+^1!2'_X#35'_Z!2'^P#369!6'_T3;$b;R3!3+=3#19vd!2,:3<!3+=3;<!2'_U!3'_V=#2:>!5'_\=#2:6vd!4'`0!2'`16?C!<'`3+^1+5'`1'_Y'`2'`46@!2,:+5@?B!2,:+5B&__arith;R&__wit;R!1,9+`5!1+^9+`5&__varmap;R!1,`6+5!1+`7+5&__ff;R!7,`8D'`:+`;+`;,`<!4,`=+5!2,`>+5@,`?!2,`>+5B,`@!2'`AD,`<!4'`B#1#3vv!2,:+;,<!3+=+;!2'`C#1#3,<!3'`D+5,U#2C#1!2'`16!2'`E3:!2'`F#2,^4!1'`G#2!3+=3!2'_U!3'_V=!2'^P#2!2'`E34:><!3+=3!2'_U!4'`H#3#24#1>!2'_X#1!3,W17vv,_[!2'`I17").
Qed.
Lemma custom_chk_nx : forall NF d scr ng BLk wregs news a0x c ps cj BLi ci,
  CH2.custom_chk NF d scr ng BLk wregs news a0x c ps cj BLi = Some ci -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - ng)%nat.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_E0!1+I+^=!2,N+^=#1!1'`N#9!1+^9+4!1'`Q#2!1'`R#2}:!1'`R#1!2+3+4+4!3'`S8!1'`T#8#?!2'^D#>#1!1'^E#;!1'`W#9!1,^R+^=!2,N+^=#6!3+=+^1!1'`R#7!2'^:!2'^:!1'^;#9'^<#@!1'`R#3!3'`P!1'`Q#3'_Z!2'^P@#A!1'`R#4!2,N+^=#5!2,N+^=#:!3+=+^1!1'`R#;!2'^:!2'^:!1'^;#='^<#D!2,N+^=#9}1!1,8,U}2!1'^;#F!1'^;#H!2'^:!2'^:J'^<#M!1'^8#G!1'^E#G|10;!1,0O!2'_LP!1,0|50f;}4!1,1R!1'a4#H!1,0,V!1,8U!1,0|40;!2'_<!2'a3#4W,U!2'_I#4,U-3RN$x;R!2+3+4+50!1'`Z!4'^A+4I!1'^8#BH1$e;R+4$csp;R+5-4RN$e;R+40#28$z;R+5=$n;R+^1-^1RN$n;R+^10#12=$n0;R+^1-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#P#O#H#E!1'`\#G!2'_8!2'^P'^<#MJ!2'_8KL!2'a0LM!2'a1LN!2'_<#6!1'a2#F!2'_<!2'a3#6P,U!2'_I,U#6!2'_J#6Q!2'^@!4'^A+4RMHS!2'^@!1'a4#F!2'a5TV!2'^DN!3,^LTU'a6!2'a7KTXY!2'_I,U#N!2'_I!1'a8!1'a9#O!2'a:#4#N2!2,N+^=!4,a;ML#4#6=$n2;R+^1=$op;R+a<$a;R+4$b;R+4=$op;R+a<$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$sx;R+;$lo;R+^1$n;R+^1$e0;R+4=$sx;R+;$k;R+^1$i;R+5$n;R+^1=!1'^;#I!1'^;#K!2'^:!2'^:['^<#P!1'^8#J!1'^E#J!1'a4#K!1'^;#J!1'^;#L!2'^:!2'^:^4'^<#Q!1'^8#K!1'^E#K!1'a4#L!2,N+^=#@!1'^;#N!2'^:!2'^:^5'^<#S!1'^8#M!1'^E#M!1'a4#N-^1RN$n;R+^10#12=$n0;R+^1-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#V#U#N#K!1'`\#M!2'_8!2'^P'^<#S^5!2'_8^;^<!2'a0^<^=!2'a1^<^>!2'_<#<!1'a2#L!2'_<!2'a3#<P,U!2'_I,U#<!2'_J#<Q!2'^@!4'^A+4R^=HS!2'^@^9!2'a5^?V!2'^D^>!3,^L^?U'a6!2'a7^;^?!2'_<!2'a3#6W,U!2'_I#6,U!2'_I,U#T!2'_I!1'a8!1'a9#U!2'a:#6#T2!2,N+^=!4,a;^=^<#6#<=$n2;R+^1=!2,N+^=#C-IRN$o;R!1+I+^=w#12$~R+^=+a>+a?$e;R0^B!2,N+^=#D!1'^;#P!2'^:!2'^:^;'^<#U!1'^8#O!1'^E#O!1'a4#P!2,N+^=#E!3+=+^1!1'`R#F!2'^:!2'^:!1'^;#M'^<#T!1'^;#O!1'^;#Q!2'^:!2'^:^L'^<#V!1'^8#P!1'^E#P!1'a4#Q-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#Y#X#Q#N!1'`\#P!2'_8!2'^P'^<#V^L!2'_8^M^N!2'a0^N^O!2'a1^N^P!2'_<#?!1'a2#O!2'_<!2'a3#?P,U!2'_I,U#?!2'_J#?Q!2'^@!4'^A+4R^OHS!2'^@!1'a4#O!2'a5^QV!2'^D^P!3,^L^QU'a6!2'a7^M^Q!2'_<!2'a3#9W,U!2'_I#9,U!2'_I,U#W!2'_I!1'a8!1'a9#X!2'a:#9#W2!2,N+^=!4,a;^O^N#9#?=!2,N+^=#G!3+=+^1!1'`R#H^N!1'^;#R!2'^:!2'^:^E'^<#W!1'^8#Q!1'^E#Q!1'a4#R!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#Z#Y#R#O!1'`\#Q!2'_8!2'^P'^<#W^E!2'_8^U^V!2'a0^V^W!2'a1^V^X!2'_<#@!1'a2#P!2'_<!2'a3#@P,U!2'_I,U#@!2'_J#@Q!2'^@!4'^A+4R^WHS!2'^@^I!2'a5^YV!2'^D^X!3,^L^YU'a6!2'a7^U^Y!2'_<!2'a3#:W,U!2'_I#:,U!2'_I,U#X!2'_I!1'a8!1'a9#Y!2'a:#:#X!2,N+^=#I!2'^:!2'^:^M'^<#X!2,N+^=#H!2'^:!2'^:^U'^<#Y!4,a;!1'^8#S_1#<#B!2,N+^=_2!2,N+^=#K!2'^:!2'^:!1'^;#S'^<#Z!3+=+^1!1'`R#L_5!2,N+^=#J!4,a;!1'^8#T_5#=#C!2'^:!2'^:!1'^;#T'^<#[$Hc;R!3+=0=_7&H;R!6'`Y0=^C,_[_4#1+a>!2'a@_6#1$eb1;R+4$eb2;R+4$Hc;R!3+=0=^S&H;R!6'`Y0=^C,_[_0#1+a>!2'a@!3+=+^1!1'`R#I^V#1!3$op;R+a<_;#3#2#1!3$op;R+a=_;#3#2#1$Hc;R!3+=0=^[&H;R!6'`Y0=^C,_[_7#1+a>!2'a@!3+=+^1!1'`R#K_1#1$e1;R+4$e2;R+4$Hc;R!3+=0=!2,N+^=#>&H;R!6'`Y0=^C,_[!2,N+^=#?#1+a>!2'a@!3+=+^1!1'`R#@!2'^:!2'^:!1'^;#G'^<#N#1!3$op;R+a<_?#3#2#1!3$op;R+a=_?#3#2#1!3+=0=^:!2,N+^=#A!2'a@!3+=+^1!1'`R#B^0#1$NF;R+^1$d;R+`J$scr;R+5$ng;R+^1$BLk;R'^7$wregs;R!1+^9'`K$news;R!1+^9+^K$a0x;R!1+I+4$c;R+^5$ps;R+^6$cj;R+^5$BLi;R'^7$ci;R+^=$H;R!3+=0!<'^H#=#<#;#:#9#8#7#6#5#4#3#21&o;R!8'`L#>#=#<#;#6#5#4#30&Hc;R!2,:0#1!3+=0!8'`L#?#>#=#<#7#6#5#4#1!2-IRN$o;R!1+I+^=%Hc;R!3+=0!8'`L#A#@#?#>#9#8#7#6#1%H;R!3+=0-IRN$x;R!1+I+^=0#22$ci;R+^=-;RN$~R+;0!2'^>!2'^>!2'^>!2'`M2-IRN$a0x;R!1+I+43#<2$e;R+4!3'`O!3'`P4'_Z!2'^P5#A6#1!3'`P!1'`Q#1'_Z!2'^P7#@!2'^\7#?9!3'`S+^K$X;R+^K-;RN$~R+;+;:2,<!8'`U#C;#B!1'`V#25#@#?#1<21==>?#22$c;R+^=!1$ci0;R+^=$Hc;R!3+=0!8'`L#B#A#@#?#:#9#8#71$H;R!3+=0-;RN$~R+;0!2'^>!2'^>!2'^>!2'`M2-IRN$a0x;R!1+I+43#<2$e;R+4!3'`OA6#1!3'`P4'_Z!2'^P5#@!2'^\5#?9!3'`S+^K$X;R+^K-;RN$~R+;+;:2,<!8'`U#C;#B!1'`V#3@#@#?#1<2!2,N+^=#2=!2,N+^=#7&b;R!2'^>!2'^>!2'^>!2'`M!1'`N#:-IRN$a0x;R!1+I+43#=2$e;R+4!3'`O!3'`P!1'`Q#4'_Z!2'^PB#B6#1A!2'^\@#@!3'`S8!1'`T#9#@!3'`S+^K$X;R+^K-;RN$~R+;+;!2'^D#?#12,<!8'`U#D!1'^E#<#C!1'`V#4B#A#@#1!1'`W#:+;!1-;RN$b;R+;%H;R!3+=0-;RN$~R+;0#12C=DE#12$H;R!3+=0!2,N+^=#4F&H0;R!6'`X0+^=$e;R0-IRN$o;R!1+I+^=+^=#12$c;R+^=#1#6CD#1!3+=+^=#5#:!1$H;R!3+=+^=#6#;!6'`Y+^=#7$ci;R+^=!3+=+^17!2'^:!2'^:!1'^;#?'^<#F&e;R!4'^A+4G!1'^8#?H+4!1-4RN$e;R+4%Hc;R!3+=0-4RN$x;R+40#18$ra;R+5Z$n;R+^1=$op;R+a<$a;R+4$b;R+4=$op;R+a<$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$sx;R+;$lo;R+^1$n;R+^1$e;R+4=$sx;R+;$k;R+^1$i;R+5$n;R+^1=F!3+=+^1!1'`R#:!2'^:!2'^:!1'^;#A'^<#H#18$z;R+5!1$z;R+5$Hc;R!3+=0ZD&p;R!1'`Z!4'^A+4I!1'^8#CH!2+3+4+5!1-3RN$p;R!2+3+4+5%Hc;R!3+=0-3RN$x;R!2+3+4+50#11$e;R+4$csp;R+5-4RN$e;R+40#28$z;R+5=$n;R+^1-^1RN$n;R+^10#12=$n0;R+^1-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#S#R#K#H!1'`\#J!2'_8!2'^P'^<#P[!2'_8\^0!2'a0^0^1!2'a1^0^2!2'_<#9!1'a2#I!2'_<!2'a3#9P,U!2'_I,U#9!2'_J#9Q!2'^@!4'^A+4R^1HS!2'^@!1'a4#I!2'a5^3V!2'^D^2!3,^L^3U'a6!2'a7\^3XY!2'_I,U#Q!2'_I!1'a8!1'a9#R!2'a:#4#Q2!2,N+^=!4,a;^1^0#4#9=$n2;R+^1=$op;R+a<$a;R+4$b;R+4=$op;R+a<$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$sx;R+;$lo;R+^1$n;R+^1$e0;R+4=$sx;R+;$k;R+^1$i;R+5$n;R+^1=!2,N+^=#=!3+=+^1!1'`R#>!2'^:!2'^:!1'^;#E'^<#L#11$e;R+4$z;R+5!2$eb;R+4$csp;R+5$Hc;R!3+=0-4RN$e;R+40#28$z;R+5=$n;R+^1-^1RN$n;R+^10#12=$n0;R+^1-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#T#S#L#I!1'`\#K!2'_8!2'^P'^<#Q^4!2'_8^5^6!2'a0^6^7!2'a1^6^8!2'_<#:!1'a2#J!2'_<!2'a3#:P,U!2'_I,U#:!2'_J#:Q!2'^@!4'^A+4R^7HS!2'^@!1'a4#J!2'a5^9V!2'^D^8!3,^L^9U'a6!2'a7^5^9XY!2'_I,U#R!2'_I!1'a8!1'a9#S!2'a:#4#R2!2,N+^=!4,a;^7^6#4#:=$n2;R+^1=$op;R+a<$a;R+4$b;R+4=$op;R+a<$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$sx;R+;$lo;R+^1$n;R+^1$e0;R+4=$sx;R+;$k;R+^1$i;R+5$n;R+^1=^:!1-4RN$e;R+4%Hc;R!3+=0-4RN$e;R+40#18$z;R+5=$n;R+^1^@$op;R+a<$a;R+4$b;R+4=$op;R+a<$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$op;R+a=$a;R+4$b;R+4=$sx;R+;$lo;R+^1$n;R+^1$e0;R+4=$sx;R+;$k;R+^1$i;R+5$n;R+^1=!2,N+^=#B!3+=+^1!1'`R#C^6#38$z;R+5!1$z0;R+5$Hc;R!3+=0=^A&H;R!6'`Y0=^C,_[^D#1+a>!2'a@!3+=+^1!1'`R#E^<#1#1$n;R+^1!1$n;R+^1$Hc;R!3+=0^@^A!1-^1RN$n;R+^1%Hc;R!3+=0-^1RN$n;R+^10#12=$n0;R+^1-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12-;RN$~R+;0!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!2'^>!4'`[#X#W#P#M!1'`\#O!2'_8!2'^P'^<#U^;!2'_8^E^F!2'a0^F^G!2'a1^F^H!2'_<#>!1'a2#N!2'_<!2'a3#>P,U!2'_I,U#>!2'_J#>Q!2'^@!4'^A+4R^GHS!2'^@^?!2'a5^IV!2'^D^H!3,^L^IU'a6!2'a7^E^I!2'_<!2'a3#8W,U!2'_I#8,U!2'_I,U#V!2'_I!1'a8!1'a9#W!2'a:#8#V2!2,N+^=!4,a;^G^F#8#>=$n2;R+^1=^J^K#22$Hc;R!3+=0=^D&H;R!6'`Y0=^C,_[^J#1+a>!2'a@^K#1$n;R+^1!1$n0;R+^1-^1RN$n;R+^1%Hc;R!3+=0-^1RN$n0;R+^10#12=$n1;R+^1-^1RN$n1;R+^10#12^R$n2;R+^1=^S^T#12$Hc;R!3+=0=!2,N+^=#F&H;R!6'`Y0=^C,_[^S#1+a>!2'a@^T#1$n;R+^1!1$n0;R+^1-^1RN$n;R+^1%Hc;R!3+=0-^1RN$n1;R+^10#12-;RN$~R+;0^Z2!2,N+^=!4,a;^W^V#:#@=$n2;R+^1=^[!3+=+^1!1'`R#J^\#12$Hc;R!3+=0^R_0&b;R^Z+;!1-;RN$b;R+;%Hc;R!3+=0-;RN$~R+;0#12_3=_4_6#12$Hc;R!3+=0!2,N+^=!4,a;!1'^8#R^\#;#A_7&H;R!6'`X0+^=$e;R0-IRN$o;R!1+I+^=+^=#12$c;R+^=#1_8_3_4#1!3+=+^=_2#K!1$H;R!3+=+^=_8#L!6'`Y+^=!4,a;!1'^8#U_9#>#D$ci0;R+^=!3+=+^17!2'^:!2'^:!1'^;#U'^<#\!2,:+^1_9#M#1#1_:#2$n;R+^1!1$n;R+^1_:#1#1#1#1#1$op;R+a<$a;R+4$b;R+4_<$op;R+a<$a;R+4$b;R+4_<$op;R+a=$a;R+4$b;R+4_=$op;R+a=$a;R+4$b;R+4_=$sx;R+;$lo;R+^1$n;R+^1$e;R+4!4$sx;R+;$lo;R+^1$n;R+^1$eb0;R+4_>#4#3#2#1$sx;R+;$k;R+^1$i;R+5$n;R+^1!4$sx;R+;$k;R+^1$i;R+5$n;R+^1_>#4#3#2#1#1#2#1#2#1$n;R+^1!1$n;R+^1$Hc;R!3+=0=D&H;R!6'`Y0=^C,_[!2,N+^=#;#1+a>!2'a@!3+=+^1!1'`R#<!2'^:!2'^:!1'^;#C'^<#J#1#1$op;R+a<$a;R+4$b;R+4_@$op;R+a<$a;R+4$b;R+4_@$op;R+a=$a;R+4$b;R+4_A$op;R+a=$a;R+4$b;R+4_A$sx;R+;$lo;R+^1$n;R+^1$e;R+4!4$sx;R+;$lo;R+^1$n;R+^1$e;R+4$Hc;R_B&H;R!6'`Y0=$e0;R0^B,_[_C#1+a>_D#4#3#2#1$sx;R+;$k;R+^1$i;R+5$n;R+^1!4$sx;R+;$k;R+^1$i;R+5$n;R+^1$Hc;R_B&H;R!6'`Y0=^C,_[_C#1+a>_D#4#3#2#1#7#<#1#1$H;R!3+=0=F&H0;R!6'`Y0=^C,_[D#1+a>!2'a@E#1#2#1$Hc;R!3+=0!8'`L#@#?#>#=#8#7#6#5=$H;R!3+=0=C&H0;R!6'`Y0=^C,_[>#1+a>!2'a@?#1#1#3").
Qed.

(* [comment removed for export] *)
Definition TXT (buf ln : Z) (M : mem) : Prop :=
  exists txt, PMFX.gtext txt /\ len txt = ln /\ 1 <= ln <= 25 /\ L5.bytes_at RSEGS M buf txt /\ PML.u8 M (buf + ln) 0 /\ L5.defined M buf 100.
Definition text (sp : Z) (i : nat) (E : env) (M : mem) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10|30;$sp;R+5$i;R+^1$E;R+_R$M;R%~R!1+E!1,F|600;!1+I!1+E!1,F0-^1RN$x;R+^1w!1'_0#32+a?$n;R+^1!3'aA!2'a:#5!1,0|714;!2'aB#3!1,1!1,_1#1#2").

Section DtoaFalseOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.
Hypothesis SNP : PMFX.snprintf_g_spec L.
Hypothesis DSG : PMFX.decstr_to_double_g_spec L PML.STRTOD_SCR_V.
Hypothesis DBOK : PMFXT.dump_buffer_x_specU L HI.

(* [comment removed for export] *)
Lemma TXT_agree : forall buf ln (M M' : mem), 0 <= buf -> buf + 101 <= 2 ^ 64 -> L5C.agree_on M M' buf 101 -> mem_grows M M' -> TXT buf ln M -> TXT buf ln M'.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^Y0|600;!1,F0|30;%~R!1+E1!1+I!1+E!1,F2!1,0|625;|10;!1,05!1,00!2'_L67!1+^9+5!1'aG#1!1'aH#1!1,0,V|49;!1,0=!1,0|624;!1'aG#2!3+=+5!1'aH#6#@!2+H!2'aC<#D!2'aC#D>!4'aI'K#G#I#>!3'aJ#K!2'_K#M#L,U!3+=+5!1'aH#F#P!2+H!2'aC<#P!2'aC#P>!4'aI'K#N#Q#F!2'_K#Q#P!3'aJ#NH,U!3'aK#N#Q?!2+HIJ!2+HGK!2+HFL!2'`E+5#F!1'_YN!2'aO67%~R!2'`2,U6%~R!2'aC,U7!2'`2,U8!2'aC,U6$Ha;RR$~R+a?!3'aP67#2%Ha;RR%~R+a?!2'aC,U8!1,9+`5!1+^9+`5!2,aQ+5#2!1+`7+5!1+`9+5!2,aR+5,V!2'`AY,`<!4'`B#1#3vv!2,:+;,<!3+=+;!2'`C#1#3,<!3'`D+5,U#2!1'aTN!2'aC,UO}2}1!3,aV+5!2,aW+5^2!3,aV+5!2,aW+5^3!2,aW+5,^4!3,2+`5!2,aU^4,aXU!2,aQ+5#3!4,aY+5^6#2!2,aQ+5#4|11;!2,aR+5^8!2,`>+5>!7,a[Y'`:+`;+`;,`<!6,a\Y'`:+`;+`;,`<#6!7,`8Y'`:+`;+`;,`<!4,`=+5^9,aS^:,`@!1,^R+`;!2,aR+55!7,`8Y'`:+`;+`;,`<!4,`=+5^=,b0^9,`@!3,b1+5Z^=!3,b1+5Z!2,`>+54!2+H#4!2'aC#3>!3+=+5#3#4!2'_K#3#4!2'_K#34!2'aC<#T!1'_Y!2'`E+5#J!2,`>+5,U!7,`8Y'`:+`;+`;,`<!4,`=+5^G,aSZ,`@!2'aC,U#1!2'aC,U#2!3,b2+5!2,`>+561!7,`8Y'`:+`;+`;,`<!4,`=+5^@,aS^K,`@!4,aY+5^6#2!1,`6+5!2,`>+5<!6,a\Y'`:+`;+`;,`<#5!7,a[Y'`:+`;+`;,`<!7,`8Y'`:+`;+`;,`<!4,`=+5^N,aS^=,`@^O!2+H!2'aC<#2#3!2'_K#2#3!2'aC#S>!7,a[Y'`:+`;+`;,`<^O!7,`8Y'`:+`;+`;,`<!4,`=+5^=,aS^:,`@!3,b1+5^?^N!2+H#3!2'aC#2>!2'_K#24!2'aC<#S$buf;R+5$ln;R+5$M;R3$M';R3$Hb;R!2'aC,U#4$He;R!2'aC!2'_K#548$Hag;R!4'aD#4#3#64$Hgr;R!2'aE#5#4$H;R!3'aA#8#7#6!5'aF9$txt;R9!2+H:!2+H!3+=+5;#9!2+H!2+H!2'aC<#9!2'aC#9>!2+H!4'aI'K#8#:#1!2+H!3'aJ#8!2'_K#:#9,U!3'aK#8#:?!3'aA#9#8#6$x;R9$~R!1$txt;R9!2+H:!2+H!3+=+5;#:!2+H!2+H!2'aC<#:!2'aC#:>!2+H!4'aI'K#9#;#1!2+H!3'aJ#9!2'_K#;#:,U!3'aK#9#;?#1!2$txt;R9$H;R!2+H:!2+H!3+=+5;#;!2+H!2+H!2'aC<#;!2'aC#;>!2+H!4'aI'K#:#<#1!2+H!3'aJ#:!2'_K#<#;,U!3'aK#:#<?!5'aL@!2+H!3+=+5!1'aH#2#<!2+H!2+H!2'aC<#<!2'aC#<>!2+H!4'aI'K#;#=#2!2+H!3'aJ#;!2'_K#=#<,U!3'aK#;#=?!3'aA#=#<#:$~R@$~R!2+H!3+=+5!1'aH#3#=!2+H!2+H!2'aC<#=!2'aC#=>!2+H!4'aI'K#<#>#3!2+H!3'aJ#<!2'_K#>#=,U!3'aK#<#>?!2$G1;R!1'aG#4$H;R!2+H!3+=+5!1'aH#5#?!2+H!2+H!2'aC<#?!2'aC#?>!2+H!4'aI'K#>#@#5!2+H!3'aJ#>!2'_K#@#?,U!3'aK#>#@?!5'aLA!2+H!2+H!2'aC<#@!2'aC#@>!2+H!4'aI'K#?#A#6!2+H!3'aJ#?!2'_K#A#@,U!3'aK#?#A?!3'aA#A#@#>$~RA$~R!2+H!2+H!2'aC<#A!2'aC#A>!2+H!4'aI'K#@#B#7!2+H!3'aJ#@!2'_K#B#A,U!3'aK#@#B?!2$G2;R!3+=+5!1'aH#8#B$H;R!2+H!2+H!2'aC<#C!2'aC#C>!2+H!4'aI'K#B#D#9!2+H!3'aJ#B!2'_K#D#C,U!3'aK#B#D?!5'aLB!2+H!4'aI'K#C#E#:!2+H!3'aJ#C!2'_K#E#D,U!3'aK#C#E?!3'aA#E#D#B$~RB$~R!2+H!4'aI'K#D#F#;!2+H!3'aJ#D!2'_K#F#E,U!3'aK#D#F?!2$G3;R!2+H!2'aC<#F!2'aC#F>$H;R!2+H!4'aI'K#F#H#=!2+H!3'aJ#F!2'_K#H#G,U!3'aK#F#H?!5'aLC!2+H!3'aJ#G!2'_K#I#H,U!3'aK#G#I?!3'aA#I#H#F$~RC$~R!2+H!3'aJ#H!2'_K#J#I,U!3'aK#H#J?!2$G4;R!4'aI'K#I#K#@$H;R!2+H!3'aJ#J!2'_K#L#K,U!3'aK#J#L?!5'aLD!3'aK#K#M?!3'aA#M#L#J$~RD$~R!3'aK#L#N?!2$G5;R!3'aJ#M!2'_K#O#N,U$G6;R!3'aK#N#P?!4,D9$txt;R9!2+H:!2+H!3+=+5;#Q!2+H!2+H!2'aC<#Q!2'aC#Q>!2+H!4'aI'K#O#R#1!2+H!3'aJ#O!2'_K#R#Q,U!3'aK#O#R?#F!4,\!1'aG#F!2+HEM#B!4,\EM#>!4,\FL#:!4,\GK!9'aM'K#O#N#Q#F!9'aN#O#N#Q4#QO#K&__sat8;RPQ&__sat7;RST&__arith;R$__x1;R+5&__wit;RUV&__varmap;RWX&__ff;R!7,`8Y'`:+`;+`;,`<!4,`=+5Z,aSZ,`@[\%__x1;R+5!2'aC#1#1!1#1#T&cstr;R^0^1&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x3;R+5$__x2;R+5$__x1;R+5&__wit;R^5V&__varmap;R^7X&__ff;R!8,aZY'`:+`;+`;,`<^;^<!8,aZY'`:+`;+`;,`<^>^<!7,`8Y'`:+`;+`;,`<!4,`=+5^?,aS^@,`@[\%__p1;Rw%__x3;R+5%__x2;R+5%__x1;R+5%~R^A%~R^B!2'aC^C^D!6#1^E#T^F#U#>#B&__sat8;RPQ&__sat7;RST&__arith;R$__x1;R+5&__wit;RUV&__varmap;RWX&__ff;R!8,aZY'`:+`;+`;,`<^H^<^H[\%__x1;R+5%~R^I^J!2#1#T#P&cstr;R^0^1&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x3;R+5$__x2;R+5$__x1;R+5&__wit;R!3,2+`5!2,aU!3,aV+5!2,aW+5}3^4,aXUV&__varmap;R^7X&__ff;R!8,aZY'`:+`;+`;,`<^;^<!8,aZY'`:+`;+`;,`<^>^<!8,aZY'`:+`;+`;,`<^L^<!7,`8Y'`:+`;+`;,`<!4,`=+5^?,aS^K,`@[\%__p1;Rw%__x3;R+5%__x2;R+5%__x1;R+5%~R^A%~R^B%~R!2'aC^D8!2'aC!2'_K#4#58!7#1^E#T^F#U#>#B#P#6!4,\IJ!8'b3#O#NH,U!9'aN#O#N#Q4H<#K&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x2;R+5$__x1;R+5&__wit;RUV&__varmap;R^MX&__ff;R!8,aZY'`:+`;+`;,`<^P^<!7,`8Y'`:+`;+`;,`<!4,`=+5Z,aS^?,`@[\%__p1;Rw%__x2;R+5%__x1;R+5%~R^Q!2'aC#2^R!4#1^S#S#T#=&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x2;R+5$__x1;R+5&__wit;RUV&__varmap;R^MX&__ff;R!8,aZY'`:+`;+`;,`<^T^<!7,`8Y'`:+`;+`;,`<!4,`=+5^U,aS^@,`@[\%__p1;Rw%__x2;R+5%__x1;R+5%~R^V!2'aC!2'_K^R<^W!4#1^X#S#T#=&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x2;R+5$__x1;R+5&__wit;R^5V&__varmap;R^MX&__ff;R!8,aZY'`:+`;+`;,`<^P^<!8,aZY'`:+`;+`;,`<^H^<!7,`8Y'`:+`;+`;,`<!4,`=+5^G,aS^?,`@[\%__p1;Rw%__x2;R+5%__x1;R+5%~R^Q%~R^J!2'aC,U^C!5#1^S#S#T#=#P&__sat8;RPQ&__sat7;RST&__arith;R$__p1;Rw$__x2;R+5$__x1;R+5&__wit;R^5V&__varmap;R^MX&__ff;R!8,aZY'`:+`;+`;,`<^T^<!8,aZY'`:+`;+`;,`<^L^<!7,`8Y'`:+`;+`;,`<!4,`=+5^U,aS^K,`@[\%__p1;Rw%__x2;R+5%__x1;R+5%~R^V%~R!2'aC^W8!2'aC!2'_K^C<8!5#1^X#S#T#=#O#2vd$q;R+5$Hq;R!2+H^I!2'`2#1?!2#L!2'L1!2'_K#S#2!2#3#2#1J#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1").
Qed.

Section StretchD.
Variables (E0 : env) (sp S2 : Z).
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis SPR : hl_ceil L + 9200 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis S2OBJ : PML.obj_on_stack L sp S2 24.

Lemma out_F0D : forall (F : list SGP.region) E' a, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 9200 <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct SPR as (P1 & P2 & P3). unfold hl_ceil in P1.
  unfold F0 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[X|[]]]; injection X as <- <- <-;
    rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) _ Hag eq_refl); unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite U2;
    rewrite u64_of_Z by lia; lia.
Qed.

Lemma out_F1D : forall (F : list SGP.region) E' a, SP.F_sub F F1 = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - 160 <= a < sp - 152) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct SPR as (P1 & P2 & P3). unfold hl_ceil in P1.
  unfold F1 in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-;
    rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) _ Hag eq_refl); unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite U2;
    rewrite u64_of_Z by lia; lia.
Qed.

Lemma sink_stretchD : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) ->
  (forall b, In b (PML.srep_blocks (ESBU.s_rep g)) -> block_range L (fst b) (snd b)) ->
  ESBU.sink_inv M S2 g -> ESBU.sink_inv M' S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HB (HS & HL).
  destruct S2OBJ as (O1 & O2 & O3). destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 9200 \/ sp <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 i Hi. apply HFR. apply (out_F0D F E' i HF Hag); lia. }
  split; [|exact HL].
  apply (EK.sink_at_agree M M' S2 (ESBU.s_rep g)); [lia | lia | apply AG; lia | | exact HS].
  destruct (ESBU.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
  destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. apply AG; unfold hl_ceil in *; lia.
Qed.

Lemma txt_stretchD : forall (F : list SGP.region) E' (M M' : mem) ln, SP.F_sub F F1 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> mem_grows M M' -> TXT (sp - 148) ln M -> TXT (sp - 148) ln M'.
Proof.
  intros F E' M M' ln HF Hag HFR HG HT. destruct SPR as (P1 & P2 & P3). unfold hl_ceil in P1.
  apply (TXT_agree (sp - 148) ln M M'); [lia | lia | | exact HG | exact HT].
  intros i Hi. apply HFR. apply (out_F1D F E' i HF Hag); lia.
Qed.

Lemma img_stretchD : forall (F : list SGP.region) E' (M M' : mem), SP.F_sub F F0 = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) -> PML.img_ro M -> PML.img_ro M'.
Proof.
  intros F E' M M' HF Hag HFR HIm. destruct SPR as (P1 & P2 & P3). unfold hl_ceil in P1.
  apply (EK.img_ro_agree M M'); [|exact HIm].
  intros a Ha. unfold PML.IMG_RO_HI in Ha. apply HFR. apply (out_F0D F E' a HF Hag); lia.
Qed.

Lemma sink_frameD : forall (Wf : list L5.range) (M M' : mem) g, L5.frame_but Wf M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> (a < sp - 9200 \/ sp <= a) -> (a < hl_img_lo L \/ hl_img_hi L <= a) -> L5.outside Wf a) ->
  (forall b, In b (PML.srep_blocks (ESBU.s_rep g)) -> block_range L (fst b) (snd b)) ->
  ESBU.sink_inv M S2 g -> ESBU.sink_inv M' S2 g.
Proof.
  intros Wf M M' g HFB HOUT HB (HS & HL).
  destruct S2OBJ as (O1 & O2 & O3). destruct SPR as (P1 & P2 & P3).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 9200 \/ sp <= a) -> (a + n <= hl_img_lo L \/ hl_img_hi L <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 H3 i Hi. apply HFB. rewrite L5.unsigned_lit by lia. apply HOUT; lia. }
  split; [|exact HL].
  apply (EK.sink_at_agree M M' S2 (ESBU.s_rep g)); [lia | lia | apply AG; unfold hl_ceil in *; lia | | exact HS].
  destruct (ESBU.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
  destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. apply AG; unfold hl_ceil in *; lia.
Qed.
End StretchD.

Ltac rcut := repeat match goal with |- context [ret_cut ?a ?b] => let v := eval vm_compute in (ret_cut a b) in change (ret_cut a b) with v end.
Ltac dik i kk Xk := destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]; destruct kk as [|[|kk]]; cbn [kind] in Xk; try discriminate Xk.
Ltac rcutH H := repeat match type of H with context [ret_cut ?a ?b] => let v := eval vm_compute in (ret_cut a b) in change (ret_cut a b) with v in H end.

Theorem dtoa_false_x_ok : PMFXT.dtoa_false_x_specU L HI PML.STRTOD_SCR_V.
Proof.
  intros dp LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & (Ha0 & Hdp & Ha1) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2' & S3 & S4 & S5).
  assert (DFV : PMFXT.DF_SCR PML.STRTOD_SCR_V = 9200) by (vm_compute; reflexivity).
  rewrite DFV in S2', S5, Hcont.
  assert (BLS0 : forall i, nth i G.BLS [] = []) by (intros i; do 15 (destruct i as [|i]; [reflexivity|]); destruct i; reflexivity).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof Hobj as (OS1 & OS2 & OS3). unfold PML.apart in Hapsk.
  set (len0 := len (PML.srep_chars rep)).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 dp) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 SK) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 S2) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = dp) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = SK) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = S2) by (rewrite V32; apply u64_of_Z; lia).
  assert (SCRV : CH.hd_scr G.HDECL = 9200) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite SCRV; unfold hl_ceil; repeat split; lia).
  assert (SPR : hl_ceil L + 9200 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47) by (unfold hl_ceil; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  set (W := [(S2, 24)]).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
  { intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. unfold in_errno. rewrite LER.
    split; [lia|]. split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | lia]. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (W_S2 : In (S2, 24) W) by (left; reflexivity).
  assert (OADDR : estart E0 (SA S2E 0) = S2) by (unfold estart, S2E; cbn [a_base a_off edenot]; rewrite U32; lia).
  set (XIv := fun (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) => ESBU.sink_inv M1 S2 g1 /\ phase i (ESBU.s_len g1 - len0) /\ text sp i E M1).
  set (CredV := ESBU.CredV L kx bx).
  set (gB := ESBU.gB []).
  assert (GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1)) by (intros g1; unfold gB, ESBU.gB; apply app_nil_r).
  assert (AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E').
  { intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. }
  assert (BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
                  (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E0 E /\
                  exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1).
  { intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb. }
  assert (KIMG : forall LBx a, 0x10000 <= a < PML.IMG_RO_HI -> L5C.kept L LBx sp (CH.hd_scr G.HDECL) W a).
  { intros LBx a Ha. unfold PML.IMG_RO_HI in Ha.
    apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LER; lia|].
    intros w Hw Hin. destruct Hw as [<-|[]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; lia. }
  assert (IMGC : forall g1 M0c i E (M1 : mem) m1, CH2V.okV L M LBo sp G.HDECL W M0c ->
             CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> PML.img_ro M1).
  { intros g1 M0c i E M1 m1 (O1 & _ & _) (_ & _ & _ & _ & HK & _) a Ha.
    rewrite (HK a (KIMG _ a Ha)), (O1 a (KIMG _ a Ha)). exact (Himg a Ha). }
  assert (STRETCH : forall g1 M0c i c k ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c k ps t -> CC.At (hl_segs L) c E R1 M1 ->
                      CH2V.okV L M LBo sp G.HDECL W M0c ->
                      CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
                      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
                      ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E0 E' /\ PML.img_ro M').
  { intros g1 M0c i c k ps t E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    apply andb_prop in X as [XF _]. apply andb_prop in XF as [XF _]. apply andb_prop in XF as [XF _].
    destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
    split; [|split; [exact HagE'|]].
    - destruct HX as (HX1 & _).
      exact (sink_stretchD E0 sp S2 U2 SPR Hobj (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) HB HX1).
    - exact (img_stretchD E0 sp U2 SPR (CC.cp_F c) E' M1 M' XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (IMGC g1 M0c i E M1 m1 OKV HA)). }
  unfold PML.cfg. change PMFX.PC_DTOA_FALSE with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := 0%nat) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - intros g1 M0c OKV i c kk ps j sg IL E R1 E' R' M1 M' m1 HAt HA Hag HLF HX.
    destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & _).
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. apply andb_prop in X as [_ X].
    apply andb_prop in X as [Xk Xj]. apply Nat.eqb_eq in Xk. apply Nat.eqb_eq in Xj. subst j.
    destruct HX as (_ & HP & _). split; [exact HINV|]. split; [|exact I]. cbn [phase].
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]; cbn [phase] in HP; try lia;
      destruct kk as [|[|kk]]; cbn [kind] in Xk; discriminate Xk.
  - intros i c kk ps pc IL g1 M0c OKV.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. cbv beta iota zeta in X.
    apply andb_prop in X as [XF X]. apply andb_prop in XF as [XF XN]. apply andb_prop in XF as [XF XF1].
    assert (TXTJ : forall E E' E2 R1 (M1 : mem) M' ps' n, env_agree (CC.cp_nx c) E E' -> env_agree (CC.cp_nx c) E' E2 -> env_agree GT.NF E0 E' ->
              CC.leaf_facts (hl_segs L) c ps' E' R1 M1 M' -> LV i = S n ->
              TXT (sp - 148) (uv E (EVar (S n))) M1 -> TXT (sp - 148) (uv E2 (EVar (S n))) M').
    { intros E E' E2 R1 M1 M' ps' n Hag Hag2 HagE' HLF HLV HT.
      unfold needs in XN. rewrite HLV in XN. apply Nat.leb_le in XN.
      rewrite HLV in XF1. cbn [Nat.eqb orb] in XF1.
      assert (EQ : uv E2 (EVar (S n)) = uv E (EVar (S n))).
      { unfold uv. rewrite (PB.uv_agree (CC.cp_nx c) E' E2 (EVar (S n)) Hag2) by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia).
        apply (PB.uv_agree (CC.cp_nx c) E E' (EVar (S n)) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. lia. }
      rewrite EQ. exact (txt_stretchD E0 sp U2 SPR (CC.cp_F c) E' M1 M' _ XF1 HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) (CC.lf_grows _ _ _ _ _ _ _ HLF) HT). }
    destruct (Z.eqb_spec pc PML.PC_STR_PUSH_BACK) as [->|Hne1].
    { cbv iota in X.
      apply andb_prop in X as [X Xk]. apply andb_prop in X as [Xpc Xs]. apply Z.eqb_eq in Xpc. apply Nat.eqb_eq in Xk.
      unfold sinkj, ret_cut in Xs. destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate Xs].
      apply andb_prop in Xs as [_ Xs].
      destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate Xs].
      destruct (ESB.pushb_chk GT.NF G.HDECL S2E 0 c ps cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
      apply (ESBU.pushb_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
               S2 Hobj W_S2 S2E 0 eq_refl OADDR PUSHB_OK i c kk ps j cj ci g1 M0c OKV IL Hret Hcj Xpc Hchk).
      - intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF.
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & _).
        split; [exact HINV|]. destruct HX as (_ & HP & _).
        dik i kk Xk; cbn [phase] in HP; unfold len0 in *; lia.
      - intros E E' R' M1 M' E2 M2 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1.
        destruct HX as (_ & HP & _).
        dik i kk Xk; vm_compute in Hret; injection Hret as <-; (split; [exact HINV2|]); (split; [cbn [phase] in HP |- *; rewrite G1; lia | exact I]). }
    destruct (Z.eqb_spec pc PMFX.PC_SNPRINTF) as [->|Hne2].
    { cbv iota in X.
      apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 Xs]. apply Z.eqb_eq in X1. apply Nat.eqb_eq in Xk.
      unfold sinkj in Xs. apply andb_prop in Xs as [Xj0 Xs].
      assert (Hret : CH2.ret_of G.RETS i kk = Some (ret_cut i kk)) by (unfold ret_cut in *; destruct (CH2.ret_of G.RETS i kk); [reflexivity | discriminate Xj0]).
      destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xs].
      destruct (snp_chk (LV (ret_cut i kk)) c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
      unfold snp_chk in Hchk.
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
      apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R14]. apply andb_prop in Hb as [Hb R13]. apply andb_prop in Hb as [Hb R12].
      apply andb_prop in Hb as [Hb R11]. apply andb_prop in Hb as [Hb R10]. apply andb_prop in Hb as [Hlv Hbe].
      apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R12. apply expr_eqb_eq in R14. apply expr_eqb_eq in R2X. apply Nat.eqb_eq in Hlv.
      pose proof (custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk) as Hcnx.
      assert (CS1 : CH2.leaves_all G.CPS G.TAGS (fun i c k ps t => negb (Nat.eqb (kind i k) 3) || CC.has_cell (SR.ps_cells ps) (KUnk (SA (EVar 2) (-160)) (ELit 112)) ||
                                                   CC.has_cell (SR.ps_cells ps) (KUnk (SA (EVar 2) (-148)) (ELit 100))) = true) by (vm_compute; reflexivity).
      pose proof (CH2.leaves_all_sound _ _ _ CS1 _ _ _ _ _ IL) as XC. cbv beta in XC. rewrite Xk in XC. cbn [Nat.eqb negb orb] in XC.
      apply (EPU.pure_leaf_okV L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               (fun _ _ _ _ _ _ H => H) PMFX.PC_SNPRINTF SNP_SCR _ _ _ i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj X1 Hchk Hbe).
      intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HH1 HC1 HFP RET.
      pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
      destruct HA' as (Hmo1 & _).
      destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & HIMG).
      destruct (BRG _ _ _ _ _ _ HA) as (HB & _ & _).
      destruct HX as (_ & HP & _).
      rewrite LS in HK. rewrite Hreq in HR.
      assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
      assert (CSP : CH2.ci_csp ci = -160).
      { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
        apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 160)) in G2; [| unfold XCE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
      assert (Ga0 : getr R' 10%bv = Z_to_bv 64 (sp - 148)).
      { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10.
        apply PB.edenot_of_uv. unfold PB.uv. apply CL5.u_lin; [unfold BUFE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. }
      assert (Ga1 : getr R' 11%bv = Z_to_bv 64 100).
      { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11. reflexivity. }
      assert (Ga12 : getr R' 12%bv = Z_to_bv 64 PMFX.FMT_G).
      { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite R12. reflexivity. }
      assert (Ga13 : exists p, getr R' 13%bv = Z_to_bv 64 p /\ (p = 15 \/ p = 17)).
      { rewrite (HR 13%bv). unfold sr_get. change (bv_eqb (13%bv : bv 5) 0) with false. cbv iota. change (ridx 13%bv) with 13%nat.
        apply orb_prop in R13 as [R13|R13]; apply expr_eqb_eq in R13; rewrite R13; [exists 15 | exists 17]; (split; [reflexivity | lia]). }
      destruct Ga13 as (p & Ga13 & Hp).
      assert (Ga14 : getr R' 14%bv = Z_to_bv 64 (uv E' (EVar 48))).
      { rewrite (HR 14%bv). unfold sr_get. change (bv_eqb (14%bv : bv 5) 0) with false. cbv iota. change (ridx 14%bv) with 14%nat. rewrite R14.
        unfold uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (HDEF : L5.defined M' (sp - 148) 100).
      { apply orb_prop in XC as [XC|XC]; pose proof (PB.has_ok E' M' _ _ HK XC) as HKU.
        - apply (L5.defined_sub M' (sp - 160) 112); [| lia | lia].
          apply (CL5.kunk_elim RSEGS E' M' _ _ (sp - 160) 112 HKU); [unfold estart; cbn [a_base a_off edenot]; rewrite U2'; lia | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity].
        - apply (CL5.kunk_elim RSEGS E' M' _ _ (sp - 148) 100 HKU); [unfold estart; cbn [a_base a_off edenot]; rewrite U2'; lia | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity]. }
      assert (SNPV : SNP_SCR = 6144) by reflexivity.
      destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *. rewrite SNPV in T2, T5.
      apply (SNP (sp - 148) p (uv E' (EVar 48)) (sp + -160) (CC.cp_pc cj) fx' R' M' m1 K (proj1 Hmo1) (proj1 (proj2 Hmo1)) HKnil HFP).
      { unfold PMFX.SNPRINTF_SCR.
        split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                 split; [exact T1 | split; [lia | split; [lia | split; [exact T4 | exact T5]]]]]]]]|].
        split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga12|]. split; [exact Ga13|]. split; [exact Hp|].
        split; [exact Ga14|]. split; [apply PB.uv_range|]. split; [exact HIMG|]. split; [exact HDEF|]. split; [lia | unfold hl_ceil in *; lia]. }
      intros fx2 R2 M2 HFP2 (txt & Hgt & Hln & Pa0 & Hbs & Hnul & Hdef2) HRP HFB HGR.
      apply (RET fx2 R2 M2 [(sp - 148, 100)] HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HFB HGR).
      + intros w a [<-|[]] Hin. unfold L5.in_rng in Hin; cbn [fst snd] in Hin. split.
        * exists (EVar 2, -148, ELit 100). split; [left; reflexivity|].
          unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite U2'. rewrite u64_of_Z by lia. lia.
        * left. rewrite SCRV. lia.
      + intros Xn HXn _. rewrite LS.
        destruct HXn as [<-|[<-|[]]].
        * cbn [kentry_ok edenot]. replace (CC.cp_nx cj - APC.NCS + 4)%nat with (CH2.ci_nx ci + 4)%nat by lia. rewrite retEx0_a0.
          unfold PML.a0 in Pa0. rewrite Pa0. rewrite u64_of_Z by lia. lia.
        * eapply CL5.kunk_intro with (A := sp - 148) (N := 100);
            [unfold estart; cbn [a_base a_off edenot]; destruct (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2) as [AGR _]; rewrite <- (AGR 2%nat) by lia; rewrite U2'; lia
            | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity | lia | lia | lia | exact Hdef2].
      + split.
        { apply (sink_frameD sp S2 SPR Hobj _ M' M2 g1 HFB); [| exact HB | exact HINV].
          intros a Ha H1 H2 rg Hrg. destruct Hrg as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; unfold PMFX.SNPRINTF_SCR; lia. }
        split.
        { dik i kk Xk; rcut; cbn [phase] in HP |- *; lia. }
        unfold text. replace (LV (ret_cut i kk)) with (S (CH2.ci_nx ci + 3)) by lia. cbv iota.
        replace (S (CH2.ci_nx ci + 3)) with (CH2.ci_nx ci + 4)%nat by lia.
        unfold uv, PB.uv. cbn [edenot]. rewrite retEx0_a0. unfold PML.a0 in Pa0. rewrite Pa0. rewrite u64_of_Z by lia.
        exists txt. split; [exact Hgt|]. split; [reflexivity|]. split; [exact Hln|]. split; [exact Hbs|]. split; [exact Hnul | exact Hdef2]. }
    destruct (Z.eqb_spec pc PML.PC_DECSTR_DOUBLE) as [->|Hne3].
    { cbv iota in X.
      apply andb_prop in X as [X _]. apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 Xs]. apply Z.eqb_eq in X1. apply Nat.eqb_eq in Xk.
      unfold sinkj in Xs. apply andb_prop in Xs as [Xj0 Xs].
      assert (Hret : CH2.ret_of G.RETS i kk = Some (ret_cut i kk)) by (unfold ret_cut in *; destruct (CH2.ret_of G.RETS i kk); [reflexivity | discriminate Xj0]).
      destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xs].
      destruct (dec_chk c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
      unfold dec_chk in Hchk.
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
      apply andb_prop in Hb as [Hb Xcell]. apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R12]. apply andb_prop in Hb as [Hb R11]. apply andb_prop in Hb as [Hbe R10].
      apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R12. apply expr_eqb_eq in R2X.
      pose proof (custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk) as Hcnx.
      assert (HIK : i = 3%nat /\ kk = 0%nat) by (dik i kk Xk; split; reflexivity). destruct HIK as [-> ->].
      rcutH Hcj. rcutH Hret.
      assert (NX5 : (56 <= CC.cp_nx cj - APC.NCS)%nat) by (vm_compute in Hcj; injection Hcj as <-; vm_compute; lia).
      apply (EPU.pure_leaf_okV L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               (fun _ _ _ _ _ _ H => H) PML.PC_DECSTR_DOUBLE DEC_SCR _ _ _ 3%nat c 0%nat ps 5%nat cj ci g1 M0c OKV IL Hret Hcj X1 Hchk Hbe).
      intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HH1 HC1 HFP RET.
      pose proof CF as [HA' HR Hreq (V1 & V2' & V3 & V4' & V5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
      destruct HA' as (Hmo1 & _).
      destruct (STRETCH g1 M0c 3%nat c 0%nat ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & _ & HIMG).
      destruct (BRG _ _ _ _ _ _ HA) as (HB & _ & _).
      destruct HX as (_ & HP & HT).
      unfold text in HT. change (LV 3) with (S 54%nat) in HT.
      pose proof (TXTJ E E' E' R' M1 M' ps 54%nat Hag (CC.env_agree_refl _ _) HagE' HLF eq_refl HT) as HT'.
      pose proof HT' as (txt & Hgt & Hlen & Hln & Hbs & Hnul & Hdef). unfold len in Hlen.
      set (n := uv E' (EVar 55%nat)) in *.
      rewrite LS in HK. rewrite Hreq in HR.
      assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
      assert (CSP : CH2.ci_csp ci = -160).
      { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
        apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 160)) in G2; [| unfold XCE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
      assert (Ga0 : getr R' 10%bv = Z_to_bv 64 (sp - 148)).
      { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10.
        apply PB.edenot_of_uv. unfold PB.uv. apply CL5.u_lin; [unfold BUFE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. }
      assert (Ga1 : getr R' 11%bv = Z_to_bv 64 (Z.of_nat (length txt))).
      { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11.
        rewrite Hlen. unfold n, uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (Ga2 : getr R' 12%bv = Z_to_bv 64 (sp - 160)).
      { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite R12.
        apply PB.edenot_of_uv. unfold PB.uv. apply CL5.u_lin; [unfold XCE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. }
      assert (HD8 : L5.defined M' (sp - 160) 8).
      { pose proof (PB.has_ok E' M' _ _ HK Xcell) as HC0.
        pose proof (CL5.kword64_elim RSEGS E' M' _ _ (sp - 160) 0 HC0 ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite U2'; lia) ltac:(reflexivity)) as HU.
        apply (PB.defined_of_u64 M' (sp - 160) 0 HU); unfold hl_ceil in *; lia. }
      assert (DECV : DEC_SCR = 96 + PML.STRTOD_SCR_V) by reflexivity.
      destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *. rewrite DECV in T2, T5.
      unfold len in Hln, Hnul.
      apply (DSG (sp - 148) (sp - 160) (sp + -160) (CC.cp_pc cj) txt fx' R' M' m1 K (proj1 Hmo1) (proj1 (proj2 Hmo1)) HKnil HFP).
      { split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                 split; [exact T1 | split; [unfold PML.STRTOD_SCR_V in *; lia | split; [unfold PML.STRTOD_SCR_V in *; lia | split; [exact T4 | exact T5]]]]]]]]|].
        split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [exact HIMG|]. split; [exact Hbs|]. split; [rewrite Hlen; exact Hnul|].
        split; [exact Hgt|]. split; [lia|]. split; [exact HD8|]. split; [lia|]. split; [unfold hl_ceil in *; lia|].
        split; [apply (L5.defined_sub M' (sp - 148) 100); [exact Hdef | lia | lia]|].
        split; [unfold hl_ceil in *; lia|]. split; [unfold hl_ceil in *; lia|]. split; [right; lia|]. right. unfold PML.TP. unfold hl_ceil in *; lia. }
      intros fx2 R2 M2 HFP2 (Pa0 & c1 & Pa1 & Hc1in) HRP HFB HGR.
      assert (AGR : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) by apply CH2.retEx_agree.
      apply (RET fx2 R2 M2 [(sp - 160, 8); (PML.TP - 164, 4)] HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HFB HGR).
      + intros w a Hw Hin. destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; split.
        * exists (EVar 2, -160, ELit 8). split; [left; reflexivity|].
          unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite U2'. rewrite u64_of_Z by lia. lia.
        * left. rewrite SCRV. lia.
        * exists (ELit 0, ERRNO, ELit 4). split; [right; left; reflexivity|].
          unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_of_Z by lia. unfold ERRNO, PML.TP in *. lia.
        * right. split; [unfold PML.TP in Hin; lia|]. split.
          -- intros LB [(A1 & A2 & A3) | A4].
             ++ apply A3. rewrite ILO, IHI. unfold PML.TP in Hin. split; [lia|]. intros XSt. pose proof (PmLayout.ly_static L LAY a XSt). lia.
             ++ pose proof (PmLayout.ly_ro_img L LAY a A4 ltac:(rewrite ILO, IHI; unfold PML.TP in Hin; lia)). unfold PML.TP in Hin. lia.
          -- intros (_ & _ & NE & _). apply NE. unfold in_errno. rewrite LER. unfold PML.TP in Hin. lia.
      + intros Xn HXn _. rewrite LS.
        destruct HXn as [<-|[<-|[<-|[]]]].
        * cbn [kentry_ok edenot]. replace (CC.cp_nx cj - APC.NCS + 5)%nat with (CH2.ci_nx ci + 5)%nat by lia. rewrite retEx0_a1, Pa1.
          destruct Hc1in as [<-|[<-|[]]]; match goal with |- ?lo <= ?x <= ?hi => let v := eval vm_compute in x in change x with v end; lia.
        * cbn [kentry_ok edenot]. replace (CC.cp_nx cj - APC.NCS + 5)%nat with (CH2.ci_nx ci + 5)%nat by lia. rewrite retEx0_a1, Pa1.
          rewrite u64_of_Z by (destruct Hc1in as [<-|[<-|[]]]; lia). destruct Hc1in as [<-|[<-|[]]]; lia.
        * eapply CL5.kunk_intro with (A := sp - 160) (N := 8);
            [unfold estart; cbn [a_base a_off edenot]; destruct AGR as [AGR0 _]; rewrite <- (AGR0 2%nat) by lia; rewrite U2'; lia
            | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; reflexivity | lia | lia | lia | exact (L5.defined_grows M' M2 _ _ HGR HD8)].
      + split.
        { apply (sink_frameD sp S2 SPR Hobj _ M' M2 g1 HFB); [| exact HB | exact HINV].
          intros a Ha H1 H2 rg Hrg. rewrite ILO, IHI in H2. destruct Hrg as [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; unfold PML.TP, PML.STRTOD_SCR_V in *; lia. }
        split.
        { cbn [phase] in HP |- *. lia. }
        unfold text. change (LV 5) with (S 54%nat). cbv iota.
        assert (EQ55 : uv (CH2.retEx E' (CH2.ci_nx ci) [] R2) (EVar 55%nat) = n).
        { unfold n, uv, PB.uv. destruct AGR as [AGR0 _]. cbn [edenot]. rewrite <- (AGR0 55%nat) by lia. reflexivity. }
        rewrite EQ55.
        apply (TXT_agree (sp - 148) n M' M2); [lia | unfold hl_ceil in *; lia | | exact HGR | exact HT'].
        intros a Ha. apply HFB. rewrite L5.unsigned_lit by (unfold hl_ceil in *; lia).
        intros rg Hrg. destruct Hrg as [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; unfold PML.TP, PML.STRTOD_SCR_V in *; unfold hl_ceil in *; lia. }
    destruct (Z.eqb_spec pc PMFX.PC_DUMP_BUFFER) as [->|Hne4].
    { cbv iota in X.
      apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 Xs]. apply Z.eqb_eq in X1. apply Nat.eqb_eq in Xk.
      unfold sinkj in Xs. apply andb_prop in Xs as [Xj0 Xs].
      assert (Hret : CH2.ret_of G.RETS i kk = Some (ret_cut i kk)) by (unfold ret_cut in *; destruct (CH2.ret_of G.RETS i kk); [reflexivity | discriminate Xj0]).
      destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xs].
      destruct (db_chk (LV i) c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate Xs].
      unfold db_chk in Hchk.
      lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
      apply andb_prop in Hb as [Hb Xcell]. apply andb_prop in Hb as [Hb R2X]. apply andb_prop in Hb as [Hb R13]. apply andb_prop in Hb as [Hb R12]. apply andb_prop in Hb as [R10 R11].
      apply expr_eqb_eq in R10. apply expr_eqb_eq in R11. apply expr_eqb_eq in R12. apply expr_eqb_eq in R13. apply expr_eqb_eq in R2X.
      apply (FXKU.strans_leaf_okN L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K DEF0
               S2 Hobj W_S2 S2E 0 eq_refl OADDR PMFX.PC_DUMP_BUFFER DB_SCR (fun pay => 1 <= pay <= 27) (fun _ _ => True) None i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj X1 Hchk).
      - intros; exact I.
      - intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF. exact (proj1 (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF)).
      - intros E R1 M1 m1 E' R' M' cr1 fx' HAt HA HX Hag HLF CF HINV HH1 HSC HFP CONT.
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (_ & _ & HIMG).
        destruct HX as (_ & HP & HT).
        assert (HP0 : ESBU.s_len g1 - len0 = 0) by (dik i kk Xk; cbn [phase] in HP; exact HP).
        assert (HLV : exists nv, LV i = S nv) by (dik i kk Xk; eexists; reflexivity).
        destruct HLV as (nv & HLV).
        unfold text in HT. rewrite HLV in HT.
        pose proof CF as [HA' HR Hreq (Q1 & Q2 & Q3 & Q4 & Q5) HK [Hra' Hraok'] (Hsp' & Hc1 & Hs0 & Hc2) Hstk' Htp' HagE' Hden Hmeas].
        destruct HA' as (Hmo1 & Hbv1 & HagE1 & _ & Hfr1 & Hdf1).
        pose proof (TXTJ E E' E' R' M1 M' ps nv Hag (CC.env_agree_refl _ _) HagE' HLF HLV HT) as HT'.
        destruct HT' as (txt & Hgt & Hlen & Hln & Hbs & Hnul & Hdef).
        rewrite HLV in R11.
        set (n := uv E' (EVar (S nv))) in *.
        assert (U2' : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [AG _]; rewrite <- (AG 2%nat) by (unfold GT.NF; lia); exact U2).
        assert (U10' : bv_unsigned (ev E' 10) = dp) by (destruct HagE' as [AG _]; rewrite <- (AG 10%nat) by (unfold GT.NF; lia); exact U10).
        assert (U11' : bv_unsigned (ev E' 11) = SK) by (destruct HagE' as [AG _]; rewrite <- (AG 11%nat) by (unfold GT.NF; lia); exact U11).
        rewrite Hreq in HR.
        assert (CSP : CH2.ci_csp ci = -160).
        { pose proof (HR 2%bv) as G2. unfold sr_get in G2. change (bv_eqb (2%bv : bv 5) 0) with false in G2. cbv iota in G2. change (ridx 2%bv) with 2%nat in G2. rewrite R2X, Hsp' in G2.
          apply (f_equal bv_unsigned) in G2. rewrite (CL5.u_lin E' _ (sp - 160)) in G2; [| unfold XCE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. rewrite u64_of_Z in G2 by (unfold hl_ceil in *; lia). lia. }
        assert (Ga0 : getr R' 10%bv = Z_to_bv 64 (sp - 148)).
        { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite R10.
          apply PB.edenot_of_uv. unfold PB.uv. apply CL5.u_lin; [unfold BUFE; lin_eval; rewrite U2'; lia | unfold hl_ceil in *; lia]. }
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 n).
        { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite R11.
          unfold n, uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (Ga2 : getr R' 12%bv = Z_to_bv 64 dp).
        { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite R12. cbn [edenot]. rewrite <- U10'. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (Ga3 : getr R' 13%bv = Z_to_bv 64 SK).
        { rewrite (HR 13%bv). unfold sr_get. change (bv_eqb (13%bv : bv 5) 0) with false. cbv iota. change (ridx 13%bv) with 13%nat. rewrite R13. cbn [edenot]. rewrite <- U11'. symmetry. apply Z_to_bv_bv_unsigned. }
        rewrite LS in HK.
        assert (HU : PML.u64 M' SK S2).
        { pose proof (PB.has_ok E' M' _ _ HK Xcell) as HC0.
          apply (CL5.kword64_elim RSEGS E' M' _ _ SK S2 HC0); [unfold estart; cbn [a_base a_off edenot]; rewrite U11'; lia |].
          destruct HagE' as [AG _]. cbn [edenot]. rewrite <- (AG 32%nat) by (unfold GT.NF; lia). exact U32. }
        assert (HRM : len (PML.srep_chars (ESBU.s_rep g1)) + (n + 2) <= CLU) by (destruct HINV as [_ HL]; rewrite HL; unfold len0 in *; lia).
        destruct Hstk' as (T1 & T2 & T3 & T4 & T5). rewrite CSP in *.
        apply (DBOK (sp - 148) n dp txt (CH2.den E' (nth i G.BLS []) ++ LBo ++ []) cr1 (sp + -160) (CC.cp_pc cj) SK S2 kx bx (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
        { unfold PMFXT.DB_SCR, PMFXT.STRX_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *. unfold DB_SCR in *.
          split; [split; [exact Hra' | split; [exact Hraok' | split; [exact Hsp' | split; [rewrite Htp', (PmLayout.ly_tp L LAY); reflexivity |
                   split; [exact T1 | split; [lia | split; [lia | split; [exact T4 | exact T5]]]]]]]]|].
          split.
          { split; [exact Ga0|]. split; [exact Ga1|]. split; [exact Ga2|]. split; [lia|]. split; [exact Ga3|]. split; [lia|].
            exists S2. split; [exact HU|]. split; [lia|].
            split; [exact Hbs|]. split; [apply (L5.defined_sub M' (sp - 148) 100); [exact Hdef | lia | lia]|]. split; [exact Hlen|].
            split; [lia|]. split; [unfold hl_ceil in *; lia|]. split; [unfold PML.apart; lia | unfold PML.apart; lia]. }
          split; [exact HU|]. split; [lia|]. split; [lia|]. split; [unfold PML.apart; lia|]. split; [exact (proj1 HINV)|].
          split; [unfold PML.obj_on_stack; lia|]. split; [exact HIMG|]. split; [exact HSC | exact HRM]. }
        intros fx2 R3 M3 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRa0 & Hs2 & Hlen2 & HLB' & HLBk & HWc & HSC') HRP2 HPRES Hbv2 HH2.
        apply (CONT fx2 R3 M3 model2 LB' cr' LBk Wc HFP2); [| exact HRP2 | exact HPRES | exact Hbv2 | exact HH2].
        exists rep', pay. split; [lia|]. split; [exact I|]. split; [exact Hs2|]. split; [exact Hlen2|]. split; [exact HLB'|]. split; [exact HLBk|]. split; [exact HWc|].
        exact HSC'.
      - intros E R1 M1 m1 E' R' M' E2 M3 g' pay HAt HA HX HagE' Hag HLF Hag2 Hnx HPRES HINV2 Hslen HPay.
        destruct HX as (_ & HP & _). split; [exact HINV2|].
        dik i kk Xk; rcut; cbn [phase] in HP |- *; (split; [rewrite Hslen; lia | exact I]). }
    cbv iota in X.
    match type of X with context [FXK.fp_site ?sg pc] => destruct (FXK.fp_site sg pc) as [hv|] eqn:Hfs end.
    + apply andb_prop in X as [X Xp4]. apply andb_prop in X as [X Xp0]. apply andb_prop in X as [X XLV]. apply andb_prop in X as [X Xk].
      apply andb_prop in X as [Xpc Xinl]. apply Z.eqb_eq in Xpc. apply Z.leb_le in Xp0. apply Z.ltb_lt in Xp4. apply Nat.eqb_eq in XLV. apply Nat.eqb_eq in Xk.
      unfold inlj in Xinl. apply andb_prop in Xinl as [Xj0 Xinl].
      destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate Xinl].
      apply andb_prop in Xinl as [Xinl Xbv]. apply andb_prop in Xinl as [Xchk Xbe].
      apply (FXKU.inl_leaf_okV L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
               G.CPS G.TAGS K heap_ok3 (fun _ _ _ _ _ _ H => H) i c kk ps pc (ret_cut i kk) cj 4 hv g1 M0c OKV IL Hcj Xchk Xbe Xbv).
      * rewrite LS, Xpc. exact (FXKU.fp_site_step RSEGS pc hv Xp0 Xp4 Hfs).
      * intros E E' R1 R' M1 M' m1 E2 HAt HA HX Hag HLF Hag2.
        destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HA HX Hag HLF) as (HINV & HagE' & _).
        destruct HX as (_ & HP & HT). split; [exact HINV|]. split.
        -- dik i kk Xk; rcut; cbn [phase] in HP |- *; lia.
        -- unfold text in HT |- *. rewrite XLV. case_eq (LV i); [intros _; exact I|]. intros n HLV. rewrite HLV in HT.
           exact (TXTJ E E' E2 R' M1 M' ps n Hag Hag2 HagE' HLF HLV HT).
    + apply andb_prop in X as [X Xk]. apply andb_prop in X as [X1 X10]. apply Nat.eqb_eq in Xk.
      intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
      destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt OKV HAmb HX Hag HLF) as (HINV & HagE'0 & _).
      assert (DEFC : L5.defined M0c (sp - 9200) 9200) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
      apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
               (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
               9200 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV r Hra Hraok heap_ok3 RETPC i c kk ps pc ret_at IL X1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
      intros HRP HP HA' HagE'. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & _ & _).
      destruct HX as (_ & HPH & _).
      assert (HP2 : L5C.hpres L LBo sp 9200 W M M').
      { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
      assert (HPAY : 1 <= ESBU.s_len g1 - len0 <= 27) by (dik i kk Xk; cbn [phase] in HPH; lia).
      assert (Ga0 : PML.a0 R' 1).
      { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (ELit 1) HLF X10) as G10.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). unfold PML.a0. rewrite G10. reflexivity. }
      apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | exact HP2 | exact Hbv1 |].
      * exists (ESBU.s_rep g1), (ESBU.s_len g1 - len0). destruct HINV as [Hs Hl].
        split; [lia|]. split; [exact Ga0|]. split; [exact Hs|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
      * unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL, BLS0 in HH1. cbn [CH2.den map app] in HH1. exact HH1.
  - reflexivity.
  - rewrite LS.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2].
    + e_range. + e_range. + e_range. + e_align OS3.
    + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj.
    + e_unk.
  - apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M 0%nat E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [split; [exact Hsink | reflexivity] | split; [cbn [ESBU.s_len phase]; lia | exact I]]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|exact Hcred].
    unfold CH2.cur, CH2V.LBr. cbn [nth G.BLS CH2.den map app]. rewrite GBL. exact HH.
  - exact Hfp.
Qed.
End DtoaFalseOk.
End DFXU.
Print Assumptions DFXU.dtoa_false_x_ok.
