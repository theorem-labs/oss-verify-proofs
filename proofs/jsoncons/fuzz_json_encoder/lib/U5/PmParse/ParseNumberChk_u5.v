(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSpecs_u5 ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseSums2_u5 ParseSums2X_u5 ParseBridgesX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_pn_xsrc_T_u5 Cut_pn_xsrc_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Numbers; @BinNums; @Zpos]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_APPEND_RANGE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_SET_EC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_END_INT]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @PC_END_FRAC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EVar]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @esub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @WEND]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @JV]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @kind]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Corelib; @Init; @Datatypes; @false]; [@Corelib; @Init; @Logic; @eq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @kind_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @KPre]; [@Corelib; @Init; @Logic; @eq_refl]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @KApp]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Logic; @False_ind]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @KSetEc]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @KEnd]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @Lists; @List; @find]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @G; @RETS]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SETEC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @APPR]; [@Corelib; @Init; @Datatypes; @orb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @ENDI]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @ENDF]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Lists; @ListDef; @map]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Lists; @ListDef; @seq]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @Lists; @List; @forallb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @nl_step]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @zseq]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutOps; @CX; @range3]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAutoX; @CAX; @cell_at]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @Pb]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Datatypes; @None]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegPlan; @SGP; @region]; [@Corelib; @Init; @Datatypes; @andb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SCR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cutpoint]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @stack_reg_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @pobj_reg_eqb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_F]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @blocks]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pvals]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @blk2]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pview]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SBx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SLEN]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SCAP]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_st]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_more]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_done]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @DONE]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_sst]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SST]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_level]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @LVL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_wptr]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SEG]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_wend]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @prove]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_nst]; [@Corelib; @Init; @Datatypes; @pair]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_know]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @post_spec]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @cells16]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SegRun; @SR; @ps_cells]; [@Corelib; @Lists; @ListDef; @nth]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutAuto; @CA; @ps_reglist]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @exit_base_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @GT; @NF]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @RETPC]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @all_regs_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @foot_pre_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @blocks_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutCert; @CC; @cp_nx]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @G; @BLS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @view_chk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @Eb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges_u5; @PB; @has]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @OBJ_JSON_CATEGORY]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseBridges2_u5; @PB2; @pv_size]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @SIZE0]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @BX]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @eadd]; [@Corelib; @Init; @Nat; @sub]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @NCS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @foot_end_chk]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @ghost_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @CURJ]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @Vb]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @nstc_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmLibDefs_u5; @PML; @VT_VISITOR]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KUnk]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @WLEN]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @sz_of]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @expr_vars_lt]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @heap_chk3]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @G; @HDECL]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @G; @CPS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @G; @TAGS]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CutCert; @CutHeap2; @CH2; @leaves_all]; [@OssFuzzTheorems; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @PmParse; @ParseNumberChk_u5; @PNC; @leaf_chk]].

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PNC.
Module G := Cut_pn_xsrc_u5.
Module GT := Cut_pn_xsrc_T_u5.
Definition RETPC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,0|B09ecc;").
Definition APPR : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'1").  Definition SETEC : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'2").  Definition ENDI : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'3").  Definition ENDF : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'4").
(* [comment removed for export] *)
Definition Pb : expr := EVar 10.  Definition SEG : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5};").  Definition Vb : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}<").  Definition Eb : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}=").
Definition WLEN : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}P").  Definition BX : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}Q").  Definition K0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}R").  Definition SIZE0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}S").  Definition P0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}T").
Definition SBx : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}U").  Definition SLEN : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}V").  Definition SCAP : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}W").
Definition LVL : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}X").  Definition SST : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}Y").  Definition NST0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}Z").  Definition DONE : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}[").
Definition JV : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,5}^8").                       (* [comment removed for export] *)
Definition WEND : expr := APC.eadd SEG WLEN.
Definition CURJ : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'6'7'8").            (* [comment removed for export] *)
Definition SCR : Z := 11248.      (* [comment removed for export] *)
Definition ENDNUM_SCR : Z := 11136.                     (* [comment removed for export] *)

Inductive kind : Set := KPre | KApp | KSetEc | KEnd.
Definition kind_eqb (a b : kind) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+9$b;R+9-9RN$a;R+9+:#24-9RN$b;R+9+:#14,;,<,<,<-9RN$b;R+9+:#14,<,;,<,<-9RN$b;R+9+:#14,<,<,;,<-9RN$b;R+9+:#14,<,<,<,;").
Lemma kind_eqb_eq : forall a b, kind_eqb a b = true -> a = b.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S=0!2'>,?,A$e;R+:-:RN$b;R+:w#12+C+D!2'>,?,G!2'>,?,H!2'>,A,?!2'>,A,G!2'>,A,H!2'>,G,?!2'>,G,A!2'>,G,H!2'>,H,?!2'>,H,A!2'>,H,G$a;R+9-9RN$k;R+9%b;R+9%~R!3+=+:!2'>#2#1,;!3+=+9#3#2#14$b;R+9-9RN$k;R+9%~R!3+=+:!2'>,?#1,;!3+=+9,?#2#14$H;R!3+=+:!2'>,?,?,;!2,@+9,?$H;R!3+=+:0,;&H0;R!6'B+:01,E,;#1+C!2'F!3+=+9,?,A#1$H;R!3+=+:2,;&H0;R!6'B+:21,E,;#1+C!2'F!3+=+9,?,G#1$H;R!3+=+:3,;&H0;R!6'B+:31,E,;#1+C!2'F!3+=+9,?,H#1$b;R+9-9RN$k;R+9%~R!3+=+:!2'>,A#1,;!3+=+9,A#2#14$H;R!3+=+:4,;&H0;R!6'B+:41,E,;#1+C!2'F!3+=+9,A,?#1$H;R!3+=+:!2'>,A,A,;!2,@+9,A$H;R!3+=+:5,;&H0;R!6'B+:51,E,;#1+C!2'F!3+=+9,A,G#1$H;R!3+=+:6,;&H0;R!6'B+:61,E,;#1+C!2'F!3+=+9,A,H#1$b;R+9-9RN$k;R+9%~R!3+=+:!2'>,G#1,;!3+=+9,G#2#14$H;R!3+=+:7,;&H0;R!6'B+:71,E,;#1+C!2'F!3+=+9,G,?#1$H;R!3+=+:8,;&H0;R!6'B+:81,E,;#1+C!2'F!3+=+9,G,A#1$H;R!3+=+:!2'>,G,G,;!2,@+9,G$H;R!3+=+:9,;&H0;R!6'B+:91,E,;#1+C!2'F!3+=+9,G,H#1$b;R+9-9RN$k;R+9%~R!3+=+:!2'>,H#1,;!3+=+9,H#2#14$H;R!3+=+::,;&H0;R!6'B+::1,E,;#1+C!2'F!3+=+9,H,?#1$H;R!3+=+:;,;&H0;R!6'B+:;1,E,;#1+C!2'F!3+=+9,H,A#1$H;R!3+=+:<,;&H0;R!6'B+:<1,E,;#1+C!2'F!3+=+9,H,G#1$H;R!3+=+:!2'>,H,H,;!2,@+9,H").
Qed.
Definition kind_of (j : nat) : kind := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S30!2+K+I+I!2+K0+I!2+K1+L$j;R+I-JRN$x;R!1+J2+9!3'M2$r;R2-KRN$r;R!2+K1+L+:#11$p;R1$z;R+L-KRN$p;R!2+K0+I+:#21$p0;R0$n;R+I-KRN$p0;R!2+K+I+I+:#21$j';R+I$n0;R+I!2'N#8#2'O2$p;R2-KRN$p;R!2+K1+L+9#11$p0;R1$pc;R+L-KRN$p0;R!2+K0+I+9#21$p1;R0$n;R+I-KRN$p1;R!2+K+I+I+9#21$n0;R+I$n1;R+I-:RN$~R+:+9!2'P#5'Q2,G-:RN$~R+:+9!2'P#5'R2,A-:RN$~R+:+9!2'S!2'P#5'T!2'P#5'U2,H,?,?").

(* [comment removed for export] *)
Definition cut_states (i : nat) : option (list Z) :=
  nth i [None; Some [0]; Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7]; Some [3]; Some [4]; Some [1; 2]; Some [7]; Some [1]; Some [4]; Some [1; 2]; Some [7];
         None; None; None; None; None; (* [comment removed for export] *) Some [1]; Some [1; 2]; Some [3]; Some [4]; Some [5]; Some [6]; Some [7]] None.
Definition entry_states (c : Z) : list Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1,0|10;!1,Y+L$c;R+L-:RN$~R+:!1+V+L!2'P#102!3,W+L!1,0,X!3,W+L01!3,W+L#11").       (* [comment removed for export] *)
Definition nst_ok (c k : Z) : bool := (Z.eqb k c || (Z.eqb c 2 && Z.eqb k 1))%bool.   (* [comment removed for export] *)
Definition final_ok (k : Z) : bool := existsb (Z.eqb k) [1; 2; 4; 7].
Definition zseq (lo hi : Z) : list Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$lo;R+L$hi;R+L!4'Z+I+L$n;R+I!2'[#3!1'\#1!2'^0,^1!1'^2!2'[!2'^3#1#2!1,0,X").
Definition step_chk (Si : list Z) (lo hi : Z) (okf : Z -> bool) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$Si;R!1+V+L$lo;R+L$hi;R+L$okf;R%~R+L+:!3'^4+L$v;R+L!3'^4+L$k;R+L-JRN$x;R!1+J+L+:!2'^5#1#22$k';R+L!1#4#1,<#5!2'^6#3#2").
(* [comment removed for export] *)
Definition rng_is (cells : list kentry) (e : expr) (v : Z) : bool := match CX.range3 cells e with Some (lo, hi) => (Z.eqb lo v && Z.eqb hi v)%bool | None => false end.
Definition lo_ge (cells : list kentry) (e : expr) (v : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!2+K+L+L$cells;R!1+V+^7$e;R+^8$v;R+L-JRN$x;R!1+J0+:!2'^9#3#22$p;R0-KRN$p;R!2+K+L+L+:#11$lo;R+L$z;R+L!2'^:#4#2,<").
(* [comment removed for export] *)
Definition named_at (cells : list kentry) (cur : expr) : option (saddr * expr * Z * Z) :=
  match find (fun X => match X with KWord a 1 _ => rng_is cells (APC.esub (APC.eaddz (a_base a) (a_off a)) cur) 0 | _ => false end) cells with
  | Some (KWord a 1 v) => match CX.range3 cells v with
                          | Some (lo, hi) => if (Z.leb 0 lo && Z.leb hi 255)%bool then Some (a, v, lo, hi) else None
                          | None => None end
  | _ => None
  end.
(* [comment removed for export] *)
Definition content_chk (i : nat) (cells : list kentry) (tgt : expr) (okf : Z -> bool) : bool :=
  match cut_states i with
  | None => false
  | Some Si =>
      if rng_is cells (APC.esub tgt CURJ) 0 then forallb okf Si
      else if (rng_is cells (APC.esub tgt CURJ) 1 && (lo_ge cells JV 1 || (rng_is cells (APC.esub WLEN JV) 0 && lo_ge cells WLEN 1)) && PB.has cells (KBlob (SA SEG 0) WLEN 1))%bool then
        match named_at cells CURJ with Some (_, _, lo, hi) => step_chk Si lo hi okf | None => false end
      else false
  end.
Definition lit_nst (cells : list kentry) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1+J+L!1,^>+L$cells;R!1+V+^7-JRN$x;R!1+J+^80!4'^;#1'^<!1,0|752;}12$e;R+^8-^8RN$e;R+^80#18$c;R+L!2,^=+L#1$n;R+I1$op;R+^?$a;R+^8$b;R+^81$op;R+^?$a;R+^8$b;R+^81$op;R+^@$a;R+^8$b;R+^81$op;R+^@$a;R+^8$b;R+^81$sx;R+:$lo;R+I$n;R+I$e0;R+^81$sx;R+:$k;R+I$i;R+L$n;R+I11").

Definition isSome {A} (o : option A) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S01<scd;$A;R{cd;$o;R!1+J#1-JRN$o;R!1+J#2+:#12$a;R#2,;,<").
Definition stack_reg_eqb (r : SGP.region) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!2+K+^8+L$r;R'^A-KRN$r;R!2+K0+^8+:#11$p;R0$len;R+^8-KRN$p;R!2+K+^8+L+:#21$b;R+^8$lo;R+L!2'^B!2'^B!2'^C#2!1,5}2!2'P#1!1'^D'^E!2'^C#3!1,^F'^E").
Definition pobj_reg_eqb (r : SGP.region) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!2+K+^8+L$r;R'^A-KRN$r;R!2+K0+^8+:#11$p;R0$len;R+^8-KRN$p;R!2+K+^8+L+:#21$b;R+^8$lo;R+L!2'^B!2'^B!2'^C#2'^<!2'P#1,^G!2'^C#3!1,^F!1,0|810;").
Definition foot_pre_chk (c : CC.cutpoint) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+^H!3'^4'^A$r;R'^A!2'S!1'^I#1!1'^J#1!1'^K#1").
Definition foot_end_chk (c : CC.cutpoint) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+^H!3'^4'^A'^I!1'^K#1").

(* [comment removed for export] *)
Definition cells16 (cells : list kentry) : list kentry :=
  match CAX.cell_at cells Pb 210 1, know_byte_lit PML.RSEGS cells Pb 210, know_byte_lit PML.RSEGS cells Pb 211 with
  | None, Some b0, Some b1 => KWord (SA Pb 210) 1 (ELit b0) :: KWord (SA Pb 211) 1 (ELit b1) :: cells
  | _, _, _ => cells
  end.

(* [comment removed for export] *)
Definition blk2 (BL : CA.blocks) : option (expr * expr) :=
  match BL with [(pe, ce); (sb, sc)] => if (expr_eqb sb SBx && expr_eqb sc SCAP)%bool then Some (pe, ce) else None | _ => None end.
Definition view_chk (more_lit : Z) (cells : list kentry) (BL : CA.blocks) : option (expr * expr * PB2.pvals) := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!2+K+^8+^8!2+K0+^M!1+J1!1,^>1$more_lit;R+L$cells;R!1+V+^7$BL;R'^L-JRN$x;R!1+J02!1'^N#12$p;R0-KRN$p;R!2+K+^8+^82#11$pe;R+^8$ce;R+^8-JRN$x;R!1+J+^M2!7'^O#5'^<#2#1'^P'^Q'^R2$pv;R+^M-:RN$~R+:2!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'^C!1'^S#1!1,^F!1,0|41;!2'^C!1'^T#1!1,^F#7!2'^C!1'^U#1'^V!2'^C!1'^W#1'^X!2'^C!1'^Y#1'^Z!2'^C!1'^[#1'^\!2'^C!1'_0#1'7!2'_1#6!3,_2!1'_3#1,^G!1,0|23;2!2,^=1!4,_40+^M!4,_4+^8+^8#3#2#1333").
Definition sz_of (c : CC.cutpoint) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+^H-JRN$x;R!1+J+^8+^8!4'^;!1'_5#1'^<!1,0|768;}82$e;R+^8#1!1,^F,^G").
Definition nstc_of (c : CC.cutpoint) : option expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+^H!4'^;!1'_5#1'^<!1,0|752;}1").

(* [comment removed for export] *)
Definition exit_pre_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=      (* [comment removed for export] *)
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.ltb 53 (CC.cp_nx c) &&
   match view_chk 1 cells (nth i G.BLS []), cut_states i with
   | Some (pe, ce, pv), Some Si =>
       match PB2.pv_nst pv with
       | ELit cn => (Z.leb 0 cn && Z.leb cn 7 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && expr_eqb pe P0 && expr_eqb (PB2.pv_size pv) SIZE0 && forallb (nst_ok cn) Si
                     && PB.prove cells (KRange (APC.esub WLEN JV) 0 0) && PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 0)
                     && PB.prove cells (KRange (APC.esub BX SIZE0) 0 67108864))%bool
       | _ => false
       end
   | _, _ => false
   end)%bool.
Definition exit_app_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=      (* [comment removed for export] *)
  let cells := SR.ps_cells ps in let a0e := nth 10 (CA.ps_reglist ps) (ELit 0) in
  (PB.exit_base_chk GT.NF RETPC c ps && CH2.all_regs_chk ps && foot_pre_chk c && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) &&
   match view_chk 1 cells (nth i G.BLS []), nstc_of c with
   | Some (pe, ce, pv), Some (ELit cn) =>
       (Z.leb 0 cn && Z.leb cn 7 && PB.has cells (KWord (SA Eb 0) 4 (ELit 0)) && expr_eqb (PB2.pv_nst pv) (ELit cn) && expr_eqb (PB2.pv_size pv) (sz_of c) && APC.expr_vars_lt (CC.cp_nx c) (sz_of c)
        && PB.prove cells (KRange (APC.esub a0e SEG) 0 16384) && PB.prove cells (KRange (APC.esub WEND a0e) 0 0)
        && PB.prove cells (KRange (APC.esub (APC.esub a0e SEG) (APC.esub (sz_of c) SIZE0)) 0 0)
        && PB.prove cells (KRange (APC.esub BX (sz_of c)) 0 67108864))%bool
   | _, _ => false
   end)%bool.
Definition exit_setec_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S90!2+K+^8+^8!4'_9'^L#5'_B!1,Y0!2+K0+^M}4|30;}8|>0000;!1,06!2'6'7#8$i;R+I$c;R+^H$ps;R+_6&cells;R!1'_7!1'_8#1!1+V+^7&a0e;R!4'_9+^8}:!1'_:#2!1,^F,^G+^8!2'^B!2'^B!2'^B!2'^B!4'_;'_<'_=#4#3!1'_>#3!1'_?#4!2'_@!1'_A#41-JRN$x;R!1+J2+:!3'_C,^G#212$p;R2-KRN$p;R!2+K0+^M+:#11$p0;R0$pv;R+^M-KRN$p0;R!2+K+^8+^8+:#21$pe;R+^8$ce;R+^8-JRN$x;R!1+J+^8+:!4'^;#7'_D,^G32$e;R+^8-^8RN$e;R+^8+:#18$code;R+L!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'^:!1,0,X#1!2'^:#1!1,0|4f;!2'_E#9!3,_F!2,_G'_D!1,045!1,^F'_H!2'^C!1'_I#5'_J!2'_1#9!3,_2!2'6#8'^\,^G7!2'_1#9!3,_28,^G7!2'_1#9!3,_2!2'6'_K!2'_L'_J8,^G!1,0|J0000000;$n;R+I,<$op;R+^?$a;R+^8$b;R+^8,<$op;R+^?$a;R+^8$b;R+^8,<$op;R+^@$a;R+^8$b;R+^8,<$op;R+^@$a;R+^8$b;R+^8,<$sx;R+:$lo;R+I$n;R+I$e0;R+^8,<$sx;R+:$k;R+I$i0;R+L$n;R+I,<,<,<").
Definition ghost_of (c : CC.cutpoint) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+^H!2'_M!2'_M!1'_A#1'_N}5").
Definition exit_end_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20}:!1'_A#4$i;R+I$c;R+^H$ps;R+_6&cells;R!1'_8#1!1+V+^7&a0e;R!4'_9+^80!1'_:#2!1,^F,^G+^8!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!4'_;'_<'_=#4#3!1'_>#3!1'_O#4!2'_@1!4'_9'^L#5'_B!1,Y!2+K+^8+^8!2'_P!1'_Q#41!2'_P}^81!2'_1#2!3,_2!2'6#1'_R,^G,^G").

(* [comment removed for export] *)
Definition app_leaf_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool :=
  let cells := SR.ps_cells ps in let regs := CA.ps_reglist ps in
  let a1e := nth 11 regs (ELit 0) in let a2e := nth 12 regs (ELit 0) in
  (expr_eqb a1e SEG && PB.has cells (KBlob (SA SEG 0) WLEN 1) && Nat.ltb 53 (CC.cp_nx c)
   && match blk2 (nth i G.BLS []) with Some (pe, ce) => expr_eqb pe P0 | None => false end
   && APC.expr_vars_lt (CC.cp_nx cj - APC.NCS - 2) a2e && Nat.leb GT.NF (CC.cp_nx cj - APC.NCS - 2)
   && match CAX.cell_at cells Pb 232 8 with Some se => (expr_eqb se SIZE0 && expr_eqb (sz_of cj) (PSU.eadd se (PSU.esub a2e a1e)))%bool | None => false end
   && match CAX.cell_at cells Pb 210 1, nstc_of cj with
      | Some (ELit cn), Some (ELit cn') => (Z.eqb cn cn' && Z.leb 0 cn && Z.leb cn 7 && content_chk i cells a2e (nst_ok cn))%bool
      | Some (EVar v), Some (EVar v') => (Nat.eqb v v' && content_chk i cells a2e final_ok)%bool
      | _, _ => false
      end)%bool.
Definition end_leaf_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "SA0!1'_A#5!2+K+^8+^8!4'_9'^L#6'_B!1,Y1}:!1,^F,^G};}<}^8}5!2+K1+^M}4}8!1'_X#<!2'6'_R'^\|>0000;!1,0>!2'6'7'_R$i;R+I$c;R+^H$ps;R+_6$cj;R+^H&cells;R!1'_8#2!1+V+^7&regs;R!1'_:#3!1+V+^8!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'_@02!2'^C!4'_9+^83#14'^<!2'^C!4'_9+^85#14'_S!2'^C!4'_9+^86#14'_D!2'_P70!2'_P7!2'_M!2'_M!1'_A#3'_N8-JRN$x;R!1+J9+:!3'_C!1,0,X#222$p;R9-KRN$p;R!2+K1+^M+:#11$p0;R1$pv;R+^M-KRN$p0;R!2+K+^8+^8+:#21$pe;R+^8$ce;R+^8-JRN$x;R!1+J+^8+:!1'_T#:2$e;R+^8-^8RN$e;R+^8+:#18$z;R+L,<$n;R+I!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'^B!2'_E#9!3,_F!2,_G'_D,^G:4!2'_E#9!3,_F!2,_G'_S,^G;!1,^F'_U!2'_E#9!2,_V!2,_G'^\,^G'_W!2'^C!1'_I#5<!2'_Y!1'_A#<<!2'_1#9!3,_2=,^G?!2'_1#9!3,_2@,^G?!2'_1#9!3,_2!2'6=!2'6<'_J,^G,^G!2'_1#9!3,_2!2'6'_K!2'_L<@,^G!1,0|J0000000;$op;R+^?$a;R+^8$b;R+^8,<$op;R+^?$a;R+^8$b;R+^8,<$op;R+^@$a;R+^8$b;R+^8,<$op;R+^@$a;R+^8$b;R+^8,<$sx;R+:$lo;R+I$n;R+I$e0;R+^8,<$sx;R+:$k;R+I$i0;R+L$n;R+I,<,<,<").

(* [comment removed for export] *)
Definition goto_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in let jj := CC.esubstL GT.NF s JV in
  (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KPre && foot_pre_chk c && Nat.ltb 0 j && Nat.ltb j 29 && (Nat.eqb i 0 || Nat.ltb 53 (CC.cp_nx c)) &&
   match cut_states j with
   | None => true
   | Some Sj =>
       if Nat.eqb i 0 then
         match CX.range3 cells NST0 with
         | Some (cn, cn') => (Z.eqb cn cn' && forallb (fun k => existsb (Z.eqb k) Sj) (entry_states cn) && rng_is cells (APC.esub WLEN jj) 0)%bool
         | None => false
         end
       else content_chk i cells (APC.esub WEND jj) (fun k => existsb (Z.eqb k) Sj)
   end)%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_chk i c ps j s
  | CC.TOther pc =>
      if Z.eqb pc RETPC then
        match kind_of i with KPre => exit_pre_chk i c ps | KApp => exit_app_chk i c ps | KSetEc => exit_setec_chk i c ps | KEnd => exit_end_chk i c ps end
      else
        (foot_pre_chk c && Z.eqb (SR.ps_pc ps) pc &&
         match CH2.ret_of G.RETS i k with
         | Some j => match nth_error G.CPS j with
                     | Some cj =>
                         if Z.eqb pc APPR then (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KApp && Nat.ltb 0 i
                                                && isSome (PB3.appendr_chk GT.NF G.HDECL Pb 224 SEG WLEN 132 c ps cj (nth i G.BLS []) (nth j G.BLS [])) && app_leaf_chk i c ps cj)%bool
                         else if Z.eqb pc SETEC then (kind_eqb (kind_of i) KPre && kind_eqb (kind_of j) KSetEc && match PB2.setec_chk GT.NF G.HDECL Eb 0 c ps cj (nth i G.BLS []) (nth j G.BLS []) with Some ci => Nat.leb GT.NF (CH2.ci_nx ci) | None => false end)%bool      (* [comment removed for export] *)
                         else if (Z.eqb pc ENDI || Z.eqb pc ENDF)%bool then
                           (kind_eqb (kind_of i) KApp && kind_eqb (kind_of j) KEnd
                            && isSome (PBX.ptrans_chkx GT.NF G.HDECL Eb 0 Pb 0 ENDNUM_SCR Vb PML.LIT_LO 12 c ps cj (nth i G.BLS []) (nth j G.BLS [])) && end_leaf_chk i c ps cj)%bool
                         else false
                     | None => false end
         | None => false end)%bool
  end.
End PNC.

Lemma heap_ok3 : CH2.heap_chk3 PNC.GT.NF PNC.G.HDECL PNC.G.BLS PNC.G.CPS PNC.G.TAGS = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,@+:,;!3+=+:!5'_Z'_<'_['_B'_\'`0,;").
Qed.
Lemma leaf_ok : CH2.leaves_all PNC.G.CPS PNC.G.TAGS PNC.leaf_chk = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,@+:,;!3+=+:!3'`1'_\'`0'`2,;").
Qed.
