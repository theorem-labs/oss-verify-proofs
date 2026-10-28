(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MA_"; "MB"; "MM0"; "OD_meta"; "pA"; "vptr"; "pB"; "OD_act"; "OD_bnc"; "mam"; "od_ok_at"; "mptr"; "OD_mem"; "vbits"; "vmem"; "OD_ctz"; "OD_got"; "OD_guard"; "OD_sct"; "obj_of"; "O_stk"; "e_bncidx"; "mbyte"; "vavail"; "vfreed"; "member"; "od_range"; "pM0"; "zl1"; "zr1"; "MC"; "vbyte"; "e_ctz"; "od_ok"; "zA"; "MP"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Corelib.Init.Datatypes"; "cons"; "app"; "option"; "Some"; "list"; "true"; "nil"; "bool"; "prod"; "pair"; "None"; "snd"; "fst"; "length"; "false"; "nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sobj"; "sprop"; "SAluW"; "SLit"; "sv"; "ss_facts"; "SAlu"; "rw"; "SPBranch"; "ss_objs"; "SExt"; "SPNot"; "smatch"; "FcsrFrm0"; "reg_sv"; "mkSS"; "ob_cells"; "rm"; "sfcsr"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_next"; "ss_pc"; "ss_resv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "LCtx"; "CTX_active"; "active_hd"; "CTX_bounces"; "loc_addr"; "Inv"; "alinks"; "ring_ok"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "sub"; "modulo"; "opp"; "to_nat"; "pow"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "MUsed"; "st_bounces"; "IRet"; "itree"; "lowbit"; "am_aidx"; "am_freed"; "IB"; "am_avail"; "am_last"; "am_maplen"; "am_mem"; "am_sc"; "class_size"; "ones"; "try_avail"; "znth"; "zset"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "callee_saved"; "pre_reg"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_AND"; "ALU_SLL"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "lfs"; "ST_R3sh"; "ST_R4nh"; "ST_R4nr"; "ST_R4sh"; "ST_R5nh"; "NXA"; "LT_R3sh"; "LT_R4nh"; "LT_R4nr"; "LT_R4sh"; "LT_R5nh"; "SA_R3sh"; "SA_R4nh"; "SA_R4nr"; "SA_R4sh"; "SA_R5nh"; "DT_R3sh"; "DT_R4nh"; "DT_R4nr"; "DT_R4sh"; "DT_R5nh"; "LA_R3shs"; "LA_R4nhs"; "LA_R4nrs"; "LA_R4shs"; "LA_R5nhs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "meta_locs"; "set_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT"; "e_maskA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sprop_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "HITP"; "oStkF";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR3sh.VR3sh"; "sR'"; "am1_B"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nr.VR4nr"; "sR'"; "s3V"; "s1V"; "am1_B"; "am1_A"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4sh.VR4sh"; "sR'"; "am1_B"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR4nh.VR4nh"; "sR'"; "am1_A"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G8.Mal_aslot_VR5nh.VR5nh"; "sR'"; "am1_A"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zholds"; "psupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "as_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_final"; "s4"; "s5"; "s6"; "step1"; "step2"; "step3"; "t_mask"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_VR4nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR4nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S34S32S6aS5eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S26S61Z0Vreq;A2S61S62Vreq;S74A2S7aVsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Vs;Vsc;A2S2dS6aVm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2dS6aVm0;A2S2aS6aVm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§1§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§1§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls4 := (@U.Mal_aslot__G1.Mal_aslot_I.cls4 s X sc Hsc m0 rest Rg).
Local Notation "§2§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§2§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12fS122VX;S34S32S6aS5eA2A1VU;S121Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1aS26S26S61Z0M0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S63G1Z100A2A2S26S25S5eS66G1Z20A2S72SaVs;Vm0;R1A3M2A1A3S27S25S5eS77G2A1G0A3A1S25S5eS17VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S72SaVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§3§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§4§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S26S61Z1000S8bQ40S42Vrho;PaA2A2M0A2S25S5eS66G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S26S61S127Z40S8bQ40S42Vrho;PfA2A2A2M0S67S12eZ0A1A1A2S61S67S69Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61S126VL;A1S62S8bQ40M0S42Vrho;PaA2A2S127Z40S8bG0S42Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§5§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§6§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§6§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;Vrd0;SbdS84VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S25S89Q40A1S31F_;Vwok0;SbeS84VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z60A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ecR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z20A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ccR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1aS25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S23VL;S78SaVs;Vm0;R1A3A1A2Z8A2A2A3S2dG1S8aG0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S62Z5a3d0Z369A2Vsc;A2A2A3S2dG1S8aG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S124S123Vrd0;S89Q40A1S2fL_;A2S125S122A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S123SbdS84VmW;A2SbeS84VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§7§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§1§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§8§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§8§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S25S5eVbnc;S7dS65Vsc;G0A2S6eVs;A1A2A3F_;").
Local Notation "§9§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§9§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S131S84VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2eSb9A1SbaOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§10§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§10§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§11§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§11§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§12§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§12§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§13§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§13§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§1§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§6§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§6§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§14§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§14§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§15§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§15§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§16§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§16§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§17§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§17§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§17§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§14§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§11§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§18§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§18§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§18§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§18§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§2§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§2§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§2§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S25SbbVvm;SbcVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2eSb9A1M0SbaVK;R2R1A2S26VKc;R3R2A2S26S25G0R3Vtr;A3S25SbaR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S47S84Vrho;S12dS12cA1S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 4%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S25S5eS75SaVs;Vm0;S3A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S27S25S5eS73SaVs;Vm0;S3A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S27S25S5eS73SaVs;Vm0;S1A3M0A1S7bS76G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S25S5eVmaskv;Sb2Vs;Vm0;S1A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Vs;S1cVm0;A1A2S2dS6bS6dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls4 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls4 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S100ScVs;Vm0;S3A3A2S2dS6bS6dS10bA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S100ScVs;Vm0;S1A3A2S2dS6bS6dSfeA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SffVq;A2S55S100Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S25S2eS5eA1S6eSffA1S6eVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S25S2cS6aA1S58SffVsc;A2S2dS6aS5Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S25S70S6cS32S2cS6aA1M0S6cA2M1A2S136Vsc;S1cVm0;A1Vam0;Vs;A4S6fS6cG1S33G0S6cS2dS6aS5Vs;Vm0;A2A2S100A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S25S6aS5Vs;Vm0;A2ScVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S100S5Vs;Vm0;A2A2S2dS6bS6dSfeA1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S137Vsc;S5Vs;Vm0;A2M1SfeS100A4S6fS6cG0S33S6aS6cG1S106A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S106S5Vs;Vm0;A2A2S2dS6bS6dSfeA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S138Vsc;S5Vs;Vm0;A2M1SfeS106A4S6fS6cG0S33S6aS6cG1SffA4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SffS5Vs;Vm0;A2A2S2dS6bS6dSfeA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S25S5eS139SfeA1Sb2Vs;Vm0;S1A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S135SffS5Vs;Vm0;A2SfeA3").
Lemma taR : ltac2:(tb__ "0|1|
S25S70S6cS32S5eS6cA2M0A2S7cVsc;Vs;A2S6fS6cG0S33S5eS6cS71Sb2Vs;Vm0;S1A3A1SfdA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S27S25S5eS71Sb2Vs;Vm0;S1A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S130VX;VU;Vs;Vsc;S71Sb2Vs;Vm0;S1A3A1SfdA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S25S2cS6aA1S58SfdVsc;A2S2dS6aS5Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SfdS5Vs;Vm0;A2A2S2dS6bS6dS132SfeA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S25S5eS79SfeA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SfdScVs;Vm0;S3A3A2S2dS6bS6dS10bA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SaeVs;S100S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SaeS100S106S30S54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SaeS106SffS30S54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
SaeVs;SffS2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|1|
S2aS0S11S2aS0S12S2aS0S8S60S6S3A1A1M0A1S2aS0S4S3S60S6S1fA1A1S60S6S1A1A1S60SfS3A1A1S60S18S3A1A1S60S19S3A1A1S60SeS3A1A1A7S2aS0S4S1G0S60S6S2A1A1S60SfS1A1A1S60S18S1A1A1S60S19S1A1A1S60SeS1A1A1A7S2aS0SdS1S60S20S1A1A1A2S2aS0S13S2aS0S10S2aS0S9S1S60PaaA1A2S30S0A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S25S2eS3bA1S44Sa0A1S2aS3bS15Sb7S0S3bS14S101A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R4nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40Sa0A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R4nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cS88S85S48S34S3fA1S2aS3bS15S30S3bA1A3S40Sa0A1S99S38A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S47S84VrhoW;S10dS33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4M0A4S47S84VrhoW;Sa0G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R4nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S25S2cS32S2eS32S3fS3fA2M0A1M1S2eS3cA1M2A2M3A1S12aSaaS95A2S2dG3S33G1G2S2aG0S33S3fS3fSb6S1A1S3aPabA1A4S30G0A1A3S35G1G2Sa5A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R4nh)). Qed.
Lemma swf_ST : swf ST_R4nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S25S31S80S3cS3cS82S3cS4eR1A1S40S95A1A3Lp;S35S2eS32S3fS3fA2A1S2eS3cA1Sa5A3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S25S31S80S3cSc1SbfA1S40S95A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S25S31S80S3cS129S40S95A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S95A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R4nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R4nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S25S5fS51S95A1S99A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R4nh 0 ST_R4nh.
Definition LT1 : sstate := lfs LT_R4nh 1 ST_R4nh.
Definition LT2 : sstate := lfs LT_R4nh 2 ST_R4nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S10aA1A2S103A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S108A1A2S104A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S109A1A2S105A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S103A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S104A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S105A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S103A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S104A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S105A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S101S103A2S102A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S101S104A2S10cA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S101S105A2S107A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S25S2eS0A1S102S2aS0S8S60S6S1A1A1A1S2aS0S4S1S60S6S3A1A1S60S6S2A1A1S60SfS1A1A1Sb3Sb5S1A1S60SeS1A1A1A7S30S0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S25S2eS0A1S107S2bS0S102S2aS0S9S1Sb4A2S30S0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S25S39S37S0VdsF;A2S37S0S101A2A3S0S7fS0R1VdsF;A3S28S22Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7fS0R2Sb1S101VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2eS0A1M0G0S0S7fS0R1Sb1R3R2A2A3S7fS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S92Vk;U3A2S25S2eS3bA1S44S93S9bVk;S95A3A1M0S2aS3bSc6S4bS83S3bS15G0A3A1A1S81S3bG0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S5eS52S93S9bVk;S95A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2eS3fA1S50S93S9bVk;S95A3A1S85A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S4dS4fS93S9bVk;S95A3A1S48A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2cS3fA1S53S93S9bVk;S95A3A1S34S3fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S3fS49S93S9bVk;S95A3ZaA2S21S60PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S5eS26S61Z1R1A2S61R1Z1fA2A2S25S31S86S68R2A1A1S2fA3S25S3fS49S93S9bVk;S95A3R3A2S87S68R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R4nh k ST_R4nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7fS3cS43S8fS3eZ1fA1S16S1A1A3S40S10aA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7fS3cS43S90S60PaaA1S3eZ0A1A3S40S108A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S1A1A3A1S40S108A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7fS3cS46S43S90S60PaaA1S3eZ0A1A3A1S40S109A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S1A1A3A1S40S109A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S25S6cS134SffS5Vs;Vm0;A2M1SfeA3S133SffG1SfeA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2SaeVs;SfdS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3G1A3G1A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SaeVs;SfdS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3G1A3G1A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M2S2aS54S56S62S59S65Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S25S2eS5eA1S6eSfdA1S7eS65Vsc;G0A2S65Vbnc;Z1A2S6eVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdS4S1S60S6S3A1A1S60S6S2A1A1S60SfS1A1A1Sb3Sb5S1A1S60SeS1A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdS8S60S6S1A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdS9S1Sb4A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1S102A3S26S7fS0R2S103A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1S10cA3S26S7fS0R2S104A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S0S7fS0R1S107A3S26S7fS0R2S105A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SfdR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M1G0A3G1A3A3A3S29S0S0S26S7fS0R1S102A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S63G3S35S5eS5eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M1S2aS54S56S62S59S65Vsc;Z7A2A2A1G0A3A3G1A3A3A3S29S0S0S26S7fS0R1S107A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S63G3S35S5eS5eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R4nh : ltac2:(tb__ "0|0|
VTR;Z0S12bS84VK;Sa0VrhoW;A4Sc5VX;VU;S121Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R4nh)).
  { apply (seg_run 300 SA_R4nh LA_R4nh _ rhoW eq_refl eq_refl runA_R4nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R4nh _ SA_R4nh LfA LA_R4nh_shape HinA) in HSPA. change (lfs LA_R4nh 0 SA_R4nh) with LA_R4nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R4nhs ST_R4nh (e_maskA MA_) (snd DT_R4nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R4nh LT_R4nh _ rhoA ST_len ST_next runT_R4nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R4nh _ _ _ ST_R4nh Lf LT_R4nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nh 0 ST_R4nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nh 0 ST_R4nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nh 1 ST_R4nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nh 1 ST_R4nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nh 2 ST_R4nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nh 2 ST_R4nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR4nh.
End Mal_aslot_VR4nh.

Module Mal_aslot_VR3sh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR3sh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S34S32S6aS5eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S26S61Z0Vreq;A2S61S62Vreq;S74A2S7aVsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Vs;Vsc;A2S2dS6aVm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2dS6aVm0;A2S2aS6aVm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§19§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§19§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§19§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§19§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§20§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§20§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12fS122VX;S34S32S6aS5eA2A1VU;S121Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1aS26S26S61Z0M0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S63G1Z100A2A2S26S25S5eS66G1Z20A2S72SaVs;Vm0;R1A3M2A1A3S27S25S5eS77G2A1G0A3A1S25S5eS17VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S72SaVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§21§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§22§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§22§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§21§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S26S61Z1000S8bQ40S42Vrho;PaA2A2M0A2S25S5eS66G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S26S61S127Z40S8bQ40S42Vrho;PfA2A2A2M0S67S12eZ0A1A1A2S61S67S69Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61S126VL;A1S62S8bQ40M0S42Vrho;PaA2A2S127Z40S8bG0S42Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§23§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§23§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§24§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§22§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;Vrd0;SbdS84VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S25S89Q40A1S31F_;Vwok0;SbeS84VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z60A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ecR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z20A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ccR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1aS25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S23VL;S78SaVs;Vm0;R1A3A1A2Z8A2A2A3S2dG1S8aG0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S62Z5a3d0Z369A2Vsc;A2A2A3S2dG1S8aG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S124S123Vrd0;S89Q40A1S2fL_;A2S125S122A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S123SbdS84VmW;A2SbeS84VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§25§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§25§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§19§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§26§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§26§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§22§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S25S5eVbnc;S7dS65Vsc;G0A2S6eVs;A1A2A3F_;").
Local Notation "§27§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§27§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S131S84VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2eSb9A1SbaOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§28§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§28§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§29§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§29§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§30§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§30§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§31§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§31§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§19§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§24§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§24§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§32§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§32§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§33§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§33§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§34§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§34§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§35§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§35§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§35§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§32§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§29§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§36§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§36§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§36§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§36§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§20§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§20§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§20§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S25SbbVvm;SbcVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2eSb9A1M0SbaVK;R2R1A2S26VKc;R3R2A2S26S25G0R3Vtr;A3S25SbaR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S47S84Vrho;S12dS12cA1S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S25S5eS75SaVs;Vm0;S3A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S27S25S5eS73SaVs;Vm0;S3A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S25S5eS73SaVs;Vm0;S1A3M0A1S7bS76G0A1A1A3").
Hypothesis HVact : maskA MB <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S25S5eVmaskv;Sb2Vs;Vm0;S2A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Vs;S1cVm0;A1A2S2dS6bS6dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS7Vs;Vm0;A2A2Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS7Vs;Vm0;A2A2Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55ScaScVs;Vm0;S3A3A2S2dS6bS6dSd6A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55ScaScVs;Vm0;S1A3A2S2dS6bS6dSd1A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S25S2cS6bA1S55ScaScVs;Vm0;S2A3A2S2dS6bS6dSc8A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sc9Vq;A2S55ScaVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S25S2eS5eA1S6eSc9A1S6eVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Sc9Vsc;A2S2dS6aS7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S25S70S6cS32S2cS6aA1M0S6cA2M1A2S136Vsc;S1cVm0;A1Vam0;Vs;A4S6fS6cG1S33G0S6cS2dS6aS5Vs;Vm0;A2A2ScaA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S25S6aS5Vs;Vm0;A2ScVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55ScaS5Vs;Vm0;A2A2S2dS6bS6dSd1A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S25S70S6cS32S6aS6cA2M0A2S137Vsc;S5Vs;Vm0;A2Sd1ScaA4S6fS6cG0S33S6aS6cS7Vs;Vm0;A2Sd0A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sd0S7Vs;Vm0;A2A2S2dS6bS6dSc8A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S138Vsc;S7Vs;Vm0;A2M1Sc8Sd0A4S6fS6cG0S33S6aS6cG1Sc9A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_B. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sc9S7Vs;Vm0;A2A2S2dS6bS6dSc8A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S25S5eS139Sc8A1Sb2Vs;Vm0;S2A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S135Sc9S7Vs;Vm0;A2Sc8A3").
Lemma taR : ltac2:(tb__ "0|1|
S25S70S6cS32S5eS6cA2M0A2S7cVsc;Vs;A2S6fS6cG0S33S5eS6cS71Sb2Vs;Vm0;S2A3A1Sc7A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S27S25S5eS71Sb2Vs;Vm0;S2A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S130VX;VU;Vs;Vsc;S71Sb2Vs;Vm0;S2A3A1Sc7A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Sc7Vsc;A2S2dS6aS7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sc7S7Vs;Vm0;A2A2S2dS6bS6dS132Sc8A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S25S5eS79Sc8A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sc7ScVs;Vm0;S3A3A2S2dS6bS6dSd6A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sc7ScVs;Vm0;S1A3A2S2dS6bS6dSd1A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SaeVs;ScaS2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SaeScaSd0S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SaeSd0Sc9S30S54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
SaeVs;Sc9S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S2aS0S11S2aS0S12S2aS0S8S60S6S3A1A1M0A1S2aS0S4S3S60S6S2A1A1M1S60S6S1A1A1M2S60SfS3A1A1S60S18S3A1A1S60S19S3A1A1S60SeS3A1A1A7S2aS0S4S1G0G1S60SfS1A1A1S60S18S1A1A1S60S19S1A1A1S60SeS1A1A1A7S2aS0S4S2G2G0S60SfS2A1A1S60S18S2A1A1S60S19S2A1A1S60SeS2A1A1A7S2aS0SdS2S60S20S2A1A1A2S2aS0S13S2aS0S10S2aS0S9S2S60PaaA1A2S30S0A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S25S2eS3bA1S44S9fA1S2aS3bS15Sb7S0S3bS14ScbA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R3sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S9fA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R3sh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cS88S85S48S34S3fA1S2aS3bS15S30S3bA1A3S40S9fA1S99S38A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S47S84VrhoW;Sd8S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4M0A4S47S84VrhoW;S9fG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R3sh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S25S2cS32S2eS32S3fS3fA2M0A1M1S2eS3cA1M2A2M3A1S12aSa9S94A2S2dG3S33G1G2S2aG0S33S3fS3fSb6S2A1S3aPabA1A4S30G0A1A3S35G1G2Sa4A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R3sh)). Qed.
Lemma swf_ST : swf ST_R3sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S25S31S80S3cS3cS82S3cS4eR1A1S40S94A1A3Lp;S35S2eS32S3fS3fA2A1S2eS3cA1Sa4A3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S25S31S80S3cSc1SbfA1S40S94A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S25S31S80S3cS129S40S94A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S94A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R3sh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R3sh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S25S5fS51S94A1S99A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R3sh 0 ST_R3sh.
Definition LT1 : sstate := lfs LT_R3sh 1 ST_R3sh.
Definition LT2 : sstate := lfs LT_R3sh 2 ST_R3sh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sd5A1A2ScdA2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sd3A1A2SceA2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sd4A1A2ScfA2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14ScdA4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14SceA4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14ScfA4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4ScdA3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4SceA3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4ScfA3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1ScbScdA2SccA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1ScbSceA2Sd7A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1ScbScfA2Sd2A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S25S2eS0A1SccS2aS0S8S60S6S2A1A1A1S2aS0S4S2S60S6S1A1A1S60S6S3A1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7S30S0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S25S2eS0A1Sd2S2bS0SccS2aS0S9S2Sb4A2S30S0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S25S39S37S0VdsF;A2S37S0ScbA2A3S0S7fS0R1VdsF;A3S28S22Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7fS0R2Sb1ScbVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2eS0A1M0G0S0S7fS0R1Sb1R3R2A2A3S7fS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S92Vk;U3A2S25S2eS3bA1S44S93S9aVk;S94A3A1M0S2aS3bSc6S4bS83S3bS15G0A3A1A1S81S3bG0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S5eS52S93S9aVk;S94A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2eS3fA1S50S93S9aVk;S94A3A1S85A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S4dS4fS93S9aVk;S94A3A1S48A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2cS3fA1S53S93S9aVk;S94A3A1S34S3fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S3fS49S93S9aVk;S94A3ZaA2S21S60PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S5eS26S61Z1R1A2S61R1Z1fA2A2S25S31S86S68R2A1A1S2fA3S25S3fS49S93S9aVk;S94A3R3A2S87S68R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R3sh k ST_R3sh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7fS3cS43S8fS3eZ1fA1S16S2A1A3S40Sd5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7fS3cS43S90S60PaaA1S3eZ0A1A3S40Sd3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Sd3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7fS3cS46S43S90S60PaaA1S3eZ0A1A3A1S40Sd4A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Sd4A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S25S6cS134Sc9S7Vs;Vm0;A2M1Sc8A3S133Sc9G1Sc8A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2SaeVs;Sc7S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G2A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SaeVs;Sc7S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G2A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3S2aS54S56S62S59S65Vsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S25S2eS5eA1S6eSc7A1S7eS65Vsc;G0A2S65Vbnc;Z1A2S6eVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7S4S2S60S6S1A1A1S60S6S3A1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_B). split; [exact MT_R'|].
  pose proof (am_final_fields am1_B) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_B; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_B; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_B, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7S8S60S6S2A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7S9S2Sb4A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1SccA3S26S7fS0R2ScdA3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1Sd7A3S26S7fS0R2SceA3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S0S7fS0R1Sd2A3S26S7fS0R2ScfA3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc7R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2G0A3G2A3A3A3S29S0S0S26S7fS0R1SccA3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MM0)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2S2aS54S56S62S59S65Vsc;Z7A2A2A1G0A3A3G2A3A3A3S29S0S0S26S7fS0R1Sd2A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MM0)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R3sh : ltac2:(tb__ "0|0|
VTR;Z0S12bS84VK;S9fVrhoW;A4Sc5VX;VU;S121Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R3sh)).
  { apply (seg_run 300 SA_R3sh LA_R3sh _ rhoW eq_refl eq_refl runA_R3sh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R3sh _ SA_R3sh LfA LA_R3sh_shape HinA) in HSPA. change (lfs LA_R3sh 0 SA_R3sh) with LA_R3shs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R3shs ST_R3sh (e_maskA MB) (snd DT_R3sh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R3sh LT_R3sh _ rhoA ST_len ST_next runT_R3sh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R3sh _ _ _ ST_R3sh Lf LT_R3sh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sh 0 ST_R3sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sh 0 ST_R3sh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sh 1 ST_R3sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sh 1 ST_R3sh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R3sh 2 ST_R3sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R3sh 2 ST_R3sh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR3sh.
End Mal_aslot_VR3sh.

Module Mal_aslot_VR4nr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR4nr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S34S32S6aS5eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S26S61Z0Vreq;A2S61S62Vreq;S74A2S7aVsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Vs;Vsc;A2S2dS6aVm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2dS6aVm0;A2S2aS6aVm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§37§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§37§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§37§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§37§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls4 := (@U.Mal_aslot__G1.Mal_aslot_I.cls4 s X sc Hsc m0 rest Rg).
Local Notation "§38§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§38§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12fS122VX;S34S32S6aS5eA2A1VU;S121Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1aS26S26S61Z0M0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S63G1Z100A2A2S26S25S5eS66G1Z20A2S72SaVs;Vm0;R1A3M2A1A3S27S25S5eS77G2A1G0A3A1S25S5eS17VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S72SaVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§39§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§40§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§40§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§39§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S26S61Z1000S8bQ40S42Vrho;PaA2A2M0A2S25S5eS66G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S26S61S127Z40S8bQ40S42Vrho;PfA2A2A2M0S67S12eZ0A1A1A2S61S67S69Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61S126VL;A1S62S8bQ40M0S42Vrho;PaA2A2S127Z40S8bG0S42Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§41§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§41§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§42§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§40§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;Vrd0;SbdS84VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S25S89Q40A1S31F_;Vwok0;SbeS84VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z60A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ecR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z20A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ccR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1aS25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S23VL;S78SaVs;Vm0;R1A3A1A2Z8A2A2A3S2dG1S8aG0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S62Z5a3d0Z369A2Vsc;A2A2A3S2dG1S8aG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S124S123Vrd0;S89Q40A1S2fL_;A2S125S122A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S123SbdS84VmW;A2SbeS84VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§43§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§43§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§37§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§44§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§44§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§45§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§45§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§40§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S25S5eVbnc;S7dS65Vsc;G0A2S6eVs;A1A2A3F_;").
Local Notation "§46§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§46§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S131S84VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2eSb9A1SbaOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§47§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§47§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§48§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§48§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§49§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§49§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§50§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§50§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§37§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§51§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§51§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§42§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§42§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§52§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§52§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§53§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§53§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§54§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§54§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§55§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§55§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§56§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§56§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§56§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§52§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§48§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§57§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§57§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§57§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§57§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§38§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§38§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§38§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S25SbbVvm;SbcVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2eSb9A1M0SbaVK;R2R1A2S26VKc;R3R2A2S26S25G0R3Vtr;A3S25SbaR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S47S84Vrho;S12dS12cA1S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 4%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S25S5eS75SaVs;Vm0;S3A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S27S25S5eS73SaVs;Vm0;S3A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S27S25S5eS73SaVs;Vm0;S1A3M0A1S7bS76G0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S25S5eVmaskv;Sb2Vs;Vm0;S2A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Vs;S1cVm0;A1A2S2dS6bS6dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls4 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls4 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS7Vs;Vm0;A2A2Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdbScVs;Vm0;S3A3A2S2dS6bS6dSe8A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdbScVs;Vm0;S1A3A2S2dS6bS6dSddA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdbScVs;Vm0;S2A3A2S2dS6bS6dSdcA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdaVq;A2S55SdbVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S25S2eS5eA1S6eSdaA1S6eVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S25S2cS6aA1S58SdaVsc;A2S2dS6aS7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S25S70S6cS32S2cS6aA1M0S6cA2M1A2S136Vsc;S1cVm0;A1Vam0;Vs;A4S6fS6cG1S33G0S6cS2dS6aS5Vs;Vm0;A2A2SdbA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S25S6aS5Vs;Vm0;A2ScVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdbS5Vs;Vm0;A2A2S2dS6bS6dSddA1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S137Vsc;S5Vs;Vm0;A2M1SddSdbA4S6fS6cG0S33S6aS6cG1Se3A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Se3S5Vs;Vm0;A2A2S2dS6bS6dSddA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S25S70S6cS32S6aS6cA2M0A2S138Vsc;S5Vs;Vm0;A2SddSe3A4S6fS6cG0S33S6aS6cS7Vs;Vm0;A2SdaA4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SdaS7Vs;Vm0;A2A2S2dS6bS6dSdcA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S25S5eS139SdcA1Sb2Vs;Vm0;S2A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S135SdaS7Vs;Vm0;A2SdcA3").
Lemma taR : ltac2:(tb__ "0|1|
S25S70S6cS32S5eS6cA2M0A2S7cVsc;Vs;A2S6fS6cG0S33S5eS6cS71Sb2Vs;Vm0;S2A3A1Sd9A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S27S25S5eS71Sb2Vs;Vm0;S2A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S130VX;VU;Vs;Vsc;S71Sb2Vs;Vm0;S2A3A1Sd9A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Sd9Vsc;A2S2dS6aS7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sd9S7Vs;Vm0;A2A2S2dS6bS6dS132SdcA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S25S5eS79SdcA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sd9ScVs;Vm0;S3A3A2S2dS6bS6dSe8A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sd9ScVs;Vm0;S1A3A2S2dS6bS6dSddA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SaeVs;SdbS2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SaeSdbSe3S30S54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SaeSe3SdaS2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
SaeVs;SdaS2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G0A3G1A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S2aS0S11S2aS0S12S2aS0S8S60S6S3A1A1M0A1S2aS0S4S3S60S6S1fA1A1M1S60S6S1A1A1M2S60SfS3A1A1S60S18S3A1A1S60S19S3A1A1S60SeS3A1A1A7S2aS0S4S1G0S60S6S2A1A1S60SfS1A1A1S60S18S1A1A1S60S19S1A1A1S60SeS1A1A1A7S2aS0SdS1S60S20S1A1A1A2S2aS0S4S2G2G1S60SfS2A1A1S60S18S2A1A1S60S19S2A1A1S60SeS2A1A1A7S2aS0SdS2S60S20S2A1A1A2S2aS0S13S2aS0S10S2aS0S9S2S60PaaA1A2S30S0A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S25S2eS3bA1S44Sa1A1S2aS3bS15Sb7S0S3bS14SdeA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R4nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40Sa1A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R4nr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cS88S85S48S34S3fA1S2aS3bS15S30S3bA1A3S40Sa1A1S99S38A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S47S84VrhoW;SeaS33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4M0A4S47S84VrhoW;Sa1G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R4nr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S25S2cS32S2eS32S3fS3fA2M0A1M1S2eS3cA1M2A2M3A1S12aSabS96A2S2dG3S33G1G2S2aG0S33S3fS3fSb6S2A1S3aPabA1A4S30G0A1A3S35G1G2Sa6A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R4nr)). Qed.
Lemma swf_ST : swf ST_R4nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S25S31S80S3cS3cS82S3cS4eR1A1S40S96A1A3Lp;S35S2eS32S3fS3fA2A1S2eS3cA1Sa6A3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S25S31S80S3cSc1SbfA1S40S96A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S25S31S80S3cS129S40S96A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S96A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R4nr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R4nr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S25S5fS51S96A1S99A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R4nr 0 ST_R4nr.
Definition LT1 : sstate := lfs LT_R4nr 1 ST_R4nr.
Definition LT2 : sstate := lfs LT_R4nr 2 ST_R4nr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Se7A1A2Se0A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Se5A1A2Se1A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Se6A1A2Se2A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Se0A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Se1A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Se2A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Se0A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Se1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Se2A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SdeSe0A2SdfA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SdeSe1A2Se9A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SdeSe2A2Se4A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S25S2eS0A1SdfS2aS0S8S60S6S2A1A1A1S2aS0S4S2S60S6S1A1A1S60S6S1fA1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7S30S0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S25S2eS0A1Se4S2bS0SdfS2aS0S9S2Sb4A2S30S0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S25S39S37S0VdsF;A2S37S0SdeA2A3S0S7fS0R1VdsF;A3S28S22Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7fS0R2Sb1SdeVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2eS0A1M0G0S0S7fS0R1Sb1R3R2A2A3S7fS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S92Vk;U3A2S25S2eS3bA1S44S93S9cVk;S96A3A1M0S2aS3bSc6S4bS83S3bS15G0A3A1A1S81S3bG0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S5eS52S93S9cVk;S96A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2eS3fA1S50S93S9cVk;S96A3A1S85A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S4dS4fS93S9cVk;S96A3A1S48A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2cS3fA1S53S93S9cVk;S96A3A1S34S3fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S3fS49S93S9cVk;S96A3ZaA2S21S60PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S5eS26S61Z1R1A2S61R1Z1fA2A2S25S31S86S68R2A1A1S2fA3S25S3fS49S93S9cVk;S96A3R3A2S87S68R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R4nr k ST_R4nr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7fS3cS43S8fS3eZ1fA1S16S2A1A3S40Se7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7fS3cS43S90S60PaaA1S3eZ0A1A3S40Se5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Se5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7fS3cS46S43S90S60PaaA1S3eZ0A1A3A1S40Se6A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Se6A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S25S6cS134SdaS7Vs;Vm0;A2M1SdcA3S133SdaG1SdcA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2SaeVs;Sd9S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G1A3G2A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SaeVs;Sd9S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G1A3G2A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3S2aS54S56S62S59S65Vsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S25S2eS5eA1S6eSd9A1S7eS65Vsc;G0A2S65Vbnc;Z1A2S6eVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9S4S2S60S6S1A1A1S60S6S1fA1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_B). split; [exact MT_R'|].
  pose proof (am_final_fields am1_B) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MC); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_B; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_B; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_B, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9S8S60S6S2A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9S9S2Sb4A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1SdfA3S26S7fS0R2Se0A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1Se9A3S26S7fS0R2Se1A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S0S7fS0R1Se4A3S26S7fS0R2Se2A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd9R2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G0A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2G0A3G2A3A3A3S29S0S0S26S7fS0R1SdfA3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G0A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2S2aS54S56S62S59S65Vsc;Z7A2A2A1G0A3A3G2A3A3A3S29S0S0S26S7fS0R1Se4A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R4nr : ltac2:(tb__ "0|0|
VTR;Z0S12bS84VK;Sa1VrhoW;A4Sc5VX;VU;S121Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R4nr)).
  { apply (seg_run 300 SA_R4nr LA_R4nr _ rhoW eq_refl eq_refl runA_R4nr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R4nr _ SA_R4nr LfA LA_R4nr_shape HinA) in HSPA. change (lfs LA_R4nr 0 SA_R4nr) with LA_R4nrs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R4nrs ST_R4nr (e_maskA MB) (snd DT_R4nr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R4nr LT_R4nr _ rhoA ST_len ST_next runT_R4nr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R4nr _ _ _ ST_R4nr Lf LT_R4nr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nr 0 ST_R4nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nr 0 ST_R4nr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nr 1 ST_R4nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nr 1 ST_R4nr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4nr 2 ST_R4nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4nr 2 ST_R4nr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR4nr.
End Mal_aslot_VR4nr.

Module Mal_aslot_VR4sh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR4sh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S34S32S6aS5eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S26S61Z0Vreq;A2S61S62Vreq;S74A2S7aVsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Vs;Vsc;A2S2dS6aVm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2dS6aVm0;A2S2aS6aVm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§58§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§58§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§58§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§58§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls4 := (@U.Mal_aslot__G1.Mal_aslot_I.cls4 s X sc Hsc m0 rest Rg).
Local Notation "§59§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§59§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12fS122VX;S34S32S6aS5eA2A1VU;S121Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1aS26S26S61Z0M0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S63G1Z100A2A2S26S25S5eS66G1Z20A2S72SaVs;Vm0;R1A3M2A1A3S27S25S5eS77G2A1G0A3A1S25S5eS17VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S72SaVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§60§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§61§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§61§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§60§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S26S61Z1000S8bQ40S42Vrho;PaA2A2M0A2S25S5eS66G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S26S61S127Z40S8bQ40S42Vrho;PfA2A2A2M0S67S12eZ0A1A1A2S61S67S69Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61S126VL;A1S62S8bQ40M0S42Vrho;PaA2A2S127Z40S8bG0S42Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§62§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§62§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§63§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§63§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;Vrd0;SbdS84VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S25S89Q40A1S31F_;Vwok0;SbeS84VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z60A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ecR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z20A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ccR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1aS25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S23VL;S78SaVs;Vm0;R1A3A1A2Z8A2A2A3S2dG1S8aG0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S62Z5a3d0Z369A2Vsc;A2A2A3S2dG1S8aG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S124S123Vrd0;S89Q40A1S2fL_;A2S125S122A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S123SbdS84VmW;A2SbeS84VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§64§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§64§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§65§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§65§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§66§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§66§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S25S5eVbnc;S7dS65Vsc;G0A2S6eVs;A1A2A3F_;").
Local Notation "§67§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§67§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S131S84VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2eSb9A1SbaOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§68§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§68§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§69§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§69§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§70§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§70§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§71§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§71§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§58§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§72§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§72§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§63§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§63§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§73§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§73§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§74§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§74§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§75§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§75§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§76§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§76§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§77§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§77§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§77§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§73§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§69§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§78§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§78§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§78§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§78§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§59§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§59§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§59§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S25SbbVvm;SbcVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2eSb9A1M0SbaVK;R2R1A2S26VKc;R3R2A2S26S25G0R3Vtr;A3S25SbaR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S47S84Vrho;S12dS12cA1S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 4%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S25S5eS75SaVs;Vm0;S3A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S27S25S5eS73SaVs;Vm0;S3A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S25S5eS73SaVs;Vm0;S1A3M0A1S7bS76G0A1A1A3").
Hypothesis HVact : maskA MB <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S25S5eVmaskv;Sb2Vs;Vm0;S2A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Vs;S1cVm0;A1A2S2dS6bS6dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls4 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls4 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS7Vs;Vm0;A2A2Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS7Vs;Vm0;A2A2Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SeeScVs;Vm0;S3A3A2S2dS6bS6dSfaA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SeeScVs;Vm0;S1A3A2S2dS6bS6dSf5A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SeeScVs;Vm0;S2A3A2S2dS6bS6dSecA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SedVq;A2S55SeeVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S25S2eS5eA1S6eSedA1S6eVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S25S2cS6aA1S58SedVsc;A2S2dS6aS7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S25S70S6cS32S2cS6aA1M0S6cA2M1A2S136Vsc;S1cVm0;A1Vam0;Vs;A4S6fS6cG1S33G0S6cS2dS6aS5Vs;Vm0;A2A2SeeA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S25S6aS5Vs;Vm0;A2ScVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SeeS5Vs;Vm0;A2A2S2dS6bS6dSf5A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S25S70S6cS32S6aS6cA2M0A2S137Vsc;S5Vs;Vm0;A2Sf5SeeA4S6fS6cG0S33S6aS6cS7Vs;Vm0;A2Sf4A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Sf4S7Vs;Vm0;A2A2S2dS6bS6dSecA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S138Vsc;S7Vs;Vm0;A2M1SecSf4A4S6fS6cG0S33S6aS6cG1SedA4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_B. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SedS7Vs;Vm0;A2A2S2dS6bS6dSecA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S25S5eS139SecA1Sb2Vs;Vm0;S2A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S135SedS7Vs;Vm0;A2SecA3").
Lemma taR : ltac2:(tb__ "0|1|
S25S70S6cS32S5eS6cA2M0A2S7cVsc;Vs;A2S6fS6cG0S33S5eS6cS71Sb2Vs;Vm0;S2A3A1SebA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S27S25S5eS71Sb2Vs;Vm0;S2A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S130VX;VU;Vs;Vsc;S71Sb2Vs;Vm0;S2A3A1SebA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S25S2cS6aA1S58SebVsc;A2S2dS6aS7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SebS7Vs;Vm0;A2A2S2dS6bS6dS132SecA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S25S5eS79SecA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SebScVs;Vm0;S3A3A2S2dS6bS6dSfaA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55SebScVs;Vm0;S1A3A2S2dS6bS6dSf5A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SaeVs;SeeS2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SaeSeeSf4S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SaeSf4SedS30S54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
SaeVs;SedS2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S2aS0S11S2aS0S12S2aS0S8S60S6S3A1A1M0A1S2aS0S4S3S60S6S1fA1A1M1S60S6S1A1A1M2S60SfS3A1A1S60S18S3A1A1S60S19S3A1A1S60SeS3A1A1A7S2aS0S4S1G0S60S6S2A1A1S60SfS1A1A1S60S18S1A1A1S60S19S1A1A1S60SeS1A1A1A7S2aS0S4S2G2G1S60SfS2A1A1S60S18S2A1A1S60S19S2A1A1S60SeS2A1A1A7S2aS0SdS2S60S20S2A1A1A2S2aS0S13S2aS0S10S2aS0S9S2S60PaaA1A2S30S0A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S25S2eS3bA1S44Sa2A1S2aS3bS15Sb7S0S3bS14SefA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R4sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40Sa2A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R4sh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cS88S85S48S34S3fA1S2aS3bS15S30S3bA1A3S40Sa2A1S99S38A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S47S84VrhoW;SfcS33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4M0A4S47S84VrhoW;Sa2G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R4sh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S25S2cS32S2eS32S3fS3fA2M0A1M1S2eS3cA1M2A2M3A1S12aSacS97A2S2dG3S33G1G2S2aG0S33S3fS3fSb6S2A1S3aPabA1A4S30G0A1A3S35G1G2Sa7A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R4sh)). Qed.
Lemma swf_ST : swf ST_R4sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S25S31S80S3cS3cS82S3cS4eR1A1S40S97A1A3Lp;S35S2eS32S3fS3fA2A1S2eS3cA1Sa7A3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S25S31S80S3cSc1SbfA1S40S97A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S25S31S80S3cS129S40S97A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S97A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R4sh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R4sh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S25S5fS51S97A1S99A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R4sh 0 ST_R4sh.
Definition LT1 : sstate := lfs LT_R4sh 1 ST_R4sh.
Definition LT2 : sstate := lfs LT_R4sh 2 ST_R4sh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sf9A1A2Sf1A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sf7A1A2Sf2A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44Sf8A1A2Sf3A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Sf1A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Sf2A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14Sf3A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Sf1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Sf2A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4Sf3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SefSf1A2Sf0A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SefSf2A2SfbA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1SefSf3A2Sf6A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S25S2eS0A1Sf0S2aS0S8S60S6S2A1A1A1S2aS0S4S2S60S6S1A1A1S60S6S1fA1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7S30S0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S25S2eS0A1Sf6S2bS0Sf0S2aS0S9S2Sb4A2S30S0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S25S39S37S0VdsF;A2S37S0SefA2A3S0S7fS0R1VdsF;A3S28S22Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7fS0R2Sb1SefVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2eS0A1M0G0S0S7fS0R1Sb1R3R2A2A3S7fS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S92Vk;U3A2S25S2eS3bA1S44S93S9dVk;S97A3A1M0S2aS3bSc6S4bS83S3bS15G0A3A1A1S81S3bG0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S5eS52S93S9dVk;S97A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2eS3fA1S50S93S9dVk;S97A3A1S85A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S4dS4fS93S9dVk;S97A3A1S48A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2cS3fA1S53S93S9dVk;S97A3A1S34S3fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S3fS49S93S9dVk;S97A3ZaA2S21S60PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S5eS26S61Z1R1A2S61R1Z1fA2A2S25S31S86S68R2A1A1S2fA3S25S3fS49S93S9dVk;S97A3R3A2S87S68R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R4sh k ST_R4sh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7fS3cS43S8fS3eZ1fA1S16S2A1A3S40Sf9A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7fS3cS43S90S60PaaA1S3eZ0A1A3S40Sf7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Sf7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7fS3cS46S43S90S60PaaA1S3eZ0A1A3A1S40Sf8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S2A1A3A1S40Sf8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S25S6cS134SedS7Vs;Vm0;A2M1SecA3S133SedG1SecA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2SaeVs;SebS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G2A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SaeVs;SebS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3M2G2A3G1A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M3S2aS54S56S62S59S65Vsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S25S2eS5eA1S6eSebA1S7eS65Vsc;G0A2S65Vbnc;Z1A2S6eVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebS4S2S60S6S1A1A1S60S6S1fA1A1S60SfS2A1A1Sb3Sb5S2A1S60SeS2A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_B). split; [exact MT_R'|].
  pose proof (am_final_fields am1_B) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MC); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_B; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_B; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_B, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebS8S60S6S2A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebS9S2Sb4A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1Sf0A3S26S7fS0R2Sf1A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1SfbA3S26S7fS0R2Sf2A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S0S7fS0R1Sf6A3S26S7fS0R2Sf3A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SebR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2G0A3G2A3A3A3S29S0S0S26S7fS0R1Sf0A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3M1G1A3G0A3S2bS54S2bS54SafS7Vs;Vm0;A2A1M2S2aS54S56S62S59S65Vsc;Z7A2A2A1G0A3A3G2A3A3A3S29S0S0S26S7fS0R1Sf6A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M3A3S5aVL;R3A2M4A2S63G4S35S5eS5eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R4sh : ltac2:(tb__ "0|0|
VTR;Z0S12bS84VK;Sa2VrhoW;A4Sc5VX;VU;S121Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R4sh)).
  { apply (seg_run 300 SA_R4sh LA_R4sh _ rhoW eq_refl eq_refl runA_R4sh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R4sh _ SA_R4sh LfA LA_R4sh_shape HinA) in HSPA. change (lfs LA_R4sh 0 SA_R4sh) with LA_R4shs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R4shs ST_R4sh (e_maskA MB) (snd DT_R4sh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R4sh LT_R4sh _ rhoA ST_len ST_next runT_R4sh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R4sh _ _ _ ST_R4sh Lf LT_R4sh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sh 0 ST_R4sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sh 0 ST_R4sh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sh 1 ST_R4sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sh 1 ST_R4sh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sh 2 ST_R4sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sh 2 ST_R4sh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR4sh.
End Mal_aslot_VR4sh.

Module Mal_aslot_VR5nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR5nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S5bVX;S34S32S6aS5eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S26S61Z0Vreq;A2S61S62Vreq;S74A2S7aVsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S25S2cS6aA1S58Vs;Vsc;A2S2dS6aVm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S5dS5cVX;Vs;Vsc;A3S2dS6aVm0;A2S2aS6aVm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§79§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§79§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§79§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§79§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§80§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§80§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S12fS122VX;S34S32S6aS5eA2A1VU;S121Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S1aS26S26S61Z0M0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S63G1Z100A2A2S26S25S5eS66G1Z20A2S72SaVs;Vm0;R1A3M2A1A3S27S25S5eS77G2A1G0A3A1S25S5eS17VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S72SaVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§81§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§82§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S26S61Z1000S8bQ40S42Vrho;PaA2A2M0A2S25S5eS66G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S26S61S127Z40S8bQ40S42Vrho;PfA2A2A2M0S67S12eZ0A1A1A2S61S67S69Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S61S126VL;A1S62S8bQ40M0S42Vrho;PaA2A2S127Z40S8bG0S42Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§83§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§83§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§84§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§82§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§84§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;Vrd0;SbdS84VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S25S89Q40A1S31F_;Vwok0;SbeS84VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z60A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ecR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S5eS26S61Z0R1A2S63R1Z20A2A2S25S2cS89Q8A1M0A1VmW;S8aQ40S62Z108ccR2A2A2A1S34G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S1aS25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S23VL;S78SaVs;Vm0;R1A3A1A2Z8A2A2A3S2dG1S8aG0S17VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S25S2cS89Q8M0A1M1A1SbdS84VmW;S8aQ40S62S62Z5a3d0Z369A2Vsc;A2A2A3S2dG1S8aG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S124S123Vrd0;S89Q40A1S2fL_;A2S125S122A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S123SbdS84VmW;A2SbeS84VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§85§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§85§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§79§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§86§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§86§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§87§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§87§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§82§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S25S5eVbnc;S7dS65Vsc;G0A2S6eVs;A1A2A3F_;").
Local Notation "§88§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§88§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§81§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S131S84VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2eSb9A1SbaOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§89§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§89§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§90§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§90§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§91§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§91§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§92§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§92§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§79§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§93§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§93§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§84§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§84§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§94§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§94§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§95§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§95§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§96§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§96§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§97§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§97§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§98§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§98§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§98§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§94§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§90§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§99§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§99§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§99§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§99§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§80§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§80§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§80§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S25S89Q40A1S2cS89Q8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S25SbbVvm;SbcVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2eSb9A1M0SbaVK;R2R1A2S26VKc;R3R2A2S26S25G0R3Vtr;A3S25SbaR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S47S84Vrho;S12dS12cA1S33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S25S5eS8bQ40S42Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S25S5eS75SaVs;Vm0;S3A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S27S25S5eS73SaVs;Vm0;S3A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S27S25S5eS73SaVs;Vm0;S1A3M0A1S7bS76G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S25S5eVmaskv;Sb2Vs;Vm0;S1A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55Vs;S1cVm0;A1A2S2dS6bS6dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sb0Vsc;S2dS6aS5Vs;Vm0;A2A2Vs;A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S111ScVs;Vm0;S3A3A2S2dS6bS6dS11cA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S111ScVs;Vm0;S1A3A2S2dS6bS6dS10fA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S110Vq;A2S55S111Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S25S2eS5eA1S6eS110A1S6eVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S25S2cS6aA1S58S110Vsc;A2S2dS6aS5Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S25S70S6cS32S2cS6aA1M0S6cA2M1A2S136Vsc;S1cVm0;A1Vam0;Vs;A4S6fS6cG1S33G0S6cS2dS6aS5Vs;Vm0;A2A2S111A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S25S6aS5Vs;Vm0;A2ScVs;Vm0;S1A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S111S5Vs;Vm0;A2A2S2dS6bS6dS10fA1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S137Vsc;S5Vs;Vm0;A2M1S10fS111A4S6fS6cG0S33S6aS6cG1S117A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S117S5Vs;Vm0;A2A2S2dS6bS6dS10fA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S25S70S6cS32S6aS6cA2M0A2S138Vsc;S5Vs;Vm0;A2M1S10fS117A4S6fS6cG0S33S6aS6cG1S110A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S110S5Vs;Vm0;A2A2S2dS6bS6dS10fA1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S25S5eS139S10fA1Sb2Vs;Vm0;S1A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S135S110S5Vs;Vm0;A2S10fA3").
Lemma taR : ltac2:(tb__ "0|1|
S25S70S6cS32S5eS6cA2M0A2S7cVsc;Vs;A2S6fS6cG0S33S5eS6cS71Sb2Vs;Vm0;S1A3A1S10eA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S27S25S5eS71Sb2Vs;Vm0;S1A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S130VX;VU;Vs;Vsc;S71Sb2Vs;Vm0;S1A3A1S10eA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S25S2cS6aA1S58S10eVsc;A2S2dS6aS5Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S10eS5Vs;Vm0;A2A2S2dS6bS6dS132S10fA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S25S5eS79S10fA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S25S2cS6bA1S55S10eScVs;Vm0;S3A3A2S2dS6bS6dS11cA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
SaeVs;S111S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
SaeS111S117S30S54A1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
SaeS117S110S30S54A1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
SaeVs;S110S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|1|
S2aS0S11S2aS0S12S2aS0S8S60S6S3A1A1M0A1S2aS0S4S3S60S6S24A1A1S60S6S1A1A1S60SfS3A1A1S60S18S3A1A1S60S19S3A1A1S60SeS3A1A1A7S2aS0S4S1G0S60S6S2A1A1S60SfS1A1A1S60S18S1A1A1S60S19S1A1A1S60SeS1A1A1A7S2aS0SdS1S60S20S1A1A1A2S2aS0S13S2aS0S10S2aS0S9S1S60PaaA1A2S30S0A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S25S2eS3bA1S44Sa3A1S2aS3bS15Sb7S0S3bS14S112A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R5nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using Hr Hsc Rg. drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Ltac solve_zf :=
  lazymatch goal with
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (SLit 0))) => apply (zf_ptr_ne0 x)
  | |- zholds _ _ (SPUle (v (vbyte ?x)) (SLit 255)) => apply (zf_byte x)
  | |- zholds _ _ (SPAlign (vptr ?x) 3) => apply (zf_align x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits ?x)) (SLit 32)) (SLit 0))) => apply (zf_freeable x)
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (v (vptr ?x)) (v (vptr ?y)))) => apply (zf_neq x y); cbn [mptr]; solve_neq
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0)) => apply (zf_avail_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vavail ?x))) (SLit 0))) => apply (zf_avail_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0)) => apply (zf_freed_eq0 x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SLit 0))) => apply (zf_freed_ne0 x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_eq x); assumption
  | |- zholds _ _ (SPBranch BC_NE (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) => apply (zf_all_ne x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); first [assumption | exact HVmask3]
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40Sa3A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R5nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cS88S85S48S34S3fA1S2aS3bS15S30S3bA1A3S40Sa3A1S99S38A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S47S84VrhoW;S11eS33S2eSb9A1S11fVtr;S120Vms;Vmd;A2A4M0A4S47S84VrhoW;Sa3G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R5nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S25S2cS32S2eS32S3fS3fA2M0A1M1S2eS3cA1M2A2M3A1S12aSadS98A2S2dG3S33G1G2S2aG0S33S3fS3fSb6S1A1S3aPabA1A4S30G0A1A3S35G1G2Sa8A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R5nh)). Qed.
Lemma swf_ST : swf ST_R5nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S25S31S80S3cS3cS82S3cS4eR1A1S40S98A1A3Lp;S35S2eS32S3fS3fA2A1S2eS3cA1Sa8A3A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S25S31S80S3cSc1SbfA1S40S98A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S25S31S80S3cS129S40S98A1A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sb8S3cS128S1eVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1dVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S40S98A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R5nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R5nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S25S5fS51S98A1S99A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R5nh 0 ST_R5nh.
Definition LT1 : sstate := lfs LT_R5nh 1 ST_R5nh.
Definition LT2 : sstate := lfs LT_R5nh 2 ST_R5nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S11bA1A2S114A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S119A1A2S115A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S25S31Sc2S81S3bS44S11aA1A2S116A2S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S114A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S115A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S25S31S80S3bSc0SbfA1Sb7S0S3bS14S116A4A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S114A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S115A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S25S31S80S0Sc4S116A3S2fA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S112S114A2S113A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S112S115A2S11dA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S25S2eS0A1Sb1S112S116A2S118A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S25S2eS0A1S113S2aS0S8S60S6S1A1A1A1S2aS0S4S1S60S6S3A1A1S60S6S2A1A1S60SfS1A1A1Sb3Sb5S1A1S60SeS1A1A1A7S30S0A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S25S2eS0A1S118S2bS0S113S2aS0S9S1Sb4A2S30S0A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S25S39S37S0VdsF;A2S37S0S112A2A3S0S7fS0R1VdsF;A3S28S22Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S7fS0R2Sb1S112VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2eS0A1M0G0S0S7fS0R1Sb1R3R2A2A3S7fS0R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
S92Vk;U3A2S25S2eS3bA1S44S93S9eVk;S98A3A1M0S2aS3bSc6S4bS83S3bS15G0A3A1A1S81S3bG0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S5eS52S93S9eVk;S98A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2eS3fA1S50S93S9eVk;S98A3A1S85A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S4dS4fS93S9eVk;S98A3A1S48A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S2cS3fA1S53S93S9eVk;S98A3A1S34S3fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
S92Vk;U3A2S25S3fS49S93S9eVk;S98A3ZaA2S21S60PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
S92Vk;U3A2S5eS26S61Z1R1A2S61R1Z1fA2A2S25S31S86S68R2A1A1S2fA3S25S3fS49S93S9eVk;S98A3R3A2S87S68R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R5nh k ST_R5nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S7fS3cS43S8fS3eZ1fA1S16S1A1A3S40S11bA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S7fS3cS43S90S60PaaA1S3eZ0A1A3S40S119A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S1A1A3A1S40S119A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S7fS3cS46S43S90S60PaaA1S3eZ0A1A3A1S40S11aA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S7fS3cS46S43S8fS3eZ1fA1S16S1A1A3A1S40S11aA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S25S6cS134S110S5Vs;Vm0;A2M1S10fA3S133S110G1S10fA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2SaeVs;S10eS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3G1A3G1A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SaeVs;S10eS2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M1A3G1A3G1A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M2S2aS54S56S62S59S65Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S26S61Z7M0Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S25S2eS5eA1S6eS10eA1S7eS65Vsc;G0A2S65Vbnc;Z1A2S6eVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eS4S1S60S6S3A1A1S60S6S2A1A1S60SfS1A1A1Sb3Sb5S1A1S60SeS1A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eS8S60S6S1A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eS9S1Sb4A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1S113A3S26S7fS0R2S114A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S28S27S26S61Z7Vsc;A2S63Vsc;Z27A2A2M0A1S26G0S25S5eVbnc;Z0A3A2A2S0S7fS0R1S11dA3S26S7fS0R2S115A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S26S61Z7Vsc;A2S63Vsc;Z27A2A2S27S25S5eVbnc;Z0A3A1S0S7fS0R1S118A3S26S7fS0R2S116A3S26SbVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S10eR2A11Sc3Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M1G0A3G1A3A3A3S29S0S0S26S7fS0R1S113A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S63G3S35S5eS5eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S54S7fS54R1S2bS54S2bS54S2bS54S2aS54S56S62S57S64Z8Vsc;A2A2A1S30S54A1M0A3G0A3G0A3S2bS54S2bS54SafS5Vs;Vm0;A2A1M1S2aS54S56S62S59S65Vsc;Z7A2A2A1G0A3A3G1A3A3A3S29S0S0S26S7fS0R1S118A3S26S61S36S5eS5eS1bVs;VL;Vsc;Vm0;R1A5M2A3S5aVL;R3A2M3A2S63G3S35S5eS5eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MM0)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R5nh : ltac2:(tb__ "0|0|
VTR;Z0S12bS84VK;Sa3VrhoW;A4Sc5VX;VU;S121Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R5nh)).
  { apply (seg_run 300 SA_R5nh LA_R5nh _ rhoW eq_refl eq_refl runA_R5nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R5nh _ SA_R5nh LfA LA_R5nh_shape HinA) in HSPA. change (lfs LA_R5nh 0 SA_R5nh) with LA_R5nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R5nhs ST_R5nh (e_maskA MA_) (snd DT_R5nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R5nh LT_R5nh _ rhoA ST_len ST_next runT_R5nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R5nh _ _ _ ST_R5nh Lf LT_R5nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nh 0 ST_R5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nh 0 ST_R5nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nh 1 ST_R5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nh 1 ST_R5nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nh 2 ST_R5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nh 2 ST_R5nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR5nh.
End Mal_aslot_VR5nh.
