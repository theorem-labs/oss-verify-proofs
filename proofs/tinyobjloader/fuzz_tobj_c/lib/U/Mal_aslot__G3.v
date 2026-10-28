(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MA_"; "pA"; "MM0"; "MB"; "OD_meta"; "pM0"; "mam"; "pB"; "od_ok_at"; "vbits"; "vmem"; "mptr"; "vptr"; "OD_act"; "OD_bnc"; "vfreed"; "member"; "vavail"; "OD_mem"; "OD_ctz"; "OD_got"; "OD_guard"; "OD_sct"; "obj_of"; "mbyte"; "zl1"; "zr1"; "e_bncidx"; "O_stk"; "od_range"; "vbyte"; "zA"; "e_ctz"; "od_ok"; "member_eqb"; "e_and"; "e_lowbit"; "e_sx"; "e_dbidx"; "e_onesw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "LCtx"; "CTX_active"; "keys"; "active_hd"; "loc_addr"; "CTX_bounces"; "Inv"; "alinks"; "ring_ok"; "memb"; "LMem"; "@Corelib.Init.Datatypes"; "cons"; "app"; "option"; "list"; "Some"; "true"; "bool"; "nil"; "prod"; "false"; "pair"; "None"; "length"; "snd"; "nat"; "fst"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "sprop"; "sobj"; "SLit"; "ss_facts"; "SAluW"; "rw"; "SAlu"; "SPBranch"; "ss_objs"; "SPNot"; "smatch"; "SExt"; "reg_sv"; "sv_eqb"; "FcsrFrm0"; "cell"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "rm"; "sprop_eqb"; "ss_pc"; "sstate"; "ob_cells"; "mkSS"; "ss_next"; "SPUle"; "c_val"; "eval"; "rl"; "swf"; "valuation"; "c_off"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "MUsed"; "st_bounces"; "IRet"; "itree"; "lowbit"; "am_aidx"; "am_freed"; "am_set_links"; "am_prev"; "ones"; "st_active"; "IB"; "am_avail"; "am_maplen"; "am_mem"; "class_size"; "try_avail"; "znth"; "am_last"; "am_sc"; "lupd"; "zset"; "am_next"; "ctz32"; "padd"; "set_bounces"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "sub"; "modulo"; "opp"; "pow"; "to_nat"; "land"; "ldiff"; "shiftl"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "find"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "set_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "callee_saved"; "pre_reg"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_AND"; "BC_LTU"; "ALU_SLL"; "BC_EQ"; "ALU_ADD"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD"; "lfs"; "ST_D2nh"; "ST_D2sh"; "ST_D3nh"; "ST_D3nr"; "NXA"; "LT_D2nh"; "LT_D2sh"; "LT_D3nh"; "LT_D3nr"; "SA_D2nh"; "SA_D2sh"; "SA_D3nh"; "SA_D3nr"; "DT_D2nh"; "DT_D2sh"; "DT_D3nh"; "DT_D3nr"; "LA_D2nhs"; "LA_D2shs"; "LA_D3nhs"; "LA_D3nrs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT"; "cell_at"; "e_maskA"; "fill"; "od_eqb"; "only_cell"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State";
"event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nh.VD3nh"; "sR'"; "am1_A"; "s1V"; "s3V"; "xp"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_B"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD3nr.VD3nr"; "sR'"; "s1V"; "s3V"; "am1_B"; "xp"; "am1_A"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2nh.VD2nh"; "sR'"; "am1_A"; "s3V"; "s1V"; "xp"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_VD2sh.VD2sh"; "sR'"; "am1_A"; "s3V"; "s1V"; "xp"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sprop_vars_all"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "s1_deq"; "s1a"; "s6"; "am_final"; "s1b"; "s4"; "s5"; "step1"; "step2"; "step3"; "t_mask"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "HITP"; "oStkF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zholds"; "toS"; "psupported"; "zeval"; "sx32"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "as_stack"; "IEC_U"; "Pre_as"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "stop_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "lfs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.T"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT"; "e_maskA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "sh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts"; "mnext"; "mprev"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_T.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition cell_at (cs : list cell) (off : Z) (dflt : sv) : sv := ltac2:(tb__ "0|0|
S3dS5fA1S4fLx;Sa1S5fS5fS5dS71R1A1S52Voff;A1A2Lc;Vcs;A3S5fS6cR1A1Lc;Vdflt;X3dx2").
Definition only_cell (cs : list cell) (dflt : sv) : sv := ltac2:(tb__ "0|1|
S3eS5fA1M0S4fLcs;Vcs;Vdflt;S5fG0G0S4fLl;R1S6cR2A1S5fG0Vdflt;Ll0;Lc0;X3ex2Ll;Lc;X3ex2").

Definition fill1 (d : od) (o : sobj) : od := ltac2:(tb__ "0|3|
S5S5Ld;Vd;Vd;Vd;Vd;Vd;S4fS13Sd3S68Vo;A1M0R1A2M1A1Lhv;S16S4fS4fS4fS4fS4fS4fG0S3eS5fA1SaR8ScfR1Z0R7A3ScfR1Z8M2R6A3ScfR1Z10R5A3ScfR1Z18R4A3ScfR1Z1cR3A3ScfR1Z20R2A3A7Tcs;Lbv;Lfv;Lav;Lmv;Lnv;Lpv;Lx;S16S4fS18R2ScfG0G2R1A3A2Lyv;Lx;S16S4fS14R2G1A2Lyv;Lx;X5x8").

Fixpoint fill (ds : list od) (os : list sobj) : list od :=
  match ds, os with
  | d :: ds', o :: os' => fill1 d o :: fill ds' os'
  | _, _ => []
  end.

Definition od_eqb (d d' : od) : bool := ltac2:(tb__ "0|9|
S5S41Ld;Vd;S5S41Ld';M0Vd';S40S44S44S44S4fS44Lhv;M1S16S4fS4fS4fS4fS4fS4fS44Lbv;Lfv;Lav;Lmv;Lnv;Lpv;M2Lx;M3S16S4fS44Lyv;M4Lx;M5G5X5x8G0Vd';S44S40S44S44G1G3G5G5X5x8G0Vd';S44S44S40S44G1G3G5G5X5x8G0Vd';S44S44S44S40G1G3G5G5X5x8S4fG0Vd';S44S44S44S44S4fS5dR2R1A2La';G3G5G5X5x8La;S16S4fS4fS4fS4fS4fS4fG0Vd';S44S44S44S44G1S16S4fS4fS4fS4fS4fS4fS4bS4bS4bS4bS4bS4bS28ReR7A2S5dRdR6A2A2S5dRcR5A2A2S5dRbR4A2A2S5dRaR3A2A2S5dR9R2A2A2S5dR8R1A2A2Lf';Le';Ld0';Lc';Lb';La';Lx';S16G4Lx0;M6G6X5x8Lf;Le;Ld0;Lc;Lb;La;Lx;S16S4fG0Vd';S44S44S44S44G1S16G2Lx0;M7S16S4fS4bS28R4R2A2S5dR3R1A2A2La';Lx';M8G6X5x8La;Lx;S16S4fG0Vd';S44S44S44S44G1G7G6G8X5x8La;Lx;X5x8").

Lemma member_eqb_sound x y : ltac2:(tb__ "0|0|
S0S41S28Vx;Vy;A2S40A3S0S16Vx;Vy;A3F_;").
Proof. destruct x, y; cbn; intros H; try reflexivity; discriminate. Qed.

Lemma od_eqb_sound d d' : ltac2:(tb__ "0|0|
S0S41Sd2Vd;Vd';A2S40A3S0S5Vd;Vd';A3F_;").
Proof.
  destruct d, d'; cbn; intros H; try discriminate; try reflexivity.
  - apply sv_eqb_sound in H. subst. reflexivity.
  - repeat (apply andb_prop in H as [H ?X]).
    apply member_eqb_sound in H. repeat match goal with H : sv_eqb _ _ = true |- _ => apply sv_eqb_sound in H end. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply member_eqb_sound in H1. apply sv_eqb_sound in H2. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply member_eqb_sound in H1. apply sv_eqb_sound in H2. subst. reflexivity.
Qed.

Fixpoint changed (ds ds' : list od) : list od :=
  match ds, ds' with
  | d :: t, d' :: t' => if od_eqb d d' then changed t t' else d' :: changed t t'
  | _, _ => []
  end.

Lemma ent_changed (P : od -> Prop) : ltac2:(tb__ "0|1|
S3eS5A1M0G0S0S49S47S5R1A2S47S5R2A2A3Sd9S5VP;R3A3S5S9cS5R1R4A3S3VP;R2A1S9cS5R2ScaR6R5A2A3A2F_;Fd;F_;F_;Fds';Fds;").
Proof.
  induction ds as [|d0 t IH]; intros [|d0' t'] Hlen HP d Hd; cbn in *; try lia; try (destruct Hd; fail).
  apply Forall_cons_iff in HP as [HP0 HPt].
  destruct (od_eqb d0 d0') eqn:E.
  - apply od_eqb_sound in E. subst d0'. destruct Hd as [<-|Hd]; [left; exact HP0|].
    apply IH; [lia | exact HPt | exact Hd].
  - destruct Hd as [<-|Hd]; [right; left; reflexivity|].
    destruct (IH t' ltac:(lia) HPt d Hd) as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma fill_length ds os : ltac2:(tb__ "0|1|
S0S49S47S51Vos;A2S47S5Vds;A2M0A3S0S49S47S5Sd1Vds;Vos;A2A2G0A3F_;").
Proof. revert os. induction ds as [|d t IH]; intros [|o os] H; cbn in *; try lia. rewrite IH; lia. Qed.

Lemma changed_sub ds ds' : ltac2:(tb__ "0|0|
S5S9cS5R1ScaVds;Vds';A2A3S9cS5R2Vds';A3F_;Fd;").
Proof.
  revert ds'. induction ds as [|d0 t IH]; intros [|d0' t'] d Hd; cbn in *; try tauto.
  destruct (od_eqb d0 d0'); [right; apply IH; exact Hd|]. destruct Hd as [<-|Hd]; [left; reflexivity | right; apply IH; exact Hd].
Qed.

Lemma leaf3 (l : list leaf) a b c d Lf : ltac2:(tb__ "0|2|
S0S3eS43S4cS158A2M0A1Sd8S156G0S160Vl;A4S3bG0Va;S3bG0Vb;S3bG0Vc;S42G0A1A3A3A3A3S9cS156VLf;Vl;A3S3S0S67S157VLf;A1M1S159Vl;U0Vd;A3A3S3S0S67G1S159Vl;U1Vd;A3A3S0S67G1S159Vl;U2Vd;A3A3A2A2F_;F_;").
Proof.
  intros E Hin. destruct l as [|L0 [|L1 [|L2 [|L3 t]]]]; cbn in E; try discriminate.
  destruct Hin as [<-|[<-|[<-|[]]]]; [left | right; left | right; right]; reflexivity.
Qed.

Lemma single_leaf (l : list leaf) pcr d Lf : ltac2:(tb__ "0|1|
S0S3eS43S4cS158A2M0A1Sd8S156G0S160Vl;A4S3bG0Vpcr;S42G0A1A3A3S9cS156VLf;Vl;A3S0S67S157VLf;A1S159Vl;U0Vd;A3A3F_;F_;").
Proof.
  intros E Hin. destruct l as [|L0 [|L1 t]]; cbn in E; try discriminate.
  destruct Hin as [<-|[]]. reflexivity.
Qed.

Lemma ctz32_lowbit m : ltac2:(tb__ "0|0|
S92Z0Vm;A2S0S4cS8dS7aVm;A1A1S8dVm;A1A3F_;").
Proof.
  intros Hm. destruct (lowbit_spec m Hm) as (k & Hk & Hl & _). unfold ctz32. rewrite Hl.
  f_equal. destruct (lowbit_spec (bit k) ltac:(unfold bit; apply Z.pow_pos_nonneg; lia)) as (k' & Hk' & Hl' & Hb' & _).
  rewrite Hl'. rewrite testbit_bit in Hb' by lia. apply Z.eqb_eq in Hb'. subst k'. reflexivity.
Qed.

Section T.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S36VX;S46S43S73S4cA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S90Z0Vreq;A2S90S91Vreq;S81A2S85Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3dS73A1S33Vs;Vsc;A2S3fS73Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S38S37VX;Vs;Vsc;A3S3fS73Vm0;A2S3bS73Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Abbreviation member_eqb := (@U.Mal_aslot__G1.Mal_aslot_I.member_eqb).
Local Abbreviation mptr := (@U.Mal_aslot__G1.Mal_aslot_I.mptr s m0).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (@U.Mal_aslot__G1.Mal_aslot_I.mam s m0).
Local Notation "§1§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mnext_used := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mnext_used).
Local Abbreviation mprev_used := (§1§ U.Mal_aslot__G1.Mal_aslot_I.mprev_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S153S146VX;S46S43S73S4cA2A1VU;S14eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation Hctx := (@U.Mal_aslot__G1.Mal_aslot_I.Hctx s L X U rd0 wok0 vm HMI).
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S16S1S1S90Z0M0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S92G1Z100A2A2S1S0S4cS95G1Z20A2S7bScVs;Vm0;R1A3M2A1A3S2S0S4cS83G2A1G0A3A1S0S4cS1eVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bScVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Abbreviation mem_R := (@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Notation "§2§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rw1 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.rw1).
Local Abbreviation rho1 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation zr1_171 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zr1_171).
Local Abbreviation ze_lit := (§2§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation ze_alu := (§2§ U.Mal_aslot__G1.Mal_aslot_I.ze_alu).
Local Abbreviation ze_aluw := (§2§ U.Mal_aslot__G1.Mal_aslot_I.ze_aluw).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§3§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_byte := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze_byte).
Local Notation "§4§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze170 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze170).
Local Abbreviation ze171 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_sx := (@U.Mal_aslot__G1.Mal_aslot_I.e_sx).
Local Abbreviation e_onesw := (@U.Mal_aslot__G1.Mal_aslot_I.e_onesw).
Local Abbreviation e_and := (@U.Mal_aslot__G1.Mal_aslot_I.e_and).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Local Abbreviation ze_sx_freed := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze_sx_freed).
Local Abbreviation ze_onesw_byte := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze_onesw_byte).
Local Abbreviation ze_bncidx := (§3§ U.Mal_aslot__G1.Mal_aslot_I.ze_bncidx).
Local Abbreviation ze_lowbit_sx := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_lowbit_sx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S90Z1000SacQ40S55Vrho;PaA2A2M0A2S0S4cS95G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S90S141Z40SacQ40S55Vrho;PfA2A2A2M0S96S150Z0A1A1A2S90S96S97Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S90S14aVL;A1S91SacQ40M0S55Vrho;PaA2A2S141Z40SacG0S55Vrho;PfA2A2A2A2A2").
Local Notation "§5§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation land_freed_act := (§5§ U.Mal_aslot__G1.Mal_aslot_I.land_freed_act).
Local Abbreviation land_fa_range := (§5§ U.Mal_aslot__G1.Mal_aslot_I.land_fa_range).
Local Abbreviation ZF_T := (@U.Mal_aslot__G1.Mal_aslot_I.ZF_T s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;Vrd0;Sd4Sa5VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SaaQ40A1S41F_;Vwok0;Sd5Sa5VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z60A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ecR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z20A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ccR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S16S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S25VL;S84ScVs;Vm0;R1A3A1A2Z8A2A2A3S3fG1SabG0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S91Z5a3d0Z369A2Vsc;A2A2A3S3fG1SabG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S148S147Vrd0;SaaQ40A1S40L_;A2S149S146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147Sd4Sa5VmW;A2Sd5Sa5VmW;A2A2").
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S0S4cVbnc;S87S94Vsc;G0A2S77Vs;A1A2A3F_;").
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S155Sa5VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S3eSdaA1SdbOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Notation "§6§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) (at level 10, h__ global).
Local Abbreviation EV := (§6§ U.Mal_aslot__G2.Mal_aslot_W.EV).
Local Abbreviation rw_agrees := (§6§ U.Mal_aslot__G2.Mal_aslot_W.rw_agrees).
Local Abbreviation leaf_fact := (@U.Mal_aslot__G2.Mal_aslot_W.leaf_fact s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K).
Local Abbreviation ZF_holds := (§6§ U.Mal_aslot__G2.Mal_aslot_W.ZF_holds).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Definition e_maskA (x : member) : sv := ltac2:(tb__ "0|0|
S29S2bS72S15Vx;A1A1A1S2dS72S24Vx;A1A1A1A2").

Definition e_freedT (x : member) : sv := ltac2:(tb__ "0|0|
S29S2bS72S15Vx;A1A1A1S54SadS52Z0A1S54Sb0S52Z2A1S72S24Vx;A1A1A3A3A2").

Definition e_avT : sv := ltac2:(tb__ "0|1|
S54SadS72PabA1M0S2aG0A1A3").

Definition e_bncdec : sv := SAlu ALU_ADD (v 170) (SLit (-1)).

Definition maskA (x : member) : Z := ltac2:(tb__ "0|1|
S99S7cScVs;Vm0;Vx;A3M0A1S7fS7bG0A1A1A2").

Lemma maskA_range x : ltac2:(tb__ "0|1|
S1S90Z0S15bVx;A1M0A2S92G0S97Z2Z20A2A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. exact (land_fa_range x). Qed.

Lemma ze_maskA x : ltac2:(tb__ "0|0|
S0S4cS143S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15fVx;A1A3S144S15bVx;A1A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_maskA, e_and, maskA. rewrite ze_alu, ze_sx_freed, ze_onesw_byte. cbn [zalu].
  rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by apply WalkArith.sx32_range. apply land_freed_act.
Qed.

Lemma negw_sll2_bits (f b : Z) (a := b mod 32) : ltac2:(tb__ "0|5|
S1S90Z0M0Vf;A2S92Vf;S97Z2M1Z20M2A2M3A2A2S90G0Vb;A2S0S4cS99Vf;S95S94G0S95S9bG1S95Vb;G2A2M4A2G3A2A2G3A2A2S9aVf;S7fG4A1A2A3F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hf Hb. set (k := b mod 32). assert (Hk : 0 <= k < 32) by (subst k; apply Z.mod_pos_bound; lia).
  assert (P : Z.shiftl 2 k = 2 ^ (k + 1)).
  { rewrite Z.shiftl_mul_pow2 by lia. change 2 with (2 ^ 1) at 1. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite P. unfold ones.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
  destruct (Z_lt_dec i 32) as [Hi32|Hi32].
  2:{ assert (T : Z.testbit f i = false).
      { destruct (Z.eq_dec f 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 32); [|lia].
        apply Z.log2_lt_pow2; lia. }
      rewrite T. reflexivity. }
  f_equal.
  assert (M : forall x, Z.testbit (x mod 2 ^ 32) i = Z.testbit x i) by (intros x; apply Z.mod_pow2_bits_low; lia).
  destruct (Z.eq_dec k 31) as [->|Hk31].
  -
    change (2 ^ (31 + 1)) with (2 ^ 32). rewrite Z_mod_same_full. change ((0 - 0) mod 2 ^ 32) with 0. rewrite Z.bits_0.
    replace (2 ^ 32 - 1) with (Z.ones 32) by reflexivity. rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite (Z.mod_small (2 ^ (k + 1))) by (split; [lia|]; apply Z.pow_lt_mono_r; lia).
    rewrite M. replace (0 - 2 ^ (k + 1)) with (- 2 ^ (k + 1)) by lia.
    rewrite Z.bits_opp by lia. replace (Z.pred (2 ^ (k + 1))) with (Z.ones (k + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
    replace (2 ^ (k + 1) - 1) with (Z.ones (k + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
    reflexivity.
Qed.

Lemma ze_freedT x : ltac2:(tb__ "0|1|
S0S4cS95S143S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15eVx;A1A3S97Z2Z20A2A2S9aS7cScVs;Vm0;Vx;A3M0A1S7fS7bG0A1A1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_freedT, e_and. rewrite ze_alu, ze_sx_freed, ze_aluw, ze_lit, ze_aluw, ze_lit, ze_byte. cbn [zalu].
  pose proof (mem_R x) as (R1 & R2 & _ & R4 & _). pose proof (Hbytes x) as (B1 & B2 & _).
  change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2. change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0.
  rewrite (Z.mod_small (mbyte x) (2 ^ 32)) by lia.
  set (XX := (Z.shiftl 2 (mbyte x mod 32)) mod 2 ^ 32).
  rewrite (ZBits.sx32_mod32 XX) by (subst XX; apply Z.mod_pos_bound; lia).
  set (YY := (0 - XX) mod 2 ^ 32). assert (HY : 0 <= YY < 2 ^ 32) by (subst YY; apply Z.mod_pos_bound; lia).
  rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by (apply WalkArith.sx32_range; lia).
  rewrite ZBits.sx32_land by lia. rewrite ZBits.sx32_mod32 by (pose proof (MallocWfSlot.land_le_l (am_freed (mam x)) YY ltac:(lia)); split; [apply Z.land_nonneg; lia | lia]).
  subst YY XX. rewrite negw_sll2_bits by lia. rewrite B2. reflexivity.
Qed.

Lemma ze_avT : ltac2:(tb__ "0|0|
S0S4cS95S143S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15cA3S97Z2Z20A2A2S94Vmaskv;S7aVmaskv;A1A2A3").
Proof using Hbnc Hgd Hmaskv Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_avT. rewrite ze_aluw, ze171, (ze_lowbit_sx (v 171) maskv ze171 Hmaskv). cbn [zalu].
  pose proof Hmaskv as R. pose proof (lowbit_range _ R) as LR.
  rewrite (ZBits.sx32_mod32 maskv) by lia. rewrite (ZBits.sx32_mod32 (lowbit maskv)) by lia.
  rewrite (Z.mod_small (maskv - lowbit maskv)) by lia. rewrite ZBits.sx32_mod32 by lia. reflexivity.
Qed.

Lemma ze_bncdec : ltac2:(tb__ "0|0|
S2S0S4cVbnc;Z0A3A1S0S4cS143S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15dA3S94Vbnc;Z1A2A3F_;").
Proof using Hbnc Hgd Hsc. drop_sp.
  intros Hb. unfold e_bncdec. rewrite ze_alu, ze170, ze_lit. cbn [zalu]. pose proof Hbnc.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). replace (bnc + (2 ^ 64 - 1)) with ((bnc - 1) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma zfact_of rhoX Lf w p : ltac2:(tb__ "0|0|
Sd7VrhoW;VrhoX;A2S13fSa5VK;VLf;VrhoX;Vw;A5S9cS50Vp;S53VLf;A1A3S0S41S12dSd6Vp;A2S40A3S0S41S142Vp;A1S40A3S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfVp;A3F_;F_;F_;F_;F_;").
Proof using mW. drop_sp. intros. eapply leaf_fact; eauto. Qed.

Lemma bnc_out_of x rhoX Lf w : ltac2:(tb__ "0|0|
Sd7VrhoW;VrhoX;A2S13fSa5VK;VLf;VrhoX;Vw;A5S9cS50S57SafS52Z1fA1S21Vx;A1A3S53VLf;A1A3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2A1F_;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hsc mW maskv req rho spanv. drop_sp.
  intros Hag HSP Hin R. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin ltac:(destruct x; reflexivity) ltac:(destruct x; reflexivity)) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze_lit, ze_bncidx in Z0. change (31 mod 2 ^ 64) with 31 in Z0.
  rewrite Z.mod_small in Z0 by lia. apply Z.ltb_lt in Z0. lia.
Qed.

Lemma bnc_in_of x rhoX Lf w : ltac2:(tb__ "0|0|
Sd7VrhoW;VrhoX;A2S13fSa5VK;VLf;VrhoX;Vw;A5S9cS50S59S57SafS52Z1fA1S21Vx;A1A3A1S53VLf;A1A3S1S90Z7Vsc;A2S92Vsc;Z27A2A2F_;F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc mW maskv req rho spanv. drop_sp.
  intros Hag HSP Hin. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin ltac:(destruct x; reflexivity) ltac:(destruct x; reflexivity)) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze_lit, ze_bncidx in Z0. change (31 mod 2 ^ 64) with 31 in Z0.
  pose proof Hsc. destruct (Z_lt_dec sc 7).
  - exfalso. apply Z0. apply Z.ltb_lt.
    replace ((sc - 7) mod 2 ^ 64) with (sc - 7 + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia). lia.
  - rewrite Z.mod_small in Z0 by lia. rewrite Z.ltb_lt in Z0. lia.
Qed.

Lemma bnc_zero_of rhoX Lf w : ltac2:(tb__ "0|1|
Sd7VrhoW;VrhoX;A2S13fSa5VK;VLf;VrhoX;Vw;A5S9cS50S57Sb1S72PaaA1S52Z0M0A1A3S53VLf;A1A3S0S4cVbnc;G0A3F_;F_;F_;").
Proof using Hbnc Hgd Hsc L byA byB byC byM0 byP m0 mW maskv req rho s spanv. drop_sp.
  intros Hag HSP Hin. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin eq_refl eq_refl) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze170, ze_lit in Z0. change (0 mod 2 ^ 64) with 0 in Z0. apply Z.eqb_eq in Z0. exact Z0.
Qed.

Lemma bnc_nz_of rhoX Lf w : ltac2:(tb__ "0|1|
Sd7VrhoW;VrhoX;A2S13fSa5VK;VLf;VrhoX;Vw;A5S9cS50S59S57Sb1S72PaaA1S52Z0M0A1A3A1S53VLf;A1A3S2S0S4cVbnc;G0A3A1F_;F_;F_;").
Proof using Hbnc Hgd Hsc L byA byB byC byM0 byP m0 mW maskv req rho s spanv. drop_sp.
  intros Hag HSP Hin. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin eq_refl eq_refl) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze170, ze_lit in Z0. change (0 mod 2 ^ 64) with 0 in Z0. intros E. apply Z0. apply Z.eqb_eq. exact E.
Qed.

Lemma zf_T171 : ltac2:(tb__ "0|2|
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S3bS50S59S57Sb1S72PabA1M0S52Z0A1M1A3A1S3bS50S59S57Sb1S2aG0A1G1A3A1S3bS50S6bS2cG0A1S52Z1fA1A2S3bS50S6bS72PaaA1S52ZffA1A2S42S50A1A3A3A3A3A3").
Proof using Hbnc Hgd Hmaskv Hsc Hsp. try clear Hsp_high. try clear Hdepth. exact ZF_T. Qed.

Lemma facts_incl_sound (nf fs : list sprop) : ltac2:(tb__ "0|0|
S0S41S9dS50S50S9fS50S65R1A1Vfs;A3Lp;Vnf;A3S40A3S50S9cS50R1Vnf;A3S9cS50R2Vfs;A3F_;Fp;F_;").
Proof using . drop_sp.
  intros H p Hp. pose proof (proj1 (forallb_forall _ _) H p Hp) as E. apply existsb_exists in E as (q & Hq & Eq).
  apply sprop_eqb_sound in Eq. subst q. exact Hq.
Qed.

Lemma linkT (LAs ST : sstate) (me : sv) (nf : list sprop) rhoX w : ltac2:(tb__ "0|7|
S0S41S6fVST;A1S40A3S0S3dS43S3eS43S4fS4fA2M0A1M1S3eS50A1M2A2M3A1S14fVLAs;VST;A2S3fG3S45G1G2S3bG0S45S4fS4fVme;S4ePabA1A4S42G0A1A3Vnf;A4A2A3Sd7VrhoW;VrhoX;A2S0S41S12eSd6Vme;A2S40A3S0S41S145Vme;A1S40A3S0S4cS143S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM4S1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM5Vme;A3S144Vmaskv;A1A3S0S41S9dS50S50S9fS50S65R1A1S53VST;A1M6A3Lp;Vnf;A3S40A3S0S41S9dS50S12dSd6A1G6A3S40A3S0S41S9dS50S142G6A3S40A3Sd9S50S140G4G5A2G6A3S13fSa5VK;VLAs;VrhoX;Vw;A5S13fSa5VK;VST;VrhoX;Vw;A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using mW. drop_sp.
  intros Hwf Hsd Hag Hv Hs Hme Hincl Hnv Hns Hnz HSP.
  eapply (SP_restate segsU K rhoX LAs ST w _ nf Hwf Hsd).
  - constructor; [|constructor]. cbn [fst snd].
    rewrite (EV rhoX me Hag Hv Hs), Hme. cbn [eval]. rewrite (rw_agrees rhoX 171%positive Hag eq_refl).
    rewrite <- (Z_to_bv_bv_unsigned 64 (rw1 171%positive)). change (bv_unsigned (rw1 171%positive)) with (zr1 171%positive). rewrite zr1_171. reflexivity.
  - apply Forall_forall. intros p Hp. apply (facts_incl_sound nf (ss_facts ST) Hincl) in Hp.
    exact (proj1 (Forall_forall _ _) (ZF_holds rhoX (ss_facts ST) Hag Hnv Hns Hnz) p Hp).
  - exact HSP.
Qed.

Lemma smatch_rename : ltac2:(tb__ "0|3|
S4dS41F_;S70S70S67S67S43S3eSdaA1S14cA2S4dS0S41R7R1A1S40A3S0SaaQ40A1M0S55R7R2A2S55R6R2A2A3F_;Fu;S4dS0S3eSaaQ8A1M1A1S6eR7R1A2S6eR6R1A2A3Fl;S0G0S3dG1A1F_;S64R7A1S64R6A1A3S0S41S6fR5A1S40A3S0S4cS66R6A1S66R7A1A3S0S3eS4fA1S62R7A1S62R8A1A3S0S60S61R8A1S61R9A1A3S0S3dS4fA1M2S63R9A1S63RaA1A3S0S3eS51A1S58RaA1S58RbA1A3S0S41S9dS4fS12eRfA1S62RcA1A3S40A3S0S41S60S41Lx;S61RdA1S40S4fS12eR11R1A2Le;X60x2S40A3S0S41G2S41Lx;S63ReA1S4fS12eR12R1A2Le;S40X3dx2S40A3S0S41S9dS51S12cR12A1S58RfA1A3S40A3S0S41S9dS50S12dR13A1S53RfA1A3S40A3S50S9cS50R1S53R11A1A3S9cS50R2S53R13A1A3F_;Fp;S4cS1S90Z1R1A2S90R1Z1fA2A2S0G0S6dR15S5cR13R2A2A2S6dR16S5cR14R2A2A2A3F_;Fr;S5aSa5R15R13R11A4S5aSa5R15R13R12A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;FS';FS;FrhoB;FrhoA;Ff;").
Proof using Hbnc Hgd Hsc rho. drop_sp.
  intros f rhoA rhoB S S' [tr [msX mdX]] Hv Hl Hm Hwf Epc Efr Efc Ers Eob Hfr Hfc Hrv Hob Hfa Hincl Hregs Hsm.
  destruct Hsm as (Hwf0 & Hpc & Hpend & Hhalt & HromX & HrocX & HregsA & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (NTH : forall (l : list sv) n, forallb (sv_vars_all f) l = true -> sv_vars_all f (nth n l (SLit 0)) = true).
  { intros l. induction l as [|x t IH]; intros n Hfl; destruct n; cbn in *; try reflexivity;
      apply andb_prop in Hfl as [A B]; [exact A | apply IH; exact B]. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [rewrite Epc; exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact HromX|]. split; [exact HrocX|].
  split. { intros r Hr. pose proof (bv_unsigned_in_range _ r) as RR0. change (bv_modulus 5) with 32 in RR0.
           rewrite (Hregs (bv_unsigned r) ltac:(lia)). apply HregsA. exact Hr. }
  split. { intros r. unfold freg_sv in *. rewrite Efr. rewrite <- (eval_agree_vars f rhoA rhoB _ Hv Hl (NTH _ _ Hfr)). apply Hfregs. }
  split. { rewrite Efc. destruct (ss_fcsr S); cbn in *; [exact Hfcsr|]. rewrite <- (eval_agree_vars f rhoA rhoB _ Hv Hl Hfc). exact Hfcsr. }
  split. { rewrite Ers. unfold resv_match in *. destruct (ss_resv S); destruct (ms_resv msX); try exact Hresv.
           rewrite <- (eval_agree_vars f rhoA rhoB _ Hv Hl Hrv). exact Hresv. }
  split.
  { rewrite Eob. destruct Hmem as (Hall & Hpd & Hfrm). split; [|split].
    - apply Forall_forall. intros o Hin. eapply obj_holds_agree_vars; eauto.
      + apply (proj1 (forallb_forall _ _) Hob). exact Hin.
      + exact (proj1 (Forall_forall _ _) Hall o Hin).
    - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd.
      erewrite map_ext_in; [exact Hpd|]. intros o Hin. eapply obj_range_agree_vars; eauto.
      apply (proj1 (forallb_forall _ _) Hob). exact Hin.
    - intros a Ha. rewrite <- Hm. apply Hfrm. unfold outside_all in *.
      apply Forall_forall. intros o Hin. cbn zeta.
      rewrite <- (obj_range_agree_vars f rhoA rhoB o Hv Hl (proj1 (forallb_forall _ _) Hob o Hin)).
      exact (proj1 (Forall_forall _ _) Ha o Hin). }
  apply Forall_forall. intros p Hin. apply (holds_agree_vars f rhoA rhoB p Hv Hl).
  - apply (proj1 (forallb_forall _ _) Hfa). exact Hin.
  - exact (proj1 (Forall_forall _ _) Hfacts p (Hincl p Hin)).
Qed.

Lemma ND : List.NoDup (keys s). Proof using HI. exact (proj1 (inv_keys HI)). Qed.

Lemma active_len : length (st_active s) = 48%nat. Proof using HI. exact (proj1 (inv_ctx HI)). Qed.
Lemma bounces_len : length (st_bounces s) = 32%nat. Proof using HI. exact (proj1 (proj2 (proj2 (proj2 (inv_ctx HI))))). Qed.

Lemma active_hd_set_hd t c vv : ltac2:(tb__ "0|1|
S0S49S47S3dS73A1M0S80Vt;A1A2U30A3S1S90Z0Vc;A2S92Vc;Z30A2A2S0G0S33Sa4Vc;Vvv;Vt;A3Vc;A2Vvv;A3F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hl Hc. unfold active_hd, set_hd, set_active. destruct t. cbn - [lupd Z.to_nat nth] in *.
  rewrite nth_lupd. rewrite Nat.eqb_refl. cbn [andb]. rewrite Hl.
  replace (Z.to_nat c <? 48)%nat with true; [reflexivity|]. symmetry. apply Nat.ltb_lt. lia.
Qed.

Lemma xraw_upd_meta q x t : ltac2:(tb__ "0|0|
S14bVX;Vt;A2S0S41S39Vq;VX;A2S44A3S14bVX;S15aVq;Vx;Vt;A3A2F_;F_;").
Proof using . drop_sp.
  intros HX Hq p Hp. rewrite MT_upd_other; [exact (HX p Hp)|]. intros ->.
  unfold memb in Hq. assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hp | apply sptr_eqb_refl]).
  rewrite E in Hq. discriminate.
Qed.
Lemma xraw_set_hd c vv t : ltac2:(tb__ "0|0|
S14bVX;Vt;A2S14bVX;Sa4Vc;Vvv;Vt;A3A2F_;").
Proof using . drop_sp. intros HX p Hp. rewrite MT_set_hd. exact (HX p Hp). Qed.
Lemma xraw_set_bounces l t : ltac2:(tb__ "0|0|
S14bVX;Vt;A2S14bVX;S8fVl;Vt;A2A2F_;").
Proof using . drop_sp. intros HX p Hp. exact (HX p Hp). Qed.
Lemma xraw_s6 t q am : ltac2:(tb__ "0|0|
S14bVX;Vt;A2S0S41S39Vq;VX;A2S44A3S14bVX;S131Vt;Vq;Vam;A3A2F_;F_;").
Proof using . drop_sp.
  intros HX Hq. unfold s6. apply xraw_upd_meta; [|exact Hq]. unfold s5.
  destruct (bounce_idx (am_sc am)) as [k|]; [destruct (_ =? 0)|]; try apply xraw_set_bounces; unfold s4; apply xraw_upd_meta; assumption.
Qed.
Lemma memb_used x : ltac2:(tb__ "0|0|
S0S41S39S11Vs;Vm0;Vx;A3VX;A2S44A3").
Proof using HI Hhd Hsc. drop_sp. exact (proj2 (usedX_MT _ _ _ _ (proj1 (mam_used x)))). Qed.

Lemma lupd_lupd {A} (l : list A) i (a b : A) : ltac2:(tb__ "0|0|
S0S3eVA;A1S8aVA;S8aVA;Vl;Vi;Va;A4Vi;Vb;A4S8aVA;Vl;Vi;Vb;A4A3").
Proof using . drop_sp. revert i. induction l as [|x t IH]; intros [|i]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma set_hd_set_hd t c a b : ltac2:(tb__ "0|0|
S0S75Sa4Vc;Vb;Sa4Vc;Va;Vt;A3A3Sa4Vc;Vb;Vt;A3A3").
Proof using . drop_sp. unfold set_hd, set_active. destruct t. cbn. f_equal. apply lupd_lupd. Qed.

Lemma st_active_set_hd t c vv : ltac2:(tb__ "0|1|
S0S3eS3dS73A1M0A1S80Sa4Vc;Vvv;Vt;A3A1S8aG0S80Vt;A1S98Vc;A1Vvv;A4A3").
Proof using . drop_sp. destruct t; reflexivity. Qed.
Lemma len_set_hd t c vv : ltac2:(tb__ "0|1|
S0S49S47S3dS73A1M0S80Sa4Vc;Vvv;Vt;A3A1A2S47G0S80Vt;A1A2A3").
Proof using . drop_sp. rewrite st_active_set_hd. apply lupd_length. Qed.

Lemma keys_set_hd t c vv : ltac2:(tb__ "0|0|
S0S3eS73A1S32Sa4Vc;Vvv;Vt;A3A1S32Vt;A1A3").
Proof using . drop_sp. destruct t; reflexivity. Qed.
Lemma st_active_upd_meta t q x : ltac2:(tb__ "0|0|
S0S3eS3dS73A1A1S80S15aVq;Vx;Vt;A3A1S80Vt;A1A3").
Proof using . drop_sp. destruct t; reflexivity. Qed.

Lemma am_next_mam x : ltac2:(tb__ "0|0|
S0S3dS73A1S8cScVs;Vm0;Vx;A3A1S3fS73S161Vs;S11Vs;Vm0;Vx;A3A2A2A3").
Proof using HI Hhd Hsc. drop_sp. destruct (mnext_used x) as (n & Hn & En). rewrite Hn, <- En. reflexivity. Qed.
Lemma am_prev_mam x : ltac2:(tb__ "0|0|
S0S3dS73A1S7eScVs;Vm0;Vx;A3A1S3fS73S162Vs;S11Vs;Vm0;Vx;A3A2A2A3").
Proof using HI Hhd Hsc. drop_sp. destruct (mprev_used x) as (p & Hp & Ep). rewrite Hp, <- Ep. reflexivity. Qed.

Lemma nonhead_avail0 x : ltac2:(tb__ "0|0|
S2S0S73S11Vs;Vm0;Vx;A3SbVm0;A1A3A1S0S4cS82ScVs;Vm0;Vx;A3A1Z0A3F_;").
Proof using HI HMI Hbnc Hgd Hhd Hsc. drop_sp.
  intros Hx. destruct (proj1 (proj2 (inv_rings HI)) sc Hsc) as (msr & _ & _ & _ & R1 & _).
  destruct (mam_used x) as (Hu & Hs & _). pose proof (mem_R x) as (Ra & _).
  destruct (Z.eq_dec (am_avail (mam x)) 0) as [E|E]; [exact E|]. exfalso.
  pose proof (R1 _ _ Hu Hs E) as Hh. rewrite Hhd in Hh. injection Hh as Hh. apply Hx. symmetry. exact Hh.
Qed.

Lemma xraw_upd_meta_ptr x xs t : ltac2:(tb__ "0|0|
S14bVX;Vt;A2S14bVX;S15aS11Vs;Vm0;Vx;A3Vxs;Vt;A3A2F_;").
Proof using HI Hhd Hsc. drop_sp. intros HX. apply xraw_upd_meta; [exact HX | apply memb_used]. Qed.

Lemma ta_post_of f s' : ltac2:(tb__ "0|1|
S0S79S75S43S4cS75A2M0A2S86Vsc;Vs;A2S78S75G0S45S4cS75Vf;Vs';A4A3A3S2S0S4cVf;Z0A3A1S154VX;VU;Vs;Vsc;Vf;Vs';A6F_;F_;").
Proof using HI Hsc. drop_sp.
  intros E Hf.
  pose proof (try_avail_spec X U s sc (fun r => fst r <> 0 -> ta_post X U s sc (fst r) (snd r)) HI Hsc
                ltac:(intros s1 _ _ _ _ H; exfalso; exact (H eq_refl)) ltac:(intros f1 s1 H _; exact H)) as T0.
  rewrite E in T0. cbn [itok fst snd] in T0. exact (T0 Hf).
Qed.

Lemma loc_meta x dd : ltac2:(tb__ "0|1|
S0S4cS34VL;S3aS8eS11Vs;Vm0;Vx;A3M0Vdd;A2A1A2S91S25VL;G0A2Vdd;A2A3").
Proof using Hbnc Hgd Hsc rho. drop_sp. unfold zA, addr_of, loc_addr. destruct (mptr x); cbn [padd]. lia. Qed.
Lemma loc_ctx off : ltac2:(tb__ "0|0|
S0S4cS34VL;S30Voff;A1A2S91Z5a3d0Voff;A2A3").
Proof using HMI. drop_sp. unfold loc_addr. rewrite Hctx. reflexivity. Qed.

Lemma in_meta_locs_range x l : ltac2:(tb__ "0|3|
S9cS2eVl;Sa2S11Vs;Vm0;Vx;A3M0A1A3S1S90S25VL;G0A2M1S34VL;Vl;A2M2A2S92G2S91G1Z28A2A2A2F_;").
Proof using Hbnc Hgd Hsc rho. drop_sp.
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite loc_meta; lia.
Qed.

End T.
End Mal_aslot_T.

Module Mal_aslot_VD2sh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VD2sh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S36VX;S46S43S73S4cA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S90Z0Vreq;A2S90S91Vreq;S81A2S85Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3dS73A1S33Vs;Vsc;A2S3fS73Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S38S37VX;Vs;Vsc;A3S3fS73Vm0;A2S3bS73Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§7§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§7§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§7§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§7§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§7§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§7§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§7§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls2 := (@U.Mal_aslot__G1.Mal_aslot_I.cls2 s X sc Hsc m0 rest Rg).
Local Notation "§8§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§8§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§8§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S153S146VX;S46S43S73S4cA2A1VU;S14eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S16S1S1S90Z0M0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S92G1Z100A2A2S1S0S4cS95G1Z20A2S7bScVs;Vm0;R1A3M2A1A3S2S0S4cS83G2A1G0A3A1S0S4cS1eVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bScVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§9§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§9§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§10§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§10§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§10§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§11§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§11§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§11§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§11§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§11§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§11§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§10§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S90Z1000SacQ40S55Vrho;PaA2A2M0A2S0S4cS95G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S90S141Z40SacQ40S55Vrho;PfA2A2A2M0S96S150Z0A1A1A2S90S96S97Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S90S14aVL;A1S91SacQ40M0S55Vrho;PaA2A2S141Z40SacG0S55Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§12§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§12§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§13§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§13§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§11§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§13§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§13§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§13§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§13§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;Vrd0;Sd4Sa5VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SaaQ40A1S41F_;Vwok0;Sd5Sa5VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z60A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ecR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z20A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ccR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S16S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S25VL;S84ScVs;Vm0;R1A3A1A2Z8A2A2A3S3fG1SabG0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S91Z5a3d0Z369A2Vsc;A2A2A3S3fG1SabG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S148S147Vrd0;SaaQ40A1S40L_;A2S149S146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147Sd4Sa5VmW;A2Sd5Sa5VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§14§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§14§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§15§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§15§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§11§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§11§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§11§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S0S4cVbnc;S87S94Vsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§16§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§16§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§10§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S155Sa5VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S3eSdaA1SdbOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§17§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§17§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§18§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§18§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§19§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§19§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§20§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§20§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§7§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§13§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§13§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§21§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§21§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§22§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§22§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§23§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§23§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§24§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§24§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§24§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§21§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§18§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§25§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§25§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§25§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§25§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§8§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§8§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§8§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§9§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;VmW;S64Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0SdcVvm;SddVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3eSdaA1M0SdbVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0SdbR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S5aSa5Vrho;S152S151A1S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 2%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S4cS82ScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S4cS7cScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S0S4cS7cScVs;Vm0;S6A3M0A1S7fS88G0A1A1A3").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S4cVmaskv;ScbVs;Vm0;S6A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SbVm0;A1A2S3fS74S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls2 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls2 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MA_).
Definition xn : mslot := ltac2:(tb__ "0|1|
S76S7dS7eScVs;Vm0;S6A3M0A1S3fS73S7Vs;Vm0;A2A2G0A3A1").
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|2|
S7dS3fS73S7Vs;Vm0;A2A2M0G0S7dS7eScVs;Vm0;S6A3M1A1G0G1A3A3").
Definition s1V : astate := ltac2:(tb__ "0|1|
S12fVs;Vsc;SbVm0;A1Vam0;S7Vs;Vm0;A2M0G0S11dS124A8").
Definition s2V : astate := ltac2:(tb__ "0|1|
Sa4Vsc;S3fS73S7Vs;Vm0;A2M0A2S12fVs;Vsc;SbVm0;A1Vam0;G0G0S11dS124A8A3").
Definition s3V : astate := ltac2:(tb__ "0|1|
Sa4Vsc;S3fS73S7Vs;Vm0;A2M0A2S12fVs;Vsc;SbVm0;A1Vam0;G0G0S11dS124A8A3").
Lemma HXp : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;S7Vs;Vm0;A2A2S3fS74S11dA2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MA_))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S3dS74A1S2fS130Vs;S7Vs;Vm0;A2M0G0S11dA4G0A2S3fS74S124A2A3").
Proof using . drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|1|
S0S3eS73A1S32S130Vs;S7Vs;Vm0;A2M0G0S11dA4A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MA_). Qed.
Lemma K1b : ltac2:(tb__ "0|1|
S0S3eS73A1S32S133Vs;S7Vs;Vm0;A2M0G0S11dS124A5A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S3eS73A1S32S11cA1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS11cS11Vs;Vm0;S8A3A2S3fS74S76S129A1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS11cS11Vs;Vm0;S6A3A2S3fS74S76S11aA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS11bVq;A2S2fS11cVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S3eS4cA1S77S11bA1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S3dS73A1S33S11bVsc;A2S3fS73S7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S43S3dS73A1M0S75A2M1A2S136Vsc;SbVm0;A1Vam0;Vs;A4S78S75G1S45G0S75S3fS73S7Vs;Vm0;A2A2S11cA4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pA pA xp xn).
  - unfold am0. rewrite (am_prev_mam MM0). f_equal; cbn [mptr]; solve_link.
  - unfold am0. rewrite (am_next_mam MM0). f_equal; cbn [mptr]; solve_link.
  - cbn [mptr]. solve_neq.
  - cbn [mptr]. solve_neq.
  - exact HXp.
  - exact HXn.
  - exact Hhd.
  - exact HVf0.
  - apply active_hd_set_hd; [| exact Hsc]. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S73S7Vs;Vm0;A2S11Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS11cS7Vs;Vm0;A2A2S3fS74S76S11aA1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S137Vsc;S7Vs;Vm0;A2M1S11aS11cA4S78S75G0S45S73S75G1S123A4A3A3").
Proof using HVskip. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pA); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS123S7Vs;Vm0;A2A2S3fS74S76S11aA1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S138Vsc;S7Vs;Vm0;A2M1S11aS123A4S78S75G0S45S73S75G1S11bA4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS11bS7Vs;Vm0;A2A2S3fS74S76S11aA1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S4cS139S11aA1ScbVs;Vm0;S6A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S131S11bS7Vs;Vm0;A2S11aA3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S43S4cS75A2M0A2S86Vsc;Vs;A2S78S75G0S45S4cS75S7aScbVs;Vm0;S6A3A1S119A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S4cS7aScbVs;Vm0;S6A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S154VX;VU;Vs;Vsc;S7aScbVs;Vm0;S6A3A1S119A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S3dS73A1S33S119Vsc;A2S3fS73S7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS119S7Vs;Vm0;A2A2S3fS74S76S132S11aA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S4cS89S11aA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS119S11Vs;Vm0;S8A3A2S3fS74S76S129A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|1|
Sa3Vs;S11cS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3Sa2SbVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pA pA xp xn))); [apply (delta_trans _ (s1b s pA pA xp xn)); [apply (delta_trans _ (s1a s pA pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pA (mam MA_)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sa3S11cS123S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sa3S123S11bS42S2eA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|3|
Sa3Vs;S11bS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3M2A3Sa2SbVm0;A1A1A3G2A3G1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S3bS5S1aS3bS5S1bS3bS5S13S72S12S8A1A1M0A1S3bS5SaS8S72S12S6A1A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G0S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7S3bS5S18S6S72S24S6A1A1A2S3bS5S1cS3bS5S19S3bS5S14S6S72PaaA1A2S42S5A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S3eS51A1S58SbfA1S3bS51S22Sd8S5S51S1dS11eA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D2sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53SbfA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D2sh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S69Z2126cSa9Sa6S5eS46S4fA1S3bS51S22S42S51A1A3S53SbfA1Sb9S44A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S5aSa5VrhoW;S12bS45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4M0A4S5aSa5VrhoW;SbfG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D2sh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S3dS43S3eS43S4fS4fA2M0A1M1S3eS50A1M2A2M3A1S14fSc7Sb6A2S3fG3S45G1G2S3bG0S45S4fS4fSd0S6A1S4ePabA1A4S42G0A1A3S48G1G2Sc3A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D2sh)). Qed.
Lemma swf_ST : swf ST_D2sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S41S9dS50S50S9fS50S65R1A1S53Sb6A1A3Lp;S48S3eS43S4fS4fA2A1S3eS50A1Sc3A3A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S41S9dS50S12dSd6A1S53Sb6A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S41S9dS50S142S53Sb6A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sb6A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D2sh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D2sh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S4dS6aSb6A1Sb9A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D2sh 0 ST_D2sh.
Definition LT1 : sstate := lfs LT_D2sh 1 ST_D2sh.
Definition LT2 : sstate := lfs LT_D2sh 2 ST_D2sh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S128A1A2S120A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S126A1A2S121A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S127A1A2S122A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS120A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS121A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS122A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS120A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS121A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS122A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS11eS120A2S11fA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS11eS121A2S12aA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS11eS122A2S125A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|2|
S0S3eS5A1S11fS3bS5S13S72S12S6A1A1M0A1S3bS5SaS8S52Z0A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G0S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7S42S5A1A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S3eS5A1S125S3cS5S11fS3bS5S14S6ScdA2S42S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S49S47S5VdsF;A2S47S5S11eA2A3S5S9cS5R1VdsF;A3S3S27Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S9cS5R2ScaS11eVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S3eS5A1M0G0S5S9cS5R1ScaR3R2A2A3S9cS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sb3Vk;U3A2S0S3eS51A1S58Sb4SbbVk;Sb6A3A1M0S3bS51S13eS68Sa0S51S22G0A3A1A1S9eS51G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4cS66Sb4SbbVk;Sb6A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3eS4fA1S62Sb4SbbVk;Sb6A3A1Sa6A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S60S61Sb4SbbVk;Sb6A3A1S5eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3dS4fA1S63Sb4SbbVk;Sb6A3A1S46S4fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4fS5cSb4SbbVk;Sb6A3ZaA2S26S72PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S4cS1S90Z1R1A2S90R1Z1fA2A2S0S41Sa7S98R2A1A1S40A3S0S4fS5cSb4SbbVk;Sb6A3R3A2Sa8S98R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D2sh k ST_D2sh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S9cS50S57SafS52Z1fA1S21S6A1A3S53S128A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S9cS50S57Sb1S72PaaA1S52Z0A1A3S53S126A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53S126A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S9cS50S59S57Sb1S72PaaA1S52Z0A1A3A1S53S127A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53S127A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S0S75S135S11bS7Vs;Vm0;A2M1S11aA3S134S11bG1S11aA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2Sa3Vs;S119S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M1G1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3M3A3Sa2SbVm0;A1A1A3G3A3G2A3S3cS2eS3cS2eG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1Sa3Vs;S119S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M1G1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3M3A3Sa2SbVm0;A1A1A3G3A3G2A3S3cS2eS3cS2eG1S3bS2eS30S91S35S94Vsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S0S3eS4cA1S77S119A1S8bS94Vsc;G0A2S94Vbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119SaS6S72S12S6A1A1M0G0S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119S13S72S12S6A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119S14S6ScdA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119SaS8S52Z0A1M0G0S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_M0. split; [exact MTF_M0|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_prev am_set_links optrZ]; reflexivity|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_next am_set_links optrZ]; reflexivity|].
  unfold am1_M0, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1S11fA3S1S9cS5R2S120A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1S12aA3S1S9cS5R2S121A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S5S9cS5R1S125A3S1S9cS5R2S122A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S119R2A11S13bVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3M2A3Sa2SbVm0;A1A1A3G2A3G1A3S3cS2eS3cS2eG0G1A3G0A3A3A3S4S5S5S1S9cS5R1S11fA3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M3A3S34VL;R3A2M4A2S92G4S48S4cS4cG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3M2A3Sa2SbVm0;A1A1A3G2A3G1A3S3cS2eS3cS2eG0S3bS2eS30S91S35S94Vsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S9cS5R1S125A3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M3A3S34VL;R3A2M4A2S92G4S48S4cS4cG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D2sh : ltac2:(tb__ "0|0|
VTR;Z0S13fSa5VK;SbfVrhoW;A4S13dVX;VU;S14eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D2sh)).
  { apply (seg_run 300 SA_D2sh LA_D2sh _ rhoW eq_refl eq_refl runA_D2sh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D2sh _ SA_D2sh LfA LA_D2sh_shape HinA) in HSPA. change (lfs LA_D2sh 0 SA_D2sh) with LA_D2shs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D2shs ST_D2sh (e_maskA MA_) (snd DT_D2sh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D2sh LT_D2sh _ rhoA ST_len ST_next runT_D2sh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D2sh _ _ _ ST_D2sh Lf LT_D2sh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2sh 0 ST_D2sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2sh 0 ST_D2sh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2sh 1 ST_D2sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2sh 1 ST_D2sh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2sh 2 ST_D2sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2sh 2 ST_D2sh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD2sh.
End Mal_aslot_VD2sh.

Module Mal_aslot_VD2nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VD2nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S36VX;S46S43S73S4cA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S90Z0Vreq;A2S90S91Vreq;S81A2S85Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3dS73A1S33Vs;Vsc;A2S3fS73Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S38S37VX;Vs;Vsc;A3S3fS73Vm0;A2S3bS73Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§26§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§26§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§26§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§26§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§26§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§26§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§26§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls2 := (@U.Mal_aslot__G1.Mal_aslot_I.cls2 s X sc Hsc m0 rest Rg).
Local Notation "§27§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§27§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§27§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S153S146VX;S46S43S73S4cA2A1VU;S14eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S16S1S1S90Z0M0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S92G1Z100A2A2S1S0S4cS95G1Z20A2S7bScVs;Vm0;R1A3M2A1A3S2S0S4cS83G2A1G0A3A1S0S4cS1eVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bScVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§28§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§28§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§29§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§29§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§29§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§29§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§29§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§30§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§30§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§30§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§30§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§30§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§30§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§29§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S90Z1000SacQ40S55Vrho;PaA2A2M0A2S0S4cS95G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S90S141Z40SacQ40S55Vrho;PfA2A2A2M0S96S150Z0A1A1A2S90S96S97Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S90S14aVL;A1S91SacQ40M0S55Vrho;PaA2A2S141Z40SacG0S55Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§31§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§31§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§32§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§30§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;Vrd0;Sd4Sa5VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SaaQ40A1S41F_;Vwok0;Sd5Sa5VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z60A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ecR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z20A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ccR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S16S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S25VL;S84ScVs;Vm0;R1A3A1A2Z8A2A2A3S3fG1SabG0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S91Z5a3d0Z369A2Vsc;A2A2A3S3fG1SabG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S148S147Vrd0;SaaQ40A1S40L_;A2S149S146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147Sd4Sa5VmW;A2Sd5Sa5VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§33§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§33§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§26§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§34§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§34§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§35§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§35§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§30§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§30§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§30§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S0S4cVbnc;S87S94Vsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§36§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§36§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S155Sa5VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S3eSdaA1SdbOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§37§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§37§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§38§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§38§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§39§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§39§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§40§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§40§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§26§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§41§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§41§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§32§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§32§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§42§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§42§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§43§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§43§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§44§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§44§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§45§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§45§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§46§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§46§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§46§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§42§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§38§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§47§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§47§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§47§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§47§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§27§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§27§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§27§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§28§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;VmW;S64Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0SdcVvm;SddVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3eSdaA1M0SdbVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0SdbR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S5aSa5Vrho;S152S151A1S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 2%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S4cS82ScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S4cS7cScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S4cS7cScVs;Vm0;S6A3M0A1S7fS88G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S4cVmaskv;ScbVs;Vm0;S6A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SbVm0;A1A2S3fS74S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls2 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls2 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MA_).
Definition xn : mslot := ltac2:(tb__ "0|1|
S76S7dS7eScVs;Vm0;S6A3M0A1S3fS73S7Vs;Vm0;A2A2G0A3A1").
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|2|
S7dS3fS73S7Vs;Vm0;A2A2M0G0S7dS7eScVs;Vm0;S6A3M1A1G0G1A3A3").
Definition s1V : astate := ltac2:(tb__ "0|1|
S12fVs;Vsc;SbVm0;A1Vam0;S7Vs;Vm0;A2M0G0S10aS111A8").
Definition s2V : astate := ltac2:(tb__ "0|1|
S12fVs;Vsc;SbVm0;A1Vam0;S7Vs;Vm0;A2M0G0S10aS111A8").
Definition s3V : astate := ltac2:(tb__ "0|1|
S12fVs;Vsc;SbVm0;A1Vam0;S7Vs;Vm0;A2M0G0S10aS111A8").
Lemma HXp : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;S7Vs;Vm0;A2A2S3fS74S10aA2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MA_))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S3dS74A1S2fS130Vs;S7Vs;Vm0;A2M0G0S10aA4G0A2S3fS74S111A2A3").
Proof using . drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|1|
S0S3eS73A1S32S130Vs;S7Vs;Vm0;A2M0G0S10aA4A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MA_). Qed.
Lemma K1b : ltac2:(tb__ "0|1|
S0S3eS73A1S32S133Vs;S7Vs;Vm0;A2M0G0S10aS111A5A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S3eS73A1S32S109A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS109S11Vs;Vm0;S8A3A2S3fS74S76S116A1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS109S11Vs;Vm0;S6A3A2S3fS74S76S107A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS108Vq;A2S2fS109Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S3eS4cA1S77S108A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S3dS73A1S33S108Vsc;A2S3fS73S7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S43S3dS73A1M0S75A2M1A2S136Vsc;SbVm0;A1Vam0;Vs;A4S78S75G1S45G0S75S3fS73S7Vs;Vm0;A2A2S109A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pA pA xp xn).
  - unfold am0. rewrite (am_prev_mam MM0). f_equal; cbn [mptr]; solve_link.
  - unfold am0. rewrite (am_next_mam MM0). f_equal; cbn [mptr]; solve_link.
  - cbn [mptr]. solve_neq.
  - cbn [mptr]. solve_neq.
  - exact HXp.
  - exact HXn.
  - exact Hhd.
  - exact HVf0.
  - apply active_hd_set_hd; [| exact Hsc]. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S73S7Vs;Vm0;A2S11Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS109S7Vs;Vm0;A2A2S3fS74S76S107A1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S137Vsc;S7Vs;Vm0;A2M1S107S109A4S78S75G0S45S73S75G1S110A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS110S7Vs;Vm0;A2A2S3fS74S76S107A1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S138Vsc;S7Vs;Vm0;A2M1S107S110A4S78S75G0S45S73S75G1S108A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS108S7Vs;Vm0;A2A2S3fS74S76S107A1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S4cS139S107A1ScbVs;Vm0;S6A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S131S108S7Vs;Vm0;A2S107A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S43S4cS75A2M0A2S86Vsc;Vs;A2S78S75G0S45S4cS75S7aScbVs;Vm0;S6A3A1S106A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S4cS7aScbVs;Vm0;S6A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S154VX;VU;Vs;Vsc;S7aScbVs;Vm0;S6A3A1S106A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S3dS73A1S33S106Vsc;A2S3fS73S7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS106S7Vs;Vm0;A2A2S3fS74S76S132S107A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S4cS89S107A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fS106S11Vs;Vm0;S8A3A2S3fS74S76S116A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|1|
Sa3Vs;S109S3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3Sa2SbVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pA pA xp xn))); [apply (delta_trans _ (s1b s pA pA xp xn)); [apply (delta_trans _ (s1a s pA pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pA (mam MA_)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sa3S109S110S42S2eA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sa3S110S108S42S2eA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
Sa3Vs;S108S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3A3Sa2SbVm0;A1A1A3G1A3G1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S3bS5S1aS3bS5S1bS3bS5S13S72S12S8A1A1M0A1S3bS5SaS8S72S12S6A1A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G0S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7S3bS5S18S6S72S24S6A1A1A2S3bS5S1cS3bS5S19S3bS5S14S6S72PaaA1A2S42S5A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S3eS51A1S58SbeA1S3bS51S22Sd8S5S51S1dS10bA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D2nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53SbeA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D2nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S69Z2126cSa9Sa6S5eS46S4fA1S3bS51S22S42S51A1A3S53SbeA1Sb9S44A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S5aSa5VrhoW;S118S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4M0A4S5aSa5VrhoW;SbeG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D2nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S3dS43S3eS43S4fS4fA2M0A1M1S3eS50A1M2A2M3A1S14fSc6Sb5A2S3fG3S45G1G2S3bG0S45S4fS4fSd0S6A1S4ePabA1A4S42G0A1A3S48G1G2Sc2A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D2nh)). Qed.
Lemma swf_ST : swf ST_D2nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S41S9dS50S50S9fS50S65R1A1S53Sb5A1A3Lp;S48S3eS43S4fS4fA2A1S3eS50A1Sc2A3A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S41S9dS50S12dSd6A1S53Sb5A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S41S9dS50S142S53Sb5A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sb5A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D2nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D2nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S4dS6aSb5A1Sb9A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D2nh 0 ST_D2nh.
Definition LT1 : sstate := lfs LT_D2nh 1 ST_D2nh.
Definition LT2 : sstate := lfs LT_D2nh 2 ST_D2nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S115A1A2S10dA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S113A1A2S10eA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S114A1A2S10fA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS10dA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS10eA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dS10fA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS10dA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS10eA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cS10fA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS10bS10dA2S10cA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS10bS10eA2S117A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaS10bS10fA2S112A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|2|
S0S3eS5A1S10cS3bS5S13S72S12S6A1A1M0A1S3bS5SaS8S52Z0A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G0S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7S42S5A1A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S3eS5A1S112S3cS5S10cS3bS5S14S6ScdA2S42S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S49S47S5VdsF;A2S47S5S10bA2A3S5S9cS5R1VdsF;A3S3S27Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S9cS5R2ScaS10bVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S3eS5A1M0G0S5S9cS5R1ScaR3R2A2A3S9cS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sb3Vk;U3A2S0S3eS51A1S58Sb4SbaVk;Sb5A3A1M0S3bS51S13eS68Sa0S51S22G0A3A1A1S9eS51G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4cS66Sb4SbaVk;Sb5A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3eS4fA1S62Sb4SbaVk;Sb5A3A1Sa6A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S60S61Sb4SbaVk;Sb5A3A1S5eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3dS4fA1S63Sb4SbaVk;Sb5A3A1S46S4fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4fS5cSb4SbaVk;Sb5A3ZaA2S26S72PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S4cS1S90Z1R1A2S90R1Z1fA2A2S0S41Sa7S98R2A1A1S40A3S0S4fS5cSb4SbaVk;Sb5A3R3A2Sa8S98R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D2nh k ST_D2nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S9cS50S57SafS52Z1fA1S21S6A1A3S53S115A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S9cS50S57Sb1S72PaaA1S52Z0A1A3S53S113A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53S113A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S9cS50S59S57Sb1S72PaaA1S52Z0A1A3A1S53S114A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53S114A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S0S75S135S108S7Vs;Vm0;A2M1S107A3S134S108G1S107A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2Sa3Vs;S106S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M1G1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3A3Sa2SbVm0;A1A1A3G2A3G2A3S3cS2eS3cS2eG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1Sa3Vs;S106S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M1G1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3A3Sa2SbVm0;A1A1A3G2A3G2A3S3cS2eS3cS2eG1S3bS2eS30S91S35S94Vsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S0S3eS4cA1S77S106A1S8bS94Vsc;G0A2S94Vbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106SaS6S72S12S6A1A1M0G0S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106S13S72S12S6A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106S14S6ScdA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106SaS8S52Z0A1M0G0S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_M0. split; [exact MTF_M0|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_prev am_set_links optrZ]; reflexivity|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_next am_set_links optrZ]; reflexivity|].
  unfold am1_M0, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1S10cA3S1S9cS5R2S10dA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1S117A3S1S9cS5R2S10eA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S5S9cS5R1S112A3S1S9cS5R2S10fA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S106R2A11S13bVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3A3Sa2SbVm0;A1A1A3G1A3G1A3S3cS2eS3cS2eG0G1A3G0A3A3A3S4S5S5S1S9cS5R1S10cA3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M2A3S34VL;R3A2M3A2S92G3S48S4cS4cG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2S7Vs;Vm0;A2A1M0G0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3A3Sa2SbVm0;A1A1A3G1A3G1A3S3cS2eS3cS2eG0S3bS2eS30S91S35S94Vsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S9cS5R1S112A3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M2A3S34VL;R3A2M3A2S92G3S48S4cS4cG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D2nh : ltac2:(tb__ "0|0|
VTR;Z0S13fSa5VK;SbeVrhoW;A4S13dVX;VU;S14eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D2nh)).
  { apply (seg_run 300 SA_D2nh LA_D2nh _ rhoW eq_refl eq_refl runA_D2nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D2nh _ SA_D2nh LfA LA_D2nh_shape HinA) in HSPA. change (lfs LA_D2nh 0 SA_D2nh) with LA_D2nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D2nhs ST_D2nh (e_maskA MA_) (snd DT_D2nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D2nh LT_D2nh _ rhoA ST_len ST_next runT_D2nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D2nh _ _ _ ST_D2nh Lf LT_D2nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2nh 0 ST_D2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2nh 0 ST_D2nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2nh 1 ST_D2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2nh 1 ST_D2nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D2nh 2 ST_D2nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D2nh 2 ST_D2nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD2nh.
End Mal_aslot_VD2nh.

Module Mal_aslot_VD3nh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VD3nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S36VX;S46S43S73S4cA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S90Z0Vreq;A2S90S91Vreq;S81A2S85Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3dS73A1S33Vs;Vsc;A2S3fS73Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S38S37VX;Vs;Vsc;A3S3fS73Vm0;A2S3bS73Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§48§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§48§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§48§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§48§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§48§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§48§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§48§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§49§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§49§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§49§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S153S146VX;S46S43S73S4cA2A1VU;S14eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S16S1S1S90Z0M0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S92G1Z100A2A2S1S0S4cS95G1Z20A2S7bScVs;Vm0;R1A3M2A1A3S2S0S4cS83G2A1G0A3A1S0S4cS1eVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bScVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§50§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§50§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§51§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§51§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§51§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§51§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§51§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§52§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§51§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S90Z1000SacQ40S55Vrho;PaA2A2M0A2S0S4cS95G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S90S141Z40SacQ40S55Vrho;PfA2A2A2M0S96S150Z0A1A1A2S90S96S97Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S90S14aVL;A1S91SacQ40M0S55Vrho;PaA2A2S141Z40SacG0S55Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§53§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§53§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§54§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§54§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§52§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§54§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§54§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§54§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§54§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;Vrd0;Sd4Sa5VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SaaQ40A1S41F_;Vwok0;Sd5Sa5VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z60A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ecR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z20A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ccR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S16S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S25VL;S84ScVs;Vm0;R1A3A1A2Z8A2A2A3S3fG1SabG0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S91Z5a3d0Z369A2Vsc;A2A2A3S3fG1SabG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S148S147Vrd0;SaaQ40A1S40L_;A2S149S146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147Sd4Sa5VmW;A2Sd5Sa5VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§55§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§55§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§48§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§56§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§56§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§57§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§57§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§52§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§52§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§52§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S0S4cVbnc;S87S94Vsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§58§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§51§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S155Sa5VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S3eSdaA1SdbOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§59§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§59§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§60§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§60§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§61§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§61§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§62§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§62§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§48§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§63§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§63§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§54§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§54§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§64§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§64§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§65§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§65§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§66§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§66§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§67§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§67§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§68§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§68§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§68§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§64§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§60§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§69§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§69§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§69§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§69§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§49§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§49§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§49§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§50§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;VmW;S64Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0SdcVvm;SddVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3eSdaA1M0SdbVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0SdbR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S5aSa5Vrho;S152S151A1S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S4cS82ScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S4cS7cScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S4cS7cScVs;Vm0;S6A3M0A1S7fS88G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S4cVmaskv;ScbVs;Vm0;S6A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SbVm0;A1A2S3fS74S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MB).
Definition xn : mslot := (MUsed (mam MA_)).
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|1|
S7dS3fS73SdVs;Vm0;A2A2S8cScVs;Vm0;S6A3M0A1G0A3").
Definition am1_B : ameta := ltac2:(tb__ "0|1|
S7dS7eScVs;Vm0;S9A3M0A1S3fS73S7Vs;Vm0;A2A2G0A3").
Definition s1V : astate := ltac2:(tb__ "0|0|
S12fVs;Vsc;SbVm0;A1Vam0;SdVs;Vm0;A2S7Vs;Vm0;A2Se2Se9A8").
Definition s2V : astate := ltac2:(tb__ "0|0|
S12fVs;Vsc;SbVm0;A1Vam0;SdVs;Vm0;A2S7Vs;Vm0;A2Se2Se9A8").
Definition s3V : astate := ltac2:(tb__ "0|0|
S12fVs;Vsc;SbVm0;A1Vam0;SdVs;Vm0;A2S7Vs;Vm0;A2Se2Se9A8").
Lemma HXp : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SdVs;Vm0;A2A2S3fS74Se2A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MB))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S3dS74A1S2fS130Vs;SdVs;Vm0;A2S7Vs;Vm0;A2M0Se2A4G0A2S3fS74Se9A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|0|
S0S3eS73A1S32S130Vs;SdVs;Vm0;A2S7Vs;Vm0;A2Se2A4A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MB). Qed.
Lemma K1b : ltac2:(tb__ "0|0|
S0S3eS73A1S32S133Vs;SdVs;Vm0;A2S7Vs;Vm0;A2Se2Se9A5A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S3eS73A1S32Se0A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe0S11Vs;Vm0;S8A3A2S3fS74S76SefA1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe0S11Vs;Vm0;S6A3A2S3fS74S76SdfA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe0S11Vs;Vm0;S9A3A2S3fS74S76SeeA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_B, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe1Vq;A2S2fSe0Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S3eS4cA1S77Se1A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S3dS73A1S33Se1Vsc;A2S3fS73S7Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S43S3dS73A1M0S75A2M1A2S136Vsc;SbVm0;A1Vam0;Vs;A4S78S75G1S45G0S75S3fS73S7Vs;Vm0;A2A2Se0A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pB pA xp xn).
  - unfold am0. rewrite (am_prev_mam MM0). f_equal; cbn [mptr]; solve_link.
  - unfold am0. rewrite (am_next_mam MM0). f_equal; cbn [mptr]; solve_link.
  - cbn [mptr]. solve_neq.
  - cbn [mptr]. solve_neq.
  - exact HXp.
  - exact HXn.
  - exact Hhd.
  - exact HVf0.
  - apply active_hd_set_hd; [| exact Hsc]. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S73S7Vs;Vm0;A2S11Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe0S7Vs;Vm0;A2A2S3fS74S76SdfA1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S137Vsc;S7Vs;Vm0;A2M1SdfSe0A4S78S75G0S45S73S75G1Se8A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe8S7Vs;Vm0;A2A2S3fS74S76SdfA1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S138Vsc;S7Vs;Vm0;A2M1SdfSe8A4S78S75G0S45S73S75G1Se1A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSe1S7Vs;Vm0;A2A2S3fS74S76SdfA1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S4cS139SdfA1ScbVs;Vm0;S6A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S131Se1S7Vs;Vm0;A2SdfA3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S43S4cS75A2M0A2S86Vsc;Vs;A2S78S75G0S45S4cS75S7aScbVs;Vm0;S6A3A1SdeA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S4cS7aScbVs;Vm0;S6A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S154VX;VU;Vs;Vsc;S7aScbVs;Vm0;S6A3A1SdeA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S3dS73A1S33SdeVsc;A2S3fS73S7Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSdeS7Vs;Vm0;A2A2S3fS74S76S132SdfA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S4cS89SdfA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSdeS11Vs;Vm0;S8A3A2S3fS74S76SefA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_B : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSdeS11Vs;Vm0;S9A3A2S3fS74S76SeeA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_B | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sa3Vs;Se0S3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3Sa2SbVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pB pA xp xn))); [apply (delta_trans _ (s1b s pB pA xp xn)); [apply (delta_trans _ (s1a s pB pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pB (mam MB)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sa3Se0Se8S42S2eA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sa3Se8Se1S42S2eA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
Sa3Vs;Se1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M0A3A3Sa2SbVm0;A1A1A3G0A3G0A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S3bS5S1aS3bS5S1bS3bS5S13S72S12S8A1A1M0A1S3bS5SaS8S72S12S9A1A1M1S72S12S6A1A1M2S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G1S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7S3bS5S18S6S72S24S6A1A1A2S3bS5SaS9G2G0S72S10S9A1A1S72S17S9A1A1S72S15S9A1A1S72SfS9A1A1A7S3bS5S1cS3bS5S19S3bS5S14S6S72PaaA1A2S42S5A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S3eS51A1S58Sc0A1S3bS51S22Sd8S5S51S1dSe3A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D3nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sc0A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D3nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S69Z2126cSa9Sa6S5eS46S4fA1S3bS51S22S42S51A1A3S53Sc0A1Sb9S44A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S5aSa5VrhoW;Sf1S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4M0A4S5aSa5VrhoW;Sc0G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D3nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S3dS43S3eS43S4fS4fA2M0A1M1S3eS50A1M2A2M3A1S14fSc8Sb7A2S3fG3S45G1G2S3bG0S45S4fS4fSd0S6A1S4ePabA1A4S42G0A1A3S48G1G2Sc4A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D3nh)). Qed.
Lemma swf_ST : swf ST_D3nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S41S9dS50S50S9fS50S65R1A1S53Sb7A1A3Lp;S48S3eS43S4fS4fA2A1S3eS50A1Sc4A3A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S41S9dS50S12dSd6A1S53Sb7A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S41S9dS50S142S53Sb7A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sb7A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D3nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D3nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S4dS6aSb7A1Sb9A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D3nh 0 ST_D3nh.
Definition LT1 : sstate := lfs LT_D3nh 1 ST_D3nh.
Definition LT2 : sstate := lfs LT_D3nh 2 ST_D3nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58SedA1A2Se5A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58SebA1A2Se6A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58SecA1A2Se7A2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSe5A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSe6A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSe7A4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSe5A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSe6A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSe7A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSe3Se5A2Se4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSe3Se6A2Sf0A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSe3Se7A2SeaA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|3|
S0S3eS5A1Se4S3bS5S13S72S12S6A1A1M0A1S3bS5SaS8S52Z0A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6S72S12S9A1A1M2G2S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7S3bS5SaS9G0G0S72S10S9A1A1S72S17S9A1A1S72S15S9A1A1S72SfS9A1A1A7S42S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S3eS5A1SeaS3cS5Se4S3bS5S14S6ScdA2S42S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S49S47S5VdsF;A2S47S5Se3A2A3S5S9cS5R1VdsF;A3S3S27Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S9cS5R2ScaSe3VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S3eS5A1M0G0S5S9cS5R1ScaR3R2A2A3S9cS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sb3Vk;U3A2S0S3eS51A1S58Sb4SbcVk;Sb7A3A1M0S3bS51S13eS68Sa0S51S22G0A3A1A1S9eS51G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4cS66Sb4SbcVk;Sb7A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3eS4fA1S62Sb4SbcVk;Sb7A3A1Sa6A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S60S61Sb4SbcVk;Sb7A3A1S5eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3dS4fA1S63Sb4SbcVk;Sb7A3A1S46S4fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4fS5cSb4SbcVk;Sb7A3ZaA2S26S72PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S4cS1S90Z1R1A2S90R1Z1fA2A2S0S41Sa7S98R2A1A1S40A3S0S4fS5cSb4SbcVk;Sb7A3R3A2Sa8S98R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D3nh k ST_D3nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S9cS50S57SafS52Z1fA1S21S6A1A3S53SedA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S9cS50S57Sb1S72PaaA1S52Z0A1A3S53SebA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53SebA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S9cS50S59S57Sb1S72PaaA1S52Z0A1A3A1S53SecA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S6A1A3A1S53SecA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S0S75S135Se1S7Vs;Vm0;A2M1SdfA3S134Se1G1SdfA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2Sa3Vs;SdeS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1M1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3A3Sa2SbVm0;A1A1A3G2A3G2A3S3cS2eS3cS2eG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1Sa3Vs;SdeS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1M1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3A3Sa2SbVm0;A1A1A3G2A3G2A3S3cS2eS3cS2eG1S3bS2eS30S91S35S94Vsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S0S3eS4cA1S77SdeA1S8bS94Vsc;G0A2S94Vbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeSaS6S72S12S9A1A1M0G0S72S10S6A1A1SccSceS6A1S72SfS6A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeS13S72S12S6A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeS14S6ScdA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeSaS8S52Z0A1M0G0S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_M0. split; [exact MTF_M0|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_prev am_set_links optrZ]; reflexivity|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_next am_set_links optrZ]; reflexivity|].
  unfold am1_M0, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_B' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeSaS9S72S12S6A1A1M0G0S72S10S9A1A1S72S17S9A1A1S72S15S9A1A1S72SfS9A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_B. split; [exact MTF_B|].
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_B, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MB); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MB); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact ok_B' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1Se4A3S1S9cS5R2Se5A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeR2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1Sf0A3S1S9cS5R2Se6A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeR2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S5S9cS5R1SeaA3S1S9cS5R2Se7A3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SdeR2A11S13bVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1M0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3A3Sa2SbVm0;A1A1A3G1A3G1A3S3cS2eS3cS2eG0G1A3G0A3A3A3S4S5S5S1S9cS5R1Se4A3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M2A3S34VL;R3A2M3A2S92G3S48S4cS4cG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MB)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MA_)) (v (vmem MB)) (v (vavail MB)) (v (vfreed MB)) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1M0A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3A3Sa2SbVm0;A1A1A3G1A3G1A3S3cS2eS3cS2eG0S3bS2eS30S91S35S94Vsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S9cS5R1SeaA3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M2A3S34VL;R3A2M3A2S92G3S48S4cS4cG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MB)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MA_)) (v (vmem MB)) (v (vavail MB)) (v (vfreed MB)) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D3nh : ltac2:(tb__ "0|0|
VTR;Z0S13fSa5VK;Sc0VrhoW;A4S13dVX;VU;S14eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D3nh)).
  { apply (seg_run 300 SA_D3nh LA_D3nh _ rhoW eq_refl eq_refl runA_D3nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D3nh _ SA_D3nh LfA LA_D3nh_shape HinA) in HSPA. change (lfs LA_D3nh 0 SA_D3nh) with LA_D3nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D3nhs ST_D3nh (e_maskA MA_) (snd DT_D3nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D3nh LT_D3nh _ rhoA ST_len ST_next runT_D3nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D3nh _ _ _ ST_D3nh Lf LT_D3nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nh 0 ST_D3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nh 0 ST_D3nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nh 1 ST_D3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nh 1 ST_D3nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nh 2 ST_D3nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nh 2 ST_D3nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD3nh.
End Mal_aslot_VD3nh.

Module Mal_aslot_VD3nr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VD3nr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S36VX;S46S43S73S4cA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S90Z0Vreq;A2S90S91Vreq;S81A2S85Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S3dS73A1S33Vs;Vsc;A2S3fS73Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S38S37VX;Vs;Vsc;A3S3fS73Vm0;A2S3bS73Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§70§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§70§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§70§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§70§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§70§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§70§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§70§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls3 := (@U.Mal_aslot__G1.Mal_aslot_I.cls3 s X sc Hsc m0 rest Rg).
Local Notation "§71§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§71§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§71§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S153S146VX;S46S43S73S4cA2A1VU;S14eVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S16S1S1S90Z0M0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S92G1Z100A2A2S1S0S4cS95G1Z20A2S7bScVs;Vm0;R1A3M2A1A3S2S0S4cS83G2A1G0A3A1S0S4cS1eVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bScVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§72§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§72§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§73§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§73§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§73§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§73§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§73§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§74§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§74§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§74§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§74§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§74§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§74§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§73§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S90Z1000SacQ40S55Vrho;PaA2A2M0A2S0S4cS95G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S90S141Z40SacQ40S55Vrho;PfA2A2A2M0S96S150Z0A1A1A2S90S96S97Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S90S14aVL;A1S91SacQ40M0S55Vrho;PaA2A2S141Z40SacG0S55Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§75§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§75§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§76§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§76§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§76§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§76§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§76§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§76§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;Vrd0;Sd4Sa5VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SaaQ40A1S41F_;Vwok0;Sd5Sa5VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z60A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ecR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S4cS1S90Z0R1A2S92R1Z20A2A2S0S3dSaaQ8A1M0A1VmW;SabQ40S91Z108ccR2A2A2A1S46G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S16S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S25VL;S84ScVs;Vm0;R1A3A1A2Z8A2A2A3S3fG1SabG0S1eVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S3dSaaQ8M0A1M1A1Sd4Sa5VmW;SabQ40S91S91Z5a3d0Z369A2Vsc;A2A2A3S3fG1SabG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S148S147Vrd0;SaaQ40A1S40L_;A2S149S146A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S147Sd4Sa5VmW;A2Sd5Sa5VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§77§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§77§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§70§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§78§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§78§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§79§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§79§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§74§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§74§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§74§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S0S4cVbnc;S87S94Vsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§80§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§80§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§73§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S155Sa5VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S3eSdaA1SdbOF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§81§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§81§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§82§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§82§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§83§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§83§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§84§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§84§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§70§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§85§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§85§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§76§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§76§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§86§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§86§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§87§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§87§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§88§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§88§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§89§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§89§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§90§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§90§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§90§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§86§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§82§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§91§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§91§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§91§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§91§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§71§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§71§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§71§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§72§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SaaQ40A1S3dSaaQ8A1A1F_;VmW;S64Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0SdcVvm;SddVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S3eSdaA1M0SdbVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0SdbR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S5aSa5Vrho;S152S151A1S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S4cSacQ40S55Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 3%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S4cS82ScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S4cS7cScVs;Vm0;S8A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S4cS7cScVs;Vm0;S6A3M0A1S7fS88G0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S4cVmaskv;ScbVs;Vm0;S9A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SbVm0;A1A2S3fS74S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls3 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls3 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MB).
Definition xn : mslot := (MUsed (mam MA_)).
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|1|
S7dS3fS73SdVs;Vm0;A2A2S8cScVs;Vm0;S6A3M0A1G0A3").
Definition am1_B : ameta := ltac2:(tb__ "0|1|
S7dS7eScVs;Vm0;S9A3M0A1S3fS73S7Vs;Vm0;A2A2G0A3").
Definition s1V : astate := ltac2:(tb__ "0|0|
S12fVs;Vsc;SbVm0;A1Vam0;SdVs;Vm0;A2S7Vs;Vm0;A2Sf6SfeA8").
Definition s2V : astate := ltac2:(tb__ "0|0|
S12fVs;Vsc;SbVm0;A1Vam0;SdVs;Vm0;A2S7Vs;Vm0;A2Sf6SfeA8").
Definition s3V : astate := ltac2:(tb__ "0|1|
Sa4Vsc;S3fS73SdVs;Vm0;A2M0A2S12fVs;Vsc;SbVm0;A1Vam0;G0S7Vs;Vm0;A2Sf6SfeA8A3").
Lemma HXp : ltac2:(tb__ "0|0|
S0S3dS74A1S2fVs;SdVs;Vm0;A2A2S3fS74Sf6A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MB))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S3dS74A1S2fS130Vs;SdVs;Vm0;A2S7Vs;Vm0;A2M0Sf6A4G0A2S3fS74SfeA2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|0|
S0S3eS73A1S32S130Vs;SdVs;Vm0;A2S7Vs;Vm0;A2Sf6A4A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MB). Qed.
Lemma K1b : ltac2:(tb__ "0|0|
S0S3eS73A1S32S133Vs;SdVs;Vm0;A2S7Vs;Vm0;A2Sf6SfeA5A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S3eS73A1S32Sf3A1S32Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf3S11Vs;Vm0;S8A3A2S3fS74S76S103A1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf3S11Vs;Vm0;S6A3A2S3fS74S76Sf7A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf3S11Vs;Vm0;S9A3A2S3fS74S76Sf5A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_B, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf4Vq;A2S2fSf3Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S3eS4cA1S77Sf4A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S3dS73A1S33Sf4Vsc;A2S3fS73SdVs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S43S3dS73A1M0S75A2M1A2S136Vsc;SbVm0;A1Vam0;Vs;A4S78S75G1S45G0S75S3fS73S7Vs;Vm0;A2A2Sf3A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pB pA xp xn).
  - unfold am0. rewrite (am_prev_mam MM0). f_equal; cbn [mptr]; solve_link.
  - unfold am0. rewrite (am_next_mam MM0). f_equal; cbn [mptr]; solve_link.
  - cbn [mptr]. solve_neq.
  - cbn [mptr]. solve_neq.
  - exact HXp.
  - exact HXn.
  - exact Hhd.
  - exact HVf0.
  - apply active_hd_set_hd; [| exact Hsc]. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S73S7Vs;Vm0;A2S11Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf3S7Vs;Vm0;A2A2S3fS74S76Sf7A1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S43S73S75A2M0A2S137Vsc;S7Vs;Vm0;A2M1Sf7Sf3A4S78S75G0S45S73S75G1SfdA4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSfdS7Vs;Vm0;A2A2S3fS74S76Sf7A1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S79S75S43S73S75A2M0A2S138Vsc;S7Vs;Vm0;A2Sf7SfdA4S78S75G0S45S73S75SdVs;Vm0;A2Sf4A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf4SdVs;Vm0;A2A2S3fS74S76Sf5A1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S4cS139Sf5A1ScbVs;Vm0;S9A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S131Sf4SdVs;Vm0;A2Sf5A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S43S4cS75A2M0A2S86Vsc;Vs;A2S78S75G0S45S4cS75S7aScbVs;Vm0;S9A3A1Sf2A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S4cS7aScbVs;Vm0;S9A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S154VX;VU;Vs;Vsc;S7aScbVs;Vm0;S9A3A1Sf2A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S3dS73A1S33Sf2Vsc;A2S3fS73SdVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf2SdVs;Vm0;A2A2S3fS74S76S132Sf5A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S4cS89Sf5A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf2S11Vs;Vm0;S8A3A2S3fS74S76S103A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S3dS74A1S2fSf2S11Vs;Vm0;S6A3A2S3fS74S76Sf7A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sa3Vs;Sf3S3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3Sa2SbVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pB pA xp xn))); [apply (delta_trans _ (s1b s pB pA xp xn)); [apply (delta_trans _ (s1a s pB pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pB (mam MB)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sa3Sf3SfdS42S2eA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sa3SfdSf4S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
Sa3Vs;Sf4S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M0A3M1A3Sa2SbVm0;A1A1A3G0A3G1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S3bS5S1aS3bS5S1bS3bS5S13S72S12S8A1A1M0A1S3bS5SaS8S72S12S9A1A1M1S72S12S6A1A1M2S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G1S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7S3bS5S18S6S72S24S6A1A1A2S3bS5SaS9G2G0S72S10S9A1A1S72S17S9A1A1S72S15S9A1A1S72SfS9A1A1A7S3bS5S18S9S72S24S9A1A1A2S3bS5S1cS3bS5S19S3bS5S14S9S72PaaA1A2S42S5A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S3eS51A1S58Sc1A1S3bS51S22Sd8S5S51S1dSf8A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D3nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
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
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sc1A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D3nr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S69Z2126cSa9Sa6S5eS46S4fA1S3bS51S22S42S51A1A3S53Sc1A1Sb9S44A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S5aSa5VrhoW;S105S45S3eSdaA1S14cVtr;S14dVms;Vmd;A2A4M0A4S5aSa5VrhoW;Sc1G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D3nr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S3dS43S3eS43S4fS4fA2M0A1M1S3eS50A1M2A2M3A1S14fSc9Sb8A2S3fG3S45G1G2S3bG0S45S4fS4fSd0S9A1S4ePabA1A4S42G0A1A3S48G1G2Sc5A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D3nr)). Qed.
Lemma swf_ST : swf ST_D3nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S41S9dS50S50S9fS50S65R1A1S53Sb8A1A3Lp;S48S3eS43S4fS4fA2A1S3eS50A1Sc5A3A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S41S9dS50S12dSd6A1S53Sb8A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S41S9dS50S142S53Sb8A1A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sd9S50S140S20Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS1fVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S53Sb8A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D3nr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D3nr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S4dS6aSb8A1Sb9A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D3nr 0 ST_D3nr.
Definition LT1 : sstate := lfs LT_D3nr 1 ST_D3nr.
Definition LT2 : sstate := lfs LT_D3nr 2 ST_D3nr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S102A1A2SfaA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S100A1A2SfbA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S41S13aS9eS51S58S101A1A2SfcA2S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSfaA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSfbA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S41S9dS51S12cSd6A1Sd8S5S51S1dSfcA4A3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSfaA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSfbA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S41S9dS5S13cSfcA3S40A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSf8SfaA2Sf9A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSf8SfbA2S104A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S3eS5A1ScaSf8SfcA2SffA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|3|
S0S3eS5A1Sf9S3bS5S13S72S12S9A1A1M0A1S3bS5SaS8S52Z0A1M1G1S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7S3bS5SaS6G0G0S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7S3bS5SaS9S72S12S6A1A1M2G2S72S10S9A1A1SccSceS9A1S72SfS9A1A1A7S42S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S3eS5A1SffS3cS5Sf9S3bS5S14S9ScdA2S42S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S49S47S5VdsF;A2S47S5Sf8A2A3S5S9cS5R1VdsF;A3S3S27Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S9cS5R2ScaSf8VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S3eS5A1M0G0S5S9cS5R1ScaR3R2A2A3S9cS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sb3Vk;U3A2S0S3eS51A1S58Sb4SbdVk;Sb8A3A1M0S3bS51S13eS68Sa0S51S22G0A3A1A1S9eS51G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4cS66Sb4SbdVk;Sb8A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3eS4fA1S62Sb4SbdVk;Sb8A3A1Sa6A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S60S61Sb4SbdVk;Sb8A3A1S5eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S3dS4fA1S63Sb4SbdVk;Sb8A3A1S46S4fA1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S0S4fS5cSb4SbdVk;Sb8A3ZaA2S26S72PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sb3Vk;U3A2S4cS1S90Z1R1A2S90R1Z1fA2A2S0S41Sa7S98R2A1A1S40A3S0S4fS5cSb4SbdVk;Sb8A3R3A2Sa8S98R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D3nr k ST_D3nr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S9cS50S57SafS52Z1fA1S21S9A1A3S53S102A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S9cS50S57Sb1S72PaaA1S52Z0A1A3S53S100A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S9A1A3A1S53S100A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S9cS50S59S57Sb1S72PaaA1S52Z0A1A3A1S53S101A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S9cS50S59S57SafS52Z1fA1S21S9A1A3A1S53S101A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S0S75S135Sf4SdVs;Vm0;A2M1Sf5A3S134Sf4G1Sf5A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2Sa3Vs;Sf2S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1M1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3M3A3Sa2SbVm0;A1A1A3G2A3G3A3S3cS2eS3cS2eG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1Sa3Vs;Sf2S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1M1Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M2A3M3A3Sa2SbVm0;A1A1A3G2A3G3A3S3cS2eS3cS2eG1S3bS2eS30S91S35S94Vsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S90Z7M0Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S0S3eS4cA1S77Sf2A1S8bS94Vsc;G0A2S94Vbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2SaS9S72S12S6A1A1M0G0S72S10S9A1A1SccSceS9A1S72SfS9A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_B). split; [exact MT_R'|].
  pose proof (am_final_fields am1_B) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_B, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MB), ?(am_next_mam MB); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_B; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_B; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_B, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2S13S72S12S9A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2S14S9ScdA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2SaS8S52Z0A1M0G0S72S10S8A1A1S72S17S8A1A1S72S15S8A1A1S72SfS8A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_M0. split; [exact MTF_M0|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_prev am_set_links optrZ]; reflexivity|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_next am_set_links optrZ]; reflexivity|].
  unfold am1_M0, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_A' : ltac2:(tb__ "0|1|
SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2SaS6S72S12S9A1A1M0G0S72S10S6A1A1S72S17S6A1A1S72S15S6A1A1S72SfS6A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_A. split; [exact MTF_A|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_A, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact ok_A' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1Sf9A3S1S9cS5R2SfaA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S90Z7Vsc;A2S92Vsc;Z27A2A2M0A1S1G0S0S4cVbnc;Z0A3A2A2S5S9cS5R1S104A3S1S9cS5R2SfbA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2R2A11S13bVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S90Z7Vsc;A2S92Vsc;Z27A2A2S2S0S4cVbnc;Z0A3A1S5S9cS5R1SffA3S1S9cS5R2SfcA3S1SeVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf2R2A11S13bVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1M0Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3M2A3Sa2SbVm0;A1A1A3G1A3G2A3S3cS2eS3cS2eG0G1A3G0A3A3A3S4S5S5S1S9cS5R1Sf9A3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M3A3S34VL;R3A2M4A2S92G4S48S4cS4cG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MB)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MA_)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S2eS9cS2eR1S3cS2eS3cS2eS3cS2eS3cS2eS3cS2eS3cS2eSa2SdVs;Vm0;A2A1M0Sa2S7Vs;Vm0;A2A1A3S3bS2eS30S91S31S93Z8Vsc;A2A2A1S42S2eA1M1A3M2A3Sa2SbVm0;A1A1A3G1A3G2A3S3cS2eS3cS2eG0S3bS2eS30S91S35S94Vsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S9cS5R1SffA3S1S90S4aS4cS4cS23Vs;VL;Vsc;Vm0;R1A5M3A3S34VL;R3A2M4A2S92G4S48S4cS4cG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MB)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MA_)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D3nr : ltac2:(tb__ "0|0|
VTR;Z0S13fSa5VK;Sc1VrhoW;A4S13dVX;VU;S14eVs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D3nr)).
  { apply (seg_run 300 SA_D3nr LA_D3nr _ rhoW eq_refl eq_refl runA_D3nr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D3nr _ SA_D3nr LfA LA_D3nr_shape HinA) in HSPA. change (lfs LA_D3nr 0 SA_D3nr) with LA_D3nrs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D3nrs ST_D3nr (e_maskA MB) (snd DT_D3nr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D3nr LT_D3nr _ rhoA ST_len ST_next runT_D3nr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D3nr _ _ _ ST_D3nr Lf LT_D3nr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nr 0 ST_D3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nr 0 ST_D3nr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nr 1 ST_D3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nr 1 ST_D3nr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D3nr 2 ST_D3nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D3nr 2 ST_D3nr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD3nr.
End Mal_aslot_VD3nr.
