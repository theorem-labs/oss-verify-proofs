(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MB"; "MC"; "OD_meta"; "MA_"; "MM0"; "vptr"; "mam"; "pB"; "pA"; "OD_mem"; "mptr"; "OD_act"; "OD_bnc"; "od_ok_at"; "pC"; "vbits"; "vmem"; "zl1"; "zr1"; "mbyte"; "OD_ctz"; "OD_got"; "OD_guard"; "OD_sct"; "obj_of"; "vfreed"; "vavail"; "O_stk"; "e_bncidx"; "member"; "vbyte"; "od_range"; "pM0"; "zA"; "e_ctz"; "od_ok"; "MP"; "e_tabidx"; "e_and"; "e_onesw"; "e_sx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "sobj"; "SLit"; "sprop"; "SAluW"; "ss_facts"; "SAlu"; "rw"; "SPBranch"; "reg_sv"; "ss_objs"; "SExt"; "SPNot"; "smatch"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "FcsrFrm0"; "sfcsr"; "ss_next"; "ss_pc"; "sprop_eqb"; "sstate"; "sv_eqb"; "eval"; "mkSS"; "ob_cells"; "rm"; "SLBytes"; "valuation"; "SMd"; "SPUle"; "agree_below"; "holds"; "ss_lenient"; "swf"; "@Corelib.Init.Datatypes"; "cons"; "option"; "bool"; "true"; "Some"; "app"; "list"; "nil"; "prod"; "pair"; "None"; "fst"; "snd"; "false"; "andb"; "negb"; "length"; "nat"; "orb"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "LCtx"; "CTX_active"; "active_hd"; "CTX_bounces"; "loc_addr"; "Inv"; "alinks"; "ring_ok"; "zseq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "sub"; "modulo"; "pow"; "opp"; "to_nat"; "land"; "ltb"; "lxor"; "of_nat"; "eqb"; "ldiff"; "leb"; "lor"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "MUsed"; "st_bounces"; "am_aidx"; "IRet"; "itree"; "class_size"; "lowbit"; "am_freed"; "am_last"; "ones"; "span_loop"; "znth"; "IB"; "am_maplen"; "am_mem"; "am_sc"; "UNIT"; "am_avail"; "try_avail"; "zset"; "size_classes"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "callee_saved"; "pre_reg"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_AND"; "ALU_ADD"; "ALU_SLL"; "BC_LTU"; "BC_EQ"; "ALU_XOR"; "BC_LT"; "ALU_OR"; "M_MUL"; "BC_NE"; "aluop"; "mulop"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "lfs"; "ST_R4sr"; "ST_R5nr"; "ST_R5sh"; "ST_R5sr"; "NXA"; "LT_R4sr"; "LT_R5nr"; "LT_R5sh"; "LT_R5sr"; "SA_R4sr"; "SA_R5nr"; "SA_R5sh"; "SA_R5sr"; "CUTS"; "DT_R4sr"; "DT_R5nr"; "DT_R5sh"; "DT_R5sr"; "LA_R4srs"; "LA_R5nrs"; "LA_R5shs"; "LA_R5srs"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "delta"; "set_hd"; "meta_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "in_vars"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT";
"e_maskA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "toS"; "zholds"; "psupported"; "zsupported"; "sx32"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR4sr.VR4sr"; "sR'"; "s1V"; "s3V"; "am1_C"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "am1_B"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sr.VR5sr"; "sR'"; "s1V"; "s3V"; "am1_C"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "am1_B"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5nr.VR5nr"; "sR'"; "s3V"; "s1V"; "am1_B"; "am1_A"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_VR5sh.VR5sh"; "sR'"; "am1_B"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "am1_A"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sv_vars_all"; "sprop_vars_all"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "keys_distinct"; "setp"; "HITP"; "oStkF"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.L.Entry"; "setsA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "lf_state"; "mkLeaf"; "sym_run"; "stop_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.L.SpanLoop"; "setsX"; "LINV"; "setsB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "diffs_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "as_stack"; "IEC_U"; "Pre_as"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.L"; "e_size"; "e_aidx"; "e_last1"; "e_a40"; "e_a60"; "e_span0"; "rename_chk"; "LINV"; "e_byteL"; "e_byteS"; "e_freedG"; "e_maskG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L"; "span0_of"; "span_exits"; "diff_okb"; "regs_okb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_final"; "s4"; "s5"; "s6"; "step1"; "step2"; "step3"; "t_mask"; "span_cnt"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "sh"].
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

Module Mal_aslot_VR4sr.

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

Section VR4sr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S73VX;S5fS5dS89S69A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S78Z0Vreq;A2S78S79Vreq;S98A2S91Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S56S89A1S70Vs;Vsc;A2S59S89Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S75S74VX;Vs;Vsc;A3S59S89Vm0;A2S55S89Vm0;Vrest;A3A3").
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
S15cS14cVX;S5fS5dS89S69A2A1VU;S151Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S78Z0M0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S7aG1Z100A2A2S1S0S69S7dG1Z20A2S8eSdVs;Vm0;R1A3M2A1A3S2S0S69S99G2A1G0A3A1S0S69S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S8eSdVs;Vm0;R2A3A1A3F_;A2A2Fx;").
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
S1S78Z1000SacQ40S38Vrho;PaA2A2M0A2S0S69S7dG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S78SeaZ40SacQ40S38Vrho;PfA2A2A2M0S7fS159Z0A1A1A2S78S7fS7eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S78S150VL;A1S79SacQ40M0S38Vrho;PaA2A2SeaZ40SacG0S38Vrho;PfA2A2A2A2A2").
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
S0SabQ40A1S56SabQ8A1A1F_;Vrd0;SdcSa6VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SabQ40A1S57F_;Vwok0;SddSa6VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z60A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ecR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z20A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ccR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S28VL;S9aSdVs;Vm0;R1A3A1A2Z8A2A2A3S59G1SadG0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S79Z5a3d0Z369A2Vsc;A2A2A3S59G1SadG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14eS14dVrd0;SabQ40A1S58L_;A2S14fS14cA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14dSdcSa6VmW;A2SddSa6VmW;A2A2").
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
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S0S69Vbnc;S97S7cVsc;G0A2S8dVs;A1A2A3F_;").
Local Notation "§9§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§9§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§3§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15dSa6VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S5bSe4A1Se5OF_;F_;").
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
S0SabQ40A1S56SabQ8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Se6Vvm;Se7Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S5bSe4A1M0Se5VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Se5R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S3eSa6Vrho;S15bS15aA1S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 4%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S69S9dSdVs;Vm0;SbA3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S69S93SdVs;Vm0;SbA3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S0S69S93SdVs;Vm0;SaA3M0A1S95S94G0A1A1A3").
Hypothesis HVact : maskA MB = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S69Vmaskv;SdfVs;Vm0;S8A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dVs;S27Vm0;A1A2S59S8aS8cVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls4 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls4 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition am1_C : ameta := (mam MC).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89S15Vs;Vm0;A2A2Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf0S11Vs;Vm0;SbA3A2S59S8aS8cSffA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf0S11Vs;Vm0;SaA3A2S59S8aS8cSf9A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf0S11Vs;Vm0;S7A3A2S59S8aS8cSfaA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT1_C : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf0S11Vs;Vm0;S8A3A2S59S8aS8cSf2A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_C. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MC)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf1Vq;A2S6dSf0Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S5bS69A1S8dSf1A1S8dVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S56S89A1S70Sf1Vsc;A2S59S89S15Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S90S8bS5dS56S89A1M0S8bA2M1A2S173Vsc;S27Vm0;A1Vam0;Vs;A4S8fS8bG1S5eG0S8bS59S89SfVs;Vm0;A2A2Sf0A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S89SfVs;Vm0;A2S11Vs;Vm0;SaA3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf0SfVs;Vm0;A2A2S59S8aS8cSf9A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S174Vsc;SfVs;Vm0;A2Sf9Sf0A4S8fS8bG0S5eS89S8bSeVs;Vm0;A2Sf8A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf8SeVs;Vm0;A2A2S59S8aS8cSfaA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S175Vsc;SeVs;Vm0;A2SfaSf8A4S8fS8bG0S5eS89S8bS15Vs;Vm0;A2Sf1A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pB am1_B pC); [unfold am1_B; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_B; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MB); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSf1S15Vs;Vm0;A2A2S59S8aS8cSf2A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_C. Qed.
Lemma Hav3 : am_avail am1_C = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_C. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S69S176Sf2A1SdfVs;Vm0;S8A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MC <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S172Sf1S15Vs;Vm0;A2Sf2A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S90S8bS5dS69S8bA2M0A2S9eVsc;Vs;A2S8fS8bG0S5eS69S8bS92SdfVs;Vm0;S8A3A1SefA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S69S92SdfVs;Vm0;S8A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MC). pose proof (lowbit_range (maskA MC) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S16eVX;VU;Vs;Vsc;S92SdfVs;Vm0;S8A3A1SefA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S56S89A1S70SefVsc;A2S59S89S15Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pC am1_C). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSefS15Vs;Vm0;A2A2S59S8aS8cS16fSf2A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MC)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S69S9bSf2A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_C. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MC))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSefS11Vs;Vm0;SbA3A2S59S8aS8cSffA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSefS11Vs;Vm0;SaA3A2S59S8aS8cSf9A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dSefS11Vs;Vm0;S7A3A2S59S8aS8cSfaA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_B | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sd6Vs;Sf0S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sd6Sf0Sf8S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sd6Sf8Sf1S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
Sd6Vs;Sf1S5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3M0G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|4|
S55S6S1cS55S6S1dS55S6S12S77ScSbA1A1M0A1S55S6S9SbS77ScS8A1A1M1S77ScSaA1A1M2S77S17SbA1A1S77S21SbA1A1S77S20SbA1A1S77S16SbA1A1A7S55S6S9SaG0S77ScS7A1A1M3S77S17SaA1A1S77S21SaA1A1S77S20SaA1A1S77S16SaA1A1A7S55S6S9S7G2G1S77S17S7A1A1S77S21S7A1A1S77S20S7A1A1S77S16S7A1A1A7S55S6S10S7S77S25S7A1A1A2S55S6S9S8G3G0S77S17S8A1A1S77S21S8A1A1S77S20S8A1A1S77S16S8A1A1A7S55S6S10S8S77S25S8A1A1A2S55S6S1eS55S6S1bS55S6S13S8S77PaaA1A2S5cS6A1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S5bS32A1S3bSc8A1S55S32S22SbbS6S32S1fSf3A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R4sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

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
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36Sc8A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R4sr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MC)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MC))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MC)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cSaaSa7S42S5fS31A1S55S32S22S5cS32A1A3S36Sc8A1Sc3S62A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S3eSa6VrhoW;S101S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4M0A4S3eSa6VrhoW;Sc8G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R4sr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S56S5dS5bS5dS31S31A2M0A1M1S5bS34A1M2A2M3A1S157Sd1SbfA2S59G3S5eG1G2S55G0S5eS31S31Se3S8A1S30PabA1A4S5cG0A1A3S61G1G2ScdA3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R4sr)). Qed.
Lemma swf_ST : swf ST_R4sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S57Sa2S34S34Sa4S34S46R1A1S36SbfA1A3Lp;S61S5bS5dS31S31A2A1S5bS34A1ScdA3A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S57Sa2S34S13bSd9A1S36SbfA1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S57Sa2S34SecS36SbfA1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36SbfA1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R4sr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R4sr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S6aS44SbfA1Sc3A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R4sr 0 ST_R4sr.
Definition LT1 : sstate := lfs LT_R4sr 1 ST_R4sr.
Definition LT2 : sstate := lfs LT_R4sr 2 ST_R4sr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bSfeA1A2Sf5A2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bSfcA1A2Sf6A2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bSfdA1A2Sf7A2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fSf5A4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fSf6A4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fSf7A4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fSf5A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fSf6A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fSf7A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeSf3Sf5A2Sf4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeSf3Sf6A2S100A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeSf3Sf7A2SfbA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S0S5bS6A1Sf4S55S6S12S77ScS8A1A1A1S55S6S9S8S77ScS7A1A1S77ScSbA1A1S77S17S8A1A1Se0Se2S8A1S77S16S8A1A1A7S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S5bS6A1SfbS5aS6Sf4S55S6S13S8Se1A2S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S66S65S6VdsF;A2S65S6Sf3A2A3S6Sa1S6R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10Sa1S6R2SdeSf3VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S5bS6A1M0G0S6Sa1S6R1SdeR3R2A2A3Sa1S6R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sd5Vk;U3A2S0S5bS32A1S3bSbeSc4Vk;SbfA3A1M0S55S32S143S4bSa5S32S22G0A3A1A1Sa3S32G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S69S45SbeSc4Vk;SbfA3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S5bS31A1S40SbeSc4Vk;SbfA3A1Sa7A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S43S3fSbeSc4Vk;SbfA3A1S42A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S56S31A1S41SbeSc4Vk;SbfA3A1S5fS31A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S31S3aSbeSc4Vk;SbfA3ZaA2S29S77PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S69S1S78Z1R1A2S78R1Z1fA2A2S0S57Sa8S80R2A1A1S58A3S0S31S3aSbeSc4Vk;SbfA3R3A2Sa9S80R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R4sr k ST_R4sr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
Sa1S34S39Sb2S33Z1fA1S23S8A1A3S36SfeA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
Sa1S34S39Sb3S77PaaA1S33Z0A1A3S36SfcA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S8A1A3A1S36SfcA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb3S77PaaA1S33Z0A1A3A1S36SfdA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S8A1A3A1S36SfdA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S0S8bS171Sf1S15Vs;Vm0;A2M1Sf2A3S170Sf1G1Sf2A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pC am1_C (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2Sd6Vs;SefS5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G2A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pC am1_C ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1Sd6Vs;SefS5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G2A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M3S55S6cS6eS79S71S7cVsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pC am1_C ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S0S5bS69A1S8dSefA1S9fS7cVsc;G0A2S7cVbnc;Z1A2S8dVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pC am1_C (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefS9S8S77ScS7A1A1S77ScSbA1A1S77S17S8A1A1Se0Se2S8A1S77S16S8A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_C). split; [exact MT_R'|].
  pose proof (am_final_fields am1_C) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MB); unfold am1_C, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_C, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_C; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_C; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_C, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefS12S77ScS8A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MC). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefS13S8Se1A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1Sf4A3S1Sa1S6R2Sf5A3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefR2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S100A3S1Sa1S6R2Sf6A3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefR2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S6Sa1S6R1SfbA3S1Sa1S6R2Sf7A3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SefR2A11S13eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G1A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M2G0A3G2A3A3A3S4S6S6S1Sa1S6R1Sf4A3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v (vptr MM0)) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G1A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M2S55S6cS6eS79S71S7cVsc;Z7A2A2A1G0A3A3G2A3A3A3S4S6S6S1Sa1S6R1SfbA3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v (vptr MM0)) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MC e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R4sr : ltac2:(tb__ "0|0|
VTR;Z0Se8Sa6VK;Sc8VrhoW;A4S142VX;VU;S151Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R4sr)).
  { apply (seg_run 300 SA_R4sr LA_R4sr _ rhoW eq_refl eq_refl runA_R4sr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R4sr _ SA_R4sr LfA LA_R4sr_shape HinA) in HSPA. change (lfs LA_R4sr 0 SA_R4sr) with LA_R4srs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R4srs ST_R4sr (e_maskA MC) (snd DT_R4sr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R4sr LT_R4sr _ rhoA ST_len ST_next runT_R4sr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MC)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R4sr _ _ _ ST_R4sr Lf LT_R4sr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MC rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sr 0 ST_R4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sr 0 ST_R4sr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sr 1 ST_R4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sr 1 ST_R4sr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R4sr 2 ST_R4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R4sr 2 ST_R4sr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR4sr.
End Mal_aslot_VR4sr.

Module Mal_aslot_VR5nr.

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

Section VR5nr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S73VX;S5fS5dS89S69A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S78Z0Vreq;A2S78S79Vreq;S98A2S91Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S56S89A1S70Vs;Vsc;A2S59S89Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S75S74VX;Vs;Vsc;A3S59S89Vm0;A2S55S89Vm0;Vrest;A3A3").
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
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§20§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§20§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S15cS14cVX;S5fS5dS89S69A2A1VU;S151Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S78Z0M0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S7aG1Z100A2A2S1S0S69S7dG1Z20A2S8eSdVs;Vm0;R1A3M2A1A3S2S0S69S99G2A1G0A3A1S0S69S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S8eSdVs;Vm0;R2A3A1A3F_;A2A2Fx;").
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
S1S78Z1000SacQ40S38Vrho;PaA2A2M0A2S0S69S7dG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S78SeaZ40SacQ40S38Vrho;PfA2A2A2M0S7fS159Z0A1A1A2S78S7fS7eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S78S150VL;A1S79SacQ40M0S38Vrho;PaA2A2SeaZ40SacG0S38Vrho;PfA2A2A2A2A2").
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
S0SabQ40A1S56SabQ8A1A1F_;Vrd0;SdcSa6VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SabQ40A1S57F_;Vwok0;SddSa6VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z60A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ecR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z20A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ccR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S28VL;S9aSdVs;Vm0;R1A3A1A2Z8A2A2A3S59G1SadG0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S79Z5a3d0Z369A2Vsc;A2A2A3S59G1SadG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14eS14dVrd0;SabQ40A1S58L_;A2S14fS14cA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14dSdcSa6VmW;A2SddSa6VmW;A2A2").
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
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S0S69Vbnc;S97S7cVsc;G0A2S8dVs;A1A2A3F_;").
Local Notation "§27§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§27§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15dSa6VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S5bSe4A1Se5OF_;F_;").
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
S0SabQ40A1S56SabQ8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Se6Vvm;Se7Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S5bSe4A1M0Se5VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Se5R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S3eSa6Vrho;S15bS15aA1S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S69S9dSdVs;Vm0;SbA3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S69S93SdVs;Vm0;SbA3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S69S93SdVs;Vm0;SaA3M0A1S95S94G0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S69Vmaskv;SdfVs;Vm0;S7A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dVs;S27Vm0;A1A2S59S8aS8cVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS117S11Vs;Vm0;SbA3A2S59S8aS8cS124A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS117S11Vs;Vm0;SaA3A2S59S8aS8cS119A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS117S11Vs;Vm0;S7A3A2S59S8aS8cS118A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS116Vq;A2S6dS117Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S5bS69A1S8dS116A1S8dVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S56S89A1S70S116Vsc;A2S59S89SeVs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S90S8bS5dS56S89A1M0S8bA2M1A2S173Vsc;S27Vm0;A1Vam0;Vs;A4S8fS8bG1S5eG0S8bS59S89SfVs;Vm0;A2A2S117A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S89SfVs;Vm0;A2S11Vs;Vm0;SaA3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS117SfVs;Vm0;A2A2S59S8aS8cS119A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S90S8bS5dS89S8bA2M0A2S174Vsc;SfVs;Vm0;A2M1S119S117A4S8fS8bG0S5eS89S8bG1S11fA4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS11fSfVs;Vm0;A2A2S59S8aS8cS119A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S175Vsc;SfVs;Vm0;A2S119S11fA4S8fS8bG0S5eS89S8bSeVs;Vm0;A2S116A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS116SeVs;Vm0;A2A2S59S8aS8cS118A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S69S176S118A1SdfVs;Vm0;S7A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S172S116SeVs;Vm0;A2S118A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S90S8bS5dS69S8bA2M0A2S9eVsc;Vs;A2S8fS8bG0S5eS69S8bS92SdfVs;Vm0;S7A3A1S115A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S69S92SdfVs;Vm0;S7A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S16eVX;VU;Vs;Vsc;S92SdfVs;Vm0;S7A3A1S115A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S56S89A1S70S115Vsc;A2S59S89SeVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS115SeVs;Vm0;A2A2S59S8aS8cS16fS118A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S69S9bS118A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS115S11Vs;Vm0;SbA3A2S59S8aS8cS124A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS115S11Vs;Vm0;SaA3A2S59S8aS8cS119A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sd6Vs;S117S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sd6S117S11fS5cS6cA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sd6S11fS116S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
Sd6Vs;S116S5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G0A3G1A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S55S6S1cS55S6S1dS55S6S12S77ScSbA1A1M0A1S55S6S9SbS77ScS2bA1A1S77ScSaA1A1M1S77S17SbA1A1S77S21SbA1A1S77S20SbA1A1S77S16SbA1A1A7S55S6S9SaG0S77ScS7A1A1S77S17SaA1A1S77S21SaA1A1S77S20SaA1A1S77S16SaA1A1A7S55S6S10SaS77S25SaA1A1A2S55S6S9S7G1S77ScS8A1A1S77S17S7A1A1S77S21S7A1A1S77S20S7A1A1S77S16S7A1A1A7S55S6S10S7S77S25S7A1A1A2S55S6S1eS55S6S1bS55S6S13S7S77PaaA1A2S5cS6A1A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S5bS32A1S3bSc9A1S55S32S22SbbS6S32S1fS11aA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R5nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
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
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36Sc9A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R5nr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cSaaSa7S42S5fS31A1S55S32S22S5cS32A1A3S36Sc9A1Sc3S62A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S3eSa6VrhoW;S126S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4M0A4S3eSa6VrhoW;Sc9G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R5nr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S56S5dS5bS5dS31S31A2M0A1M1S5bS34A1M2A2M3A1S157Sd2Sc0A2S59G3S5eG1G2S55G0S5eS31S31Se3S7A1S30PabA1A4S5cG0A1A3S61G1G2SceA3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R5nr)). Qed.
Lemma swf_ST : swf ST_R5nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S57Sa2S34S34Sa4S34S46R1A1S36Sc0A1A3Lp;S61S5bS5dS31S31A2A1S5bS34A1SceA3A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S57Sa2S34S13bSd9A1S36Sc0A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S57Sa2S34SecS36Sc0A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36Sc0A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R5nr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R5nr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S6aS44Sc0A1Sc3A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R5nr 0 ST_R5nr.
Definition LT1 : sstate := lfs LT_R5nr 1 ST_R5nr.
Definition LT2 : sstate := lfs LT_R5nr 2 ST_R5nr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS123A1A2S11cA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS121A1A2S11dA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS122A1A2S11eA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS11cA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS11dA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS11eA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS11cA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS11dA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS11eA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS11aS11cA2S11bA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS11aS11dA2S125A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS11aS11eA2S120A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S11bS55S6S12S77ScS7A1A1A1S55S6S9S7S77ScSaA1A1S77ScS8A1A1S77S17S7A1A1Se0Se2S7A1S77S16S7A1A1A7S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S120S5aS6S11bS55S6S13S7Se1A2S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S66S65S6VdsF;A2S65S6S11aA2A3S6Sa1S6R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10Sa1S6R2SdeS11aVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S5bS6A1M0G0S6Sa1S6R1SdeR3R2A2A3Sa1S6R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sd5Vk;U3A2S0S5bS32A1S3bSbeSc5Vk;Sc0A3A1M0S55S32S143S4bSa5S32S22G0A3A1A1Sa3S32G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S69S45SbeSc5Vk;Sc0A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S5bS31A1S40SbeSc5Vk;Sc0A3A1Sa7A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S43S3fSbeSc5Vk;Sc0A3A1S42A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S56S31A1S41SbeSc5Vk;Sc0A3A1S5fS31A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S31S3aSbeSc5Vk;Sc0A3ZaA2S29S77PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S69S1S78Z1R1A2S78R1Z1fA2A2S0S57Sa8S80R2A1A1S58A3S0S31S3aSbeSc5Vk;Sc0A3R3A2Sa9S80R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R5nr k ST_R5nr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
Sa1S34S39Sb2S33Z1fA1S23S7A1A3S36S123A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
Sa1S34S39Sb3S77PaaA1S33Z0A1A3S36S121A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S7A1A3A1S36S121A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb3S77PaaA1S33Z0A1A3A1S36S122A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S7A1A3A1S36S122A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S0S8bS171S116SeVs;Vm0;A2M1S118A3S170S116G1S118A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2Sd6Vs;S115S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G1A3G2A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1Sd6Vs;S115S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G1A3G2A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M3S55S6cS6eS79S71S7cVsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S0S5bS69A1S8dS115A1S9fS7cVsc;G0A2S7cVbnc;Z1A2S8dVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115S9S7S77ScSaA1A1S77ScS8A1A1S77S17S7A1A1Se0Se2S7A1S77S16S7A1A1A7A11").
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
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115S12S77ScS7A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115S13S7Se1A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S11bA3S1Sa1S6R2S11cA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S125A3S1Sa1S6R2S11dA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S6Sa1S6R1S120A3S1Sa1S6R2S11eA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S115R2A11S13eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G0A3G1A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M2G0A3G2A3A3A3S4S6S6S1Sa1S6R1S11bA3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G0A3G1A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M2S55S6cS6eS79S71S7cVsc;Z7A2A2A1G0A3A3G2A3A3A3S4S6S6S1Sa1S6R1S120A3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R5nr : ltac2:(tb__ "0|0|
VTR;Z0Se8Sa6VK;Sc9VrhoW;A4S142VX;VU;S151Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R5nr)).
  { apply (seg_run 300 SA_R5nr LA_R5nr _ rhoW eq_refl eq_refl runA_R5nr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R5nr _ SA_R5nr LfA LA_R5nr_shape HinA) in HSPA. change (lfs LA_R5nr 0 SA_R5nr) with LA_R5nrs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R5nrs ST_R5nr (e_maskA MB) (snd DT_R5nr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R5nr LT_R5nr _ rhoA ST_len ST_next runT_R5nr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R5nr _ _ _ ST_R5nr Lf LT_R5nr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nr 0 ST_R5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nr 0 ST_R5nr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nr 1 ST_R5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nr 1 ST_R5nr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5nr 2 ST_R5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5nr 2 ST_R5nr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR5nr.
End Mal_aslot_VR5nr.

Module Mal_aslot_VR5sh.

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

Section VR5sh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S73VX;S5fS5dS89S69A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S78Z0Vreq;A2S78S79Vreq;S98A2S91Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S56S89A1S70Vs;Vsc;A2S59S89Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S75S74VX;Vs;Vsc;A3S59S89Vm0;A2S55S89Vm0;Vrest;A3A3").
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
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§38§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§38§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S15cS14cVX;S5fS5dS89S69A2A1VU;S151Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S78Z0M0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S7aG1Z100A2A2S1S0S69S7dG1Z20A2S8eSdVs;Vm0;R1A3M2A1A3S2S0S69S99G2A1G0A3A1S0S69S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S8eSdVs;Vm0;R2A3A1A3F_;A2A2Fx;").
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
S1S78Z1000SacQ40S38Vrho;PaA2A2M0A2S0S69S7dG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S78SeaZ40SacQ40S38Vrho;PfA2A2A2M0S7fS159Z0A1A1A2S78S7fS7eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S78S150VL;A1S79SacQ40M0S38Vrho;PaA2A2SeaZ40SacG0S38Vrho;PfA2A2A2A2A2").
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
S0SabQ40A1S56SabQ8A1A1F_;Vrd0;SdcSa6VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SabQ40A1S57F_;Vwok0;SddSa6VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z60A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ecR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z20A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ccR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S28VL;S9aSdVs;Vm0;R1A3A1A2Z8A2A2A3S59G1SadG0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S79Z5a3d0Z369A2Vsc;A2A2A3S59G1SadG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14eS14dVrd0;SabQ40A1S58L_;A2S14fS14cA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14dSdcSa6VmW;A2SddSa6VmW;A2A2").
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
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S0S69Vbnc;S97S7cVsc;G0A2S8dVs;A1A2A3F_;").
Local Notation "§46§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§46§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15dSa6VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S5bSe4A1Se5OF_;F_;").
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
S0SabQ40A1S56SabQ8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Se6Vvm;Se7Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S5bSe4A1M0Se5VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Se5R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S3eSa6Vrho;S15bS15aA1S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S69S9dSdVs;Vm0;SbA3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S69S93SdVs;Vm0;SbA3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S0S69S93SdVs;Vm0;SaA3M0A1S95S94G0A1A1A3").
Hypothesis HVact : maskA MB <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S69Vmaskv;SdfVs;Vm0;S7A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dVs;S27Vm0;A1A2S59S8aS8cVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS12aS11Vs;Vm0;SbA3A2S59S8aS8cS136A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS12aS11Vs;Vm0;SaA3A2S59S8aS8cS131A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS12aS11Vs;Vm0;S7A3A2S59S8aS8cS128A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS129Vq;A2S6dS12aVq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S5bS69A1S8dS129A1S8dVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S56S89A1S70S129Vsc;A2S59S89SeVs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S90S8bS5dS56S89A1M0S8bA2M1A2S173Vsc;S27Vm0;A1Vam0;Vs;A4S8fS8bG1S5eG0S8bS59S89SfVs;Vm0;A2A2S12aA4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S89SfVs;Vm0;A2S11Vs;Vm0;SaA3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS12aSfVs;Vm0;A2A2S59S8aS8cS131A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S174Vsc;SfVs;Vm0;A2S131S12aA4S8fS8bG0S5eS89S8bSeVs;Vm0;A2S130A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS130SeVs;Vm0;A2A2S59S8aS8cS128A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S90S8bS5dS89S8bA2M0A2S175Vsc;SeVs;Vm0;A2M1S128S130A4S8fS8bG0S5eS89S8bG1S129A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_B. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS129SeVs;Vm0;A2A2S59S8aS8cS128A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S69S176S128A1SdfVs;Vm0;S7A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S172S129SeVs;Vm0;A2S128A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S90S8bS5dS69S8bA2M0A2S9eVsc;Vs;A2S8fS8bG0S5eS69S8bS92SdfVs;Vm0;S7A3A1S127A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S69S92SdfVs;Vm0;S7A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S16eVX;VU;Vs;Vsc;S92SdfVs;Vm0;S7A3A1S127A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S56S89A1S70S127Vsc;A2S59S89SeVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS127SeVs;Vm0;A2A2S59S8aS8cS16fS128A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S69S9bS128A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS127S11Vs;Vm0;SbA3A2S59S8aS8cS136A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS127S11Vs;Vm0;SaA3A2S59S8aS8cS131A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sd6Vs;S12aS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sd6S12aS130S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sd6S130S129S5cS6cA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
Sd6Vs;S129S5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S55S6S1cS55S6S1dS55S6S12S77ScSbA1A1M0A1S55S6S9SbS77ScS2bA1A1S77ScSaA1A1M1S77S17SbA1A1S77S21SbA1A1S77S20SbA1A1S77S16SbA1A1A7S55S6S9SaG0S77ScS7A1A1S77S17SaA1A1S77S21SaA1A1S77S20SaA1A1S77S16SaA1A1A7S55S6S9S7G1S77ScS8A1A1S77S17S7A1A1S77S21S7A1A1S77S20S7A1A1S77S16S7A1A1A7S55S6S10S7S77S25S7A1A1A2S55S6S1eS55S6S1bS55S6S13S7S77PaaA1A2S5cS6A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S5bS32A1S3bScaA1S55S32S22SbbS6S32S1fS12bA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R5sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
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
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36ScaA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R5sh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cSaaSa7S42S5fS31A1S55S32S22S5cS32A1A3S36ScaA1Sc3S62A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S3eSa6VrhoW;S138S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4M0A4S3eSa6VrhoW;ScaG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R5sh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S56S5dS5bS5dS31S31A2M0A1M1S5bS34A1M2A2M3A1S157Sd3Sc1A2S59G3S5eG1G2S55G0S5eS31S31Se3S7A1S30PabA1A4S5cG0A1A3S61G1G2ScfA3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R5sh)). Qed.
Lemma swf_ST : swf ST_R5sh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S57Sa2S34S34Sa4S34S46R1A1S36Sc1A1A3Lp;S61S5bS5dS31S31A2A1S5bS34A1ScfA3A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S57Sa2S34S13bSd9A1S36Sc1A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S57Sa2S34SecS36Sc1A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36Sc1A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R5sh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R5sh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S6aS44Sc1A1Sc3A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R5sh 0 ST_R5sh.
Definition LT1 : sstate := lfs LT_R5sh 1 ST_R5sh.
Definition LT2 : sstate := lfs LT_R5sh 2 ST_R5sh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS135A1A2S12dA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS133A1A2S12eA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS134A1A2S12fA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS12dA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS12eA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS12fA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS12dA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS12eA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS12fA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS12bS12dA2S12cA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS12bS12eA2S137A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS12bS12fA2S132A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S12cS55S6S12S77ScS7A1A1A1S55S6S9S7S77ScSaA1A1S77ScS8A1A1S77S17S7A1A1Se0Se2S7A1S77S16S7A1A1A7S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S132S5aS6S12cS55S6S13S7Se1A2S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S66S65S6VdsF;A2S65S6S12bA2A3S6Sa1S6R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10Sa1S6R2SdeS12bVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S5bS6A1M0G0S6Sa1S6R1SdeR3R2A2A3Sa1S6R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sd5Vk;U3A2S0S5bS32A1S3bSbeSc6Vk;Sc1A3A1M0S55S32S143S4bSa5S32S22G0A3A1A1Sa3S32G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S69S45SbeSc6Vk;Sc1A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S5bS31A1S40SbeSc6Vk;Sc1A3A1Sa7A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S43S3fSbeSc6Vk;Sc1A3A1S42A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S56S31A1S41SbeSc6Vk;Sc1A3A1S5fS31A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S31S3aSbeSc6Vk;Sc1A3ZaA2S29S77PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S69S1S78Z1R1A2S78R1Z1fA2A2S0S57Sa8S80R2A1A1S58A3S0S31S3aSbeSc6Vk;Sc1A3R3A2Sa9S80R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R5sh k ST_R5sh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
Sa1S34S39Sb2S33Z1fA1S23S7A1A3S36S135A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
Sa1S34S39Sb3S77PaaA1S33Z0A1A3S36S133A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S7A1A3A1S36S133A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb3S77PaaA1S33Z0A1A3A1S36S134A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S7A1A3A1S36S134A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S0S8bS171S129SeVs;Vm0;A2M1S128A3S170S129G1S128A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2Sd6Vs;S127S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G1A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1Sd6Vs;S127S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G1A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M3S55S6cS6eS79S71S7cVsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S0S5bS69A1S8dS127A1S9fS7cVsc;G0A2S7cVbnc;Z1A2S8dVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127S9S7S77ScSaA1A1S77ScS8A1A1S77S17S7A1A1Se0Se2S7A1S77S16S7A1A1A7A11").
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
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127S12S77ScS7A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127S13S7Se1A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S12cA3S1Sa1S6R2S12dA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S137A3S1Sa1S6R2S12eA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S6Sa1S6R1S132A3S1Sa1S6R2S12fA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S127R2A11S13eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G0A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M2G0A3G2A3A3A3S4S6S6S1Sa1S6R1S12cA3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G0A3S5aS6cS5aS6cSd8SeVs;Vm0;A2A1M2S55S6cS6eS79S71S7cVsc;Z7A2A2A1G0A3A3G2A3A3A3S4S6S6S1Sa1S6R1S132A3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R5sh : ltac2:(tb__ "0|0|
VTR;Z0Se8Sa6VK;ScaVrhoW;A4S142VX;VU;S151Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R5sh)).
  { apply (seg_run 300 SA_R5sh LA_R5sh _ rhoW eq_refl eq_refl runA_R5sh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R5sh _ SA_R5sh LfA LA_R5sh_shape HinA) in HSPA. change (lfs LA_R5sh 0 SA_R5sh) with LA_R5shs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R5shs ST_R5sh (e_maskA MB) (snd DT_R5sh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R5sh LT_R5sh _ rhoA ST_len ST_next runT_R5sh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R5sh _ _ _ ST_R5sh Lf LT_R5sh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sh 0 ST_R5sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sh 0 ST_R5sh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sh 1 ST_R5sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sh 1 ST_R5sh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sh 2 ST_R5sh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sh 2 ST_R5sh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR5sh.
End Mal_aslot_VR5sh.

Module Mal_aslot_VR5sr.

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

Section VR5sr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S73VX;S5fS5dS89S69A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S78Z0Vreq;A2S78S79Vreq;S98A2S91Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S56S89A1S70Vs;Vsc;A2S59S89Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S75S74VX;Vs;Vsc;A3S59S89Vm0;A2S55S89Vm0;Vrest;A3A3").
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
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§59§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§59§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S15cS14cVX;S5fS5dS89S69A2A1VU;S151Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S78Z0M0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S7aG1Z100A2A2S1S0S69S7dG1Z20A2S8eSdVs;Vm0;R1A3M2A1A3S2S0S69S99G2A1G0A3A1S0S69S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S8eSdVs;Vm0;R2A3A1A3F_;A2A2Fx;").
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
Local Notation "§62§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze152 := (§62§ U.Mal_aslot__G1.Mal_aslot_I.ze152).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S78Z1000SacQ40S38Vrho;PaA2A2M0A2S0S69S7dG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S78SeaZ40SacQ40S38Vrho;PfA2A2A2M0S7fS159Z0A1A1A2S78S7fS7eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S78S150VL;A1S79SacQ40M0S38Vrho;PaA2A2SeaZ40SacG0S38Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§63§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§63§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§64§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§64§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§61§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§64§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§64§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§64§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§64§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SabQ40A1S56SabQ8A1A1F_;Vrd0;SdcSa6VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SabQ40A1S57F_;Vwok0;SddSa6VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z60A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ecR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z20A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ccR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S28VL;S9aSdVs;Vm0;R1A3A1A2Z8A2A2A3S59G1SadG0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S79Z5a3d0Z369A2Vsc;A2A2A3S59G1SadG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14eS14dVrd0;SabQ40A1S58L_;A2S14fS14cA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14dSdcSa6VmW;A2SddSa6VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§65§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§65§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§66§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§66§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§67§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§67§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§61§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S0S69Vbnc;S97S7cVsc;G0A2S8dVs;A1A2A3F_;").
Local Notation "§68§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§68§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15dSa6VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S5bSe4A1Se5OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§69§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§69§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§70§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§70§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§71§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§71§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§72§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§72§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§58§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§73§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§73§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§64§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§64§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§74§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§74§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§75§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§75§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§76§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§76§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§77§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§77§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§78§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§78§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§78§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§74§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§70§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§79§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§79§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§79§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§79§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
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
S0SabQ40A1S56SabQ8A1A1F_;VmW;S4cVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Se6Vvm;Se7Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S5bSe4A1M0Se5VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Se5R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S3eSa6Vrho;S15bS15aA1S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S69SacQ40S38Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S69S9dSdVs;Vm0;SbA3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S69S93SdVs;Vm0;SbA3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S0S69S93SdVs;Vm0;SaA3M0A1S95S94G0A1A1A3").
Hypothesis HVact : maskA MB = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S69Vmaskv;SdfVs;Vm0;S8A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dVs;S27Vm0;A1A2S59S8aS8cVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition am1_A : ameta := (mam MA_).
Definition am1_B : ameta := (mam MB).
Definition am1_C : ameta := (mam MC).
Definition s1V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
Sd7Vsc;S59S89S15Vs;Vm0;A2A2Sd7Vsc;S59S89SeVs;Vm0;A2A2Sd7Vsc;S59S89SfVs;Vm0;A2A2Vs;A3A3A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS103S11Vs;Vm0;SbA3A2S59S8aS8cS112A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS103S11Vs;Vm0;SaA3A2S59S8aS8cS10cA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_A. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS103S11Vs;Vm0;S7A3A2S59S8aS8cS10dA1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_B. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT1_C : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS103S11Vs;Vm0;S8A3A2S59S8aS8cS105A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_C. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MC)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS104Vq;A2S6dS103Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S5bS69A1S8dS104A1S8dVs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S56S89A1S70S104Vsc;A2S59S89S15Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S90S8bS5dS56S89A1M0S8bA2M1A2S173Vsc;S27Vm0;A1Vam0;Vs;A4S8fS8bG1S5eG0S8bS59S89SfVs;Vm0;A2A2S103A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S89SfVs;Vm0;A2S11Vs;Vm0;SaA3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS103SfVs;Vm0;A2A2S59S8aS8cS10cA1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S174Vsc;SfVs;Vm0;A2S10cS103A4S8fS8bG0S5eS89S8bSeVs;Vm0;A2S10bA4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS10bSeVs;Vm0;A2A2S59S8aS8cS10dA1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S90S8bS5dS89S8bA2M0A2S175Vsc;SeVs;Vm0;A2S10dS10bA4S8fS8bG0S5eS89S8bS15Vs;Vm0;A2S104A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pB am1_B pC); [unfold am1_B; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_B; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MB); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS104S15Vs;Vm0;A2A2S59S8aS8cS105A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_C. Qed.
Lemma Hav3 : am_avail am1_C = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_C. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S69S176S105A1SdfVs;Vm0;S8A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MC <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S172S104S15Vs;Vm0;A2S105A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S90S8bS5dS69S8bA2M0A2S9eVsc;Vs;A2S8fS8bG0S5eS69S8bS92SdfVs;Vm0;S8A3A1S102A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S69S92SdfVs;Vm0;S8A3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MC). pose proof (lowbit_range (maskA MC) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S16eVX;VU;Vs;Vsc;S92SdfVs;Vm0;S8A3A1S102A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S56S89A1S70S102Vsc;A2S59S89S15Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pC am1_C). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS102S15Vs;Vm0;A2A2S59S8aS8cS16fS105A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MC)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S69S9bS105A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_C. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MC))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS102S11Vs;Vm0;SbA3A2S59S8aS8cS112A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS102S11Vs;Vm0;SaA3A2S59S8aS8cS10cA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_B : ltac2:(tb__ "0|0|
S0S56S8aA1S6dS102S11Vs;Vm0;S7A3A2S59S8aS8cS10dA1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_B | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
Sd6Vs;S103S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s1V. apply delta_sh. lia. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
Sd6S103S10bS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
Sd6S10bS104S55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
Sd6Vs;S104S5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1A3M0G0A3G0A3A3").
Proof using Hbnc Hgd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|3|
S55S6S1cS55S6S1dS55S6S12S77ScSbA1A1M0A1S55S6S9SbS77ScS2bA1A1S77ScSaA1A1M1S77S17SbA1A1S77S21SbA1A1S77S20SbA1A1S77S16SbA1A1A7S55S6S9SaG0S77ScS7A1A1M2S77S17SaA1A1S77S21SaA1A1S77S20SaA1A1S77S16SaA1A1A7S55S6S9S7G1S77ScS8A1A1S77S17S7A1A1S77S21S7A1A1S77S20S7A1A1S77S16S7A1A1A7S55S6S10S7S77S25S7A1A1A2S55S6S9S8G2S77P98A1S77S17S8A1A1S77S21S8A1A1S77S20S8A1A1S77S16S8A1A1A7S55S6S10S8S77S25S8A1A1A2S55S6S1eS55S6S1bS55S6S13S8S77PaaA1A2S5cS6A1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S5bS32A1S3bScbA1S55S32S22SbbS6S32S1fS106A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R5sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | exact ze152].
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
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36ScbA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_R5sr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MC)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MC))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MC)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S4aZ2126cSaaSa7S42S5fS31A1S55S32S22S5cS32A1A3S36ScbA1Sc3S62A9").

Lemma carve_R : ltac2:(tb__ "0|1|
S3eSa6VrhoW;S114S5eS5bSe4A1S152Vtr;S153Vms;Vmd;A2A4M0A4S3eSa6VrhoW;ScbG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R5sr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S56S5dS5bS5dS31S31A2M0A1M1S5bS34A1M2A2M3A1S157Sd4Sc2A2S59G3S5eG1G2S55G0S5eS31S31Se3S8A1S30PabA1A4S5cG0A1A3S61G1G2Sd0A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R5sr)). Qed.
Lemma swf_ST : swf ST_R5sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S57Sa2S34S34Sa4S34S46R1A1S36Sc2A1A3Lp;S61S5bS5dS31S31A2A1S5bS34A1Sd0A3A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S57Sa2S34S13bSd9A1S36Sc2A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S57Sa2S34SecS36Sc2A1A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
SbcS34SebS19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S36Sc2A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_R5sr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R5sr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S6aS44Sc2A1Sc3A3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R5sr 0 ST_R5sr.
Definition LT1 : sstate := lfs LT_R5sr 1 ST_R5sr.
Definition LT2 : sstate := lfs LT_R5sr 2 ST_R5sr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS111A1A2S108A2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS10fA1A2S109A2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S57S13dSa3S32S3bS110A1A2S10aA2S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS108A4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS109A4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S57Sa2S32S139Sd9A1SbbS6S32S1fS10aA4A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS108A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS109A3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S57Sa2S6S13fS10aA3S58A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS106S108A2S107A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS106S109A2S113A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S5bS6A1SdeS106S10aA2S10eA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S107S55S6S12S77ScS8A1A1A1S55S6S9S8S77ScS7A1A1S77P98A1S77S17S8A1A1Se0Se2S8A1S77S16S8A1A1A7S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S5bS6A1S10eS5aS6S107S55S6S13S8Se1A2S5cS6A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S66S65S6VdsF;A2S65S6S106A2A3S6Sa1S6R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10Sa1S6R2SdeS106VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S5bS6A1M0G0S6Sa1S6R1SdeR3R2A2A3Sa1S6R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sd5Vk;U3A2S0S5bS32A1S3bSbeSc7Vk;Sc2A3A1M0S55S32S143S4bSa5S32S22G0A3A1A1Sa3S32G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S69S45SbeSc7Vk;Sc2A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S5bS31A1S40SbeSc7Vk;Sc2A3A1Sa7A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S43S3fSbeSc7Vk;Sc2A3A1S42A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S56S31A1S41SbeSc7Vk;Sc2A3A1S5fS31A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S0S31S3aSbeSc7Vk;Sc2A3ZaA2S29S77PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sd5Vk;U3A2S69S1S78Z1R1A2S78R1Z1fA2A2S0S57Sa8S80R2A1A1S58A3S0S31S3aSbeSc7Vk;Sc2A3R3A2Sa9S80R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R5sr k ST_R5sr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
Sa1S34S39Sb2S33Z1fA1S23S8A1A3S36S111A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
Sa1S34S39Sb3S77PaaA1S33Z0A1A3S36S10fA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S8A1A3A1S36S10fA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb3S77PaaA1S33Z0A1A3A1S36S110A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb2S33Z1fA1S23S8A1A3A1S36S110A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S0S8bS171S104S15Vs;Vm0;A2M1S105A3S170S104G1S105A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pC am1_C (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2Sd6Vs;S102S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G2A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pC am1_C ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1Sd6Vs;S102S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M1A3M2G2A3G2A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M3S55S6cS6eS79S71S7cVsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pC am1_C ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S0S5bS69A1S8dS102A1S9fS7cVsc;G0A2S7cVbnc;Z1A2S8dVs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pC am1_C (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102S9S8S77ScS7A1A1S77P98A1S77S17S8A1A1Se0Se2S8A1S77S16S8A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_C). split; [exact MT_R'|].
  pose proof (am_final_fields am1_C) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MB); unfold am1_C, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite ze152; unfold am1_C, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; reflexivity|].
  split; [unfold am1_C; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_C; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_C, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102S12S77ScS8A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MC). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102S13S8Se1A2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S107A3S1Sa1S6R2S108A3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S78Z7Vsc;A2S7aVsc;Z27A2A2M0A1S1G0S0S69Vbnc;Z0A3A2A2S6Sa1S6R1S113A3S1Sa1S6R2S109A3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102R2A11S13eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S78Z7Vsc;A2S7aVsc;Z27A2A2S2S0S69Vbnc;Z0A3A1S6Sa1S6R1S10eA3S1Sa1S6R2S10aA3S1S14Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S102R2A11S13eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G1A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M2G0A3G2A3A3A3S4S6S6S1Sa1S6R1S107A3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v 152) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S6cSa1S6cR1S5aS6cS5aS6cS5aS6cS55S6cS6eS79S6fS7bZ8Vsc;A2A2A1S5cS6cA1M0A3M1G1A3G1A3S5aS6cS5aS6cSd8S15Vs;Vm0;A2A1M2S55S6cS6eS79S71S7cVsc;Z7A2A2A1G0A3A3G2A3A3A3S4S6S6S1Sa1S6R1S10eA3S1S78S60S69S69S26Vs;VL;Vsc;Vm0;R1A5M3A3S72VL;R3A2M4A2S7aG4S61S69S69G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v 152) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MC e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_R5sr : ltac2:(tb__ "0|0|
VTR;Z0Se8Sa6VK;ScbVrhoW;A4S142VX;VU;S151Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R5sr)).
  { apply (seg_run 300 SA_R5sr LA_R5sr _ rhoW eq_refl eq_refl runA_R5sr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R5sr _ SA_R5sr LfA LA_R5sr_shape HinA) in HSPA. change (lfs LA_R5sr 0 SA_R5sr) with LA_R5srs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R5srs ST_R5sr (e_maskA MC) (snd DT_R5sr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R5sr LT_R5sr _ rhoA ST_len ST_next runT_R5sr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MC)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R5sr _ _ _ ST_R5sr Lf LT_R5sr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MC rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sr 0 ST_R5sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sr 0 ST_R5sr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sr 1 ST_R5sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sr 1 ST_R5sr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R5sr 2 ST_R5sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R5sr 2 ST_R5sr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR5sr.
End Mal_aslot_VR5sr.

Module Mal_aslot_L.

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

Fixpoint span_exits (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exits f (span + size) size else true
  end.

Lemma span_loop_S f cnt span size : ltac2:(tb__ "0|2|
S0S69S96S68Vf;A1Vcnt;Vspan;Vsize;A4S57S69L_;S82S83Vspan;S7cS79Vspan;Vsize;A2M0Z1M1A2A2Z1000A2S96Vf;S79Vcnt;G1A2G0Vsize;A4Vcnt;X57x2A3").
Proof. reflexivity. Qed.
Lemma span_exits_S f span size : ltac2:(tb__ "0|1|
S0S57S16bS68Vf;A1Vspan;Vsize;A3S57S57L_;S82S83Vspan;S7cS79Vspan;Vsize;A2M0Z1A2A2Z1000A2S16bVf;G0Vsize;A3S58X57x2A3").
Proof. reflexivity. Qed.

Lemma span_loop_ge : ltac2:(tb__ "0|0|
S66S69S69S69S78R3S96R4R3R2R1A4A2Fsize;Fspan;Fcnt;Ff;").
Proof.
  induction f as [|f IH]; intros cnt span size; cbn [span_loop]; [lia|].
  destruct (_ <? _); [|lia]. specialize (IH (cnt + 1) (span + size) size). lia.
Qed.

Definition span0_of (sc a : Z) : Z := ltac2:(tb__ "0|0|
S79S9cS7bS91Vsc;A1S79Va;Z2A2A2A2").

Definition span_chk : bool := ltac2:(tb__ "0|5|
Sa2S69S69Sa2S69S69S67S64S82S7cZ1000S9cA2S7bS91R2A1M0S79R1Z2A2M1A2A2A1S63S16bU12cM2S16aR2R1A2M3G0A3S87S96G2G1G3G0A4Z12cA2A2A2La;S76Z0M4Z20A2A3Lsc;S76G4Z30A2A3").

Lemma span_chk_ok : span_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma span_facts sc a : ltac2:(tb__ "0|5|
S1S78Z0M0Vsc;A2S7aVsc;Z30A2A2S1S78G0Va;A2S7aVa;Z20A2A2S7aS7cZ1000S9cA2S7bS91Vsc;A1M1S79Va;Z2A2M2A2A2S1S0S57S16bU12cM3S16aVsc;Va;A2M4G1A3S58A3S78S96G3G2G4G1A4Z12cA2A2F_;F_;F_;").
Proof.
  intros Hsc Ha Hp. pose proof span_chk_ok as C. unfold span_chk in C.
  pose proof (proj1 (forallb_forall _ _) C sc (zseq_In 0 48 sc ltac:(lia) ltac:(lia))) as C1. cbn beta in C1.
  pose proof (proj1 (forallb_forall _ _) C1 a (zseq_In 0 32 a ltac:(lia) ltac:(lia))) as C2. cbn beta in C2.
  apply Bool.orb_prop in C2 as [C2|C2].
  - apply Bool.negb_true_iff in C2. apply Z.ltb_ge in C2. lia.
  - apply andb_prop in C2 as [C2 C3]. apply Z.leb_le in C3. auto.
Qed.

Definition diff_okb (sets : list (positive * sv)) (xv : positive) (xe : sv) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|5|
Sa2S5dS31S31A2M0G0S31S57Lx;S61S31S31R1A3S69S62Lz;S6aS67Sa4S5dS6aS31A2M1G1S63S178S60S6aS31R1A3R2A2S48S61S6aS31R1A3S60S31S31R3A3A2A2Lq;Vsets;A3S63S178R1Vxv;A2S48S60S31S31R2A3Vxe;A2A2A2Lj;Sb9S31S31S62Lb;La;M2Lop;M3G3SbaG2Lop;M4G4S57S6bS31S62La;Lw;Lsgn;S6aS31S69S62Lk;Li;Ll;X31x8Lp;Vd;A3").

Definition regs_okb (f : positive -> bool) (S S' : sstate) (sets : list (positive * sv)) : bool := ltac2:(tb__ "0|1|
Sa2S69S69S3aVS';R1A2S31S3aVS;R2A2S31S67Sa4S5dS6aS31A2M0G0S63S48R3S30S60S6aS31R1A3A1A2S48S61S6aS31R1A3R2A2A2Lq;Vsets;A3S63S48R2R1A2S13aVf;R1A2A2A2Te;Te';Lr;SbbS66S69S84SbdU1U1fA2A4A3").

Lemma leaf4 (l : list leaf) a b c d0 d Lf : ltac2:(tb__ "0|2|
S0S5bS5dS69S14bA2M0A1SbbS146G0S17bVl;A4S55G0Va;S55G0Vb;S55G0Vc;S55G0Vd0;S5cG0A1A3A3A3A3A3Sa1S146VLf;Vl;A3S3S0S47S148VLf;A1M1SbeVl;U0Vd;A3A3S3S0S47G1SbeVl;U1Vd;A3A3S3S0S47G1SbeVl;U2Vd;A3A3S0S47G1SbeVl;U3Vd;A3A3A2A2A2F_;F_;").
Proof.
  intros E Hin. destruct l as [|L0 [|L1 [|L2 [|L3 [|L4 t]]]]]; cbn in E; try discriminate.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; [left | right; left | right; right; left | right; right; right]; reflexivity.
Qed.

Section L.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S73VX;S5fS5dS89S69A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S78Z0Vreq;A2S78S79Vreq;S98A2S91Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S56S89A1S70Vs;Vsc;A2S59S89Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S75S74VX;Vs;Vsc;A3S59S89Vm0;A2S55S89Vm0;Vrest;A3A3").
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (@U.Mal_aslot__G1.Mal_aslot_I.mam s m0).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S15cS14cVX;S5fS5dS89S69A2A1VU;S151Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S78Z0M0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S7aG1Z100A2A2S1S0S69S7dG1Z20A2S8eSdVs;Vm0;R1A3M2A1A3S2S0S69S99G2A1G0A3A1S0S69S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S8eSdVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§80§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§80§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Abbreviation mem_bits := (§80§ U.Mal_aslot__G1.Mal_aslot_I.mem_bits).
Local Abbreviation bits_mod32 := (§80§ U.Mal_aslot__G1.Mal_aslot_I.bits_mod32).
Local Notation "§81§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rw1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.rw1).
Local Abbreviation rho1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§81§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation zl1_1 := (@U.Mal_aslot__G1.Mal_aslot_I.zl1_1 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Abbreviation ze_lit := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation ze_alu := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_alu).
Local Abbreviation ze_aluw := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_aluw).
Local Abbreviation ze_mul := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_mul).
Local Abbreviation ze_ext := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_ext).
Local Abbreviation ze_lbytes := (§81§ U.Mal_aslot__G1.Mal_aslot_I.ze_lbytes).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§82§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bits := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze_byte := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_byte).
Local Notation "§83§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hspanv) (at level 10, h__ global).
Local Abbreviation zr1_172 := (§83§ U.Mal_aslot__G1.Mal_aslot_I.zr1_172).
Local Abbreviation ze172 := (§83§ U.Mal_aslot__G1.Mal_aslot_I.ze172).
Local Abbreviation e_sx := (@U.Mal_aslot__G1.Mal_aslot_I.e_sx).
Local Abbreviation e_onesw := (@U.Mal_aslot__G1.Mal_aslot_I.e_onesw).
Local Abbreviation e_and := (@U.Mal_aslot__G1.Mal_aslot_I.e_and).
Local Abbreviation e_tabidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_tabidx).
Local Abbreviation ze_sx_freed := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_sx_freed).
Local Abbreviation ze_tabidx := (§82§ U.Mal_aslot__G1.Mal_aslot_I.ze_tabidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S78Z1000SacQ40S38Vrho;PaA2A2M0A2S0S69S7dG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S78SeaZ40SacQ40S38Vrho;PfA2A2A2M0S7fS159Z0A1A1A2S78S7fS7eZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S78S150VL;A1S79SacQ40M0S38Vrho;PaA2A2SeaZ40SacG0S38Vrho;PfA2A2A2A2A2").
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SabQ40A1S56SabQ8A1A1F_;Vrd0;SdcSa6VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SabQ40A1S57F_;Vwok0;SddSa6VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z60A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ecR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S69S1S78Z0R1A2S7aR1Z20A2A2S0S56SabQ8A1M0A1VmW;SadQ40S79Z108ccR2A2A2A1S5fG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S28VL;S9aSdVs;Vm0;R1A3A1A2Z8A2A2A3S59G1SadG0S1aVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S56SabQ8M0A1M1A1SdcSa6VmW;SadQ40S79S79Z5a3d0Z369A2Vsc;A2A2A3S59G1SadG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S14eS14dVrd0;SabQ40A1S58L_;A2S14fS14cA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S14dSdcSa6VmW;A2SddSa6VmW;A2A2").
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S78Z7M0Vsc;A2S7aVsc;Z27A2A2S0S69Vbnc;S97S7cVsc;G0A2S8dVs;A1A2A3F_;").
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S15dSa6VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S5bSe4A1Se5OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Notation "§84§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) (at level 10, h__ global).
Local Abbreviation EVu := (§84§ U.Mal_aslot__G2.Mal_aslot_W.EVu).
Local Abbreviation HOLDS := (§84§ U.Mal_aslot__G2.Mal_aslot_W.HOLDS).
Local Abbreviation rw_agrees := (§84§ U.Mal_aslot__G2.Mal_aslot_W.rw_agrees).
Local Notation "§85§ h__" := (h__ Kc RF GF TR RR) (at level 10, h__ global).
Local Abbreviation tr_seq := (§85§ U.Mal_aslot__G2.Mal_aslot_W.tr_seq).
Local Abbreviation tr_ex := (§85§ U.Mal_aslot__G2.Mal_aslot_W.tr_ex).
Local Abbreviation tr_pure := (§85§ U.Mal_aslot__G2.Mal_aslot_W.tr_pure).
Local Abbreviation tr_disj := (§85§ U.Mal_aslot__G2.Mal_aslot_W.tr_disj).
Local Abbreviation tr_refl := (§85§ U.Mal_aslot__G2.Mal_aslot_W.tr_refl).
Local Notation "§86§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§86§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Abbreviation setp := (@U.Mal_aslot__G2.Mal_aslot_W.setp).
Local Abbreviation keys_distinct := (@U.Mal_aslot__G2.Mal_aslot_W.keys_distinct).
Local Abbreviation setp_get := (@U.Mal_aslot__G2.Mal_aslot_W.setp_get).
Local Abbreviation setp_other := (@U.Mal_aslot__G2.Mal_aslot_W.setp_other).
Local Abbreviation setp_rl := (@U.Mal_aslot__G2.Mal_aslot_W.setp_rl).
Local Abbreviation setp_rm := (@U.Mal_aslot__G2.Mal_aslot_W.setp_rm).
Local Abbreviation agrees_setp := (§84§ U.Mal_aslot__G2.Mal_aslot_W.agrees_setp).
Local Abbreviation relinkp := (@U.Mal_aslot__G2.Mal_aslot_W.relinkp K).
Local Abbreviation linkp := (§86§ U.Mal_aslot__G2.Mal_aslot_W.linkp).
Local Abbreviation scratch_of := (@U.Mal_aslot__G2.Mal_aslot_W.scratch_of).
Local Abbreviation rho' := (@U.Mal_aslot__G2.Mal_aslot_W.rho' rho).
Local Abbreviation negw_sll2_bits := (@U.Mal_aslot__G3.Mal_aslot_T.negw_sll2_bits sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation zfact_of := (§86§ U.Mal_aslot__G3.Mal_aslot_T.zfact_of).
Local Abbreviation facts_incl_sound := (@U.Mal_aslot__G3.Mal_aslot_T.facts_incl_sound).
Local Abbreviation smatch_rename := (@U.Mal_aslot__G3.Mal_aslot_T.smatch_rename sc rho bnc gd Hsc Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Definition e_size (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb1S3cS62Q10S4dP1S2cVx;A1Z2A3A3S33Z4A1A3").

Definition e_aidx (x : member) : sv := ltac2:(tb__ "0|0|
S37SafS77S25Vx;A1A1S33Z1fA1A3").

Definition e_span0 (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb0S4fSb7S15eVx;A1S37Sb0S15fVx;A1S33Z2A1A3A3S33Z10A1A3").
Definition e_a60 (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb0S4fSb7S37Sb0S37Sb1S15fVx;A1S33Z4A1A3S33Z30A1A3S3cS62Q10S4dP1S2cVx;A1Z2A3A3A3S33ZfA1A3").
Definition e_a40 (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb0S15fVx;A1S33Z1A1A3").

Definition e_byteS (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb6S37SafS37Sb0S77PacA1S33N1A1A3S33Z1fA1A3S37SafS77S25Vx;A1A1S33Ze0A1A3A3").
Definition e_byteL (x : member) : sv := ltac2:(tb__ "0|1|
S37Sb6S37SafS37SafS77S16Vx;A1A1S33Z1fA1M0A3G0A3S37SafS77S25Vx;A1A1S33Ze0A1A3A3").

Definition e_maskG (x : member) (e : sv) : sv := ltac2:(tb__ "0|0|
S2dS2fS77S20Vx;A1A1A1S2eVe;A1A2").
Definition e_freedG (x : member) (e : sv) : sv := ltac2:(tb__ "0|0|
S2dS2fS77S20Vx;A1A1A1S35SaeS33Z0A1S35Sb1S33Z2A1Ve;A3A3A2").

Lemma size_range : ltac2:(tb__ "0|2|
S1S1S78Z10M0S91Vsc;A1M1A2S78G1Z1fff0A2A2S0S69S7dG1G0A2Z0A3A2").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold class_size, UNIT. pose proof (znth_size_classes_range sc ltac:(pose proof Hsc; lia)). split; [lia|].
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma ze_u16 x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS3cS62Q10S4dP1S2cVx;A1Z2A3A3A3S97Vsc;Sa0A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  rewrite ze_ext. cbn [Z.of_N]. rewrite ze_lbytes, ze_tabidx, zl1_1. pose proof Hsc.
  rewrite table_u16 by lia. pose proof (znth_size_classes_range sc ltac:(lia)).
  rewrite !Z.mod_small; lia.
Qed.

Lemma ze_size x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15eVx;A1A3S91Vsc;A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_size. rewrite ze_alu, ze_u16, ze_lit. cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4.
  rewrite Z.shiftl_mul_pow2 by lia. pose proof Hsc. pose proof (znth_size_classes_range sc ltac:(lia)).
  unfold class_size, UNIT. change (2 ^ 4) with 16. rewrite Z.mod_small; lia.
Qed.

Lemma ze_aidx x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS15fVx;A1A3S8eSdVs;Vm0;Vx;A3A1A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  unfold e_aidx. rewrite ze_alu, ze_byte, ze_lit. cbn [zalu]. pose proof (Hbytes x) as (B1 & B2 & _).
  change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). rewrite (Z.mod_small (mbyte x)) by lia.
  rewrite Z.land_ones by lia. change (2 ^ 5) with 32. exact B2.
Qed.

Lemma aidx_range x : ltac2:(tb__ "0|1|
S1S78Z0S8eSdVs;Vm0;Vx;A3A1M0A2S7aG0Z20A2A2").
Proof using Hbnc Hbytes Hgd Hsc rho. drop_sp. pose proof (Hbytes x) as (B1 & B2 & _). rewrite <- B2. apply Z.mod_pos_bound. lia. Qed.

Lemma ze_span0 x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS163Vx;A1A3S16aVsc;S8eSdVs;Vm0;Vx;A3A1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_span0, span0_of, UNIT. rewrite ze_alu, ze_mul, ze_size, ze_alu, ze_aidx, !ze_lit. cbn [zalu].
  pose proof size_range as [SR _]. pose proof (aidx_range x) as AR.
  assert (B : 0 <= class_size sc * (am_aidx (mam x) + 2) <= 131056 * 34) by (clear - SR AR; nia).
  change (2 mod 2 ^ 64) with 2. change (16 mod 2 ^ 64) with 16. rewrite !Z.mod_small; lia.
Qed.

Lemma ze_a60 x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS162Vx;A1A3S7cS79S16aVsc;S8eSdVs;Vm0;Vx;A3A1A2S91Vsc;A1A2Z1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_a60, span0_of, UNIT. rewrite ze_alu, ze_mul, ze_alu, ze_alu, ze_aidx, ze_u16, !ze_lit. cbn [zalu].
  pose proof Hsc. pose proof (znth_size_classes_range sc ltac:(lia)). pose proof (aidx_range x).
  change ((4 mod 2 ^ 64) mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  change (48 mod 2 ^ 64) with 48. change (15 mod 2 ^ 64) with 15. unfold class_size, UNIT.
  set (u := znth sc size_classes) in *. set (a := am_aidx (mam x)) in *.
  assert (B : 0 <= (a * 16 + 48) * u <= (31 * 16 + 48) * 8191) by (clear - H0 H1; nia).
  assert (E : (a * 16 + 48) * u = 16 * u * (a + 2) + 16 * u) by ring.
  rewrite (Z.mod_small (a * 16)) by lia. rewrite (Z.mod_small (a * 16 + 48)) by lia.
  rewrite (Z.mod_small ((a * 16 + 48) * u)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ze_a40 x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS161Vx;A1A3S79S8eSdVs;Vm0;Vx;A3A1Z1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  unfold e_a40. rewrite ze_alu, ze_aidx, ze_lit. cbn [zalu]. pose proof (aidx_range x).
  change (1 mod 2 ^ 64) with 1. apply Z.mod_small. lia.
Qed.

Lemma lor_low5 a b : ltac2:(tb__ "0|4|
S1S78Z0M0Va;A2S7aVa;Z20M1A2A2S1S78G0Vb;A2S7aVb;Z100M2A2A2S1S0S69S88Va;S81Vb;Ze0A2A2M3S79Va;S7cVb;S7dVb;G1A2A2A2A3S1S78G0G3A2S7aG3G2A2A2A2F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros Ha Hb.
  pose proof (forall_range_dec (fun a => forallb (fun b => (Z.lor a (Z.land b 224) =? a + (b - b mod 32)) && (0 <=? Z.lor a (Z.land b 224)) && (Z.lor a (Z.land b 224) <? 256))%bool
                                  (map (fun k => 0 + Z.of_nat k) (seq 0 256))) 0 32 ltac:(vm_compute; reflexivity) a ltac:(lia)) as H.
  cbn beta in H. pose proof (forall_range_dec _ 0 256 H b ltac:(lia)) as H2. cbn beta in H2.
  apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3].
  apply Z.eqb_eq in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4. lia.
Qed.

Lemma ze_byteS x : ltac2:(tb__ "0|5|
S1S78Z1M0Vspanv;A2S78Vspanv;Z20M1A2A2S1S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS167Vx;A1A3M2S79S7cVspanv;G0A2M3S7cS1aVbyM0;VbyA;VbyB;VbyC;VbyP;Vx;A6M4S7dG4G1A2A2A2A3S1S1S78Z0G2A2S7aG2Z100A2A2S0S69S7dG2G1A2G3A3A2A2F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  intros Hs. unfold e_byteS. rewrite !ze_alu, ze172, ze_byte, !ze_lit. cbn [zalu].
  pose proof (Hbytes x) as (B1 & B2 & _).
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). change ((224 mod 2 ^ 64) mod 2 ^ 64) with 224.
  replace ((spanv + (2 ^ 64 - 1)) mod 2 ^ 64) with (spanv - 1)
    by (replace (spanv + (2 ^ 64 - 1)) with ((spanv - 1) + 1 * 2 ^ 64) by lia; rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  rewrite (Z.mod_small (spanv - 1)) by lia. rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (spanv - 1)) by lia. rewrite (Z.mod_small (spanv - 1)) by lia. rewrite (Z.mod_small (mbyte x)) by lia.
  destruct (lor_low5 (spanv - 1) (mbyte x) ltac:(lia) ltac:(lia)) as [E R].
  rewrite (Z.mod_small (Z.land (mbyte x) 224)) by (pose proof (MallocWfSlot.land_le_l (mbyte x) 224 ltac:(lia)); pose proof (Z.land_nonneg (mbyte x) 224); lia).
  rewrite E. split; [reflexivity|]. split; [lia|].
  pose proof (Z.mod_pos_bound (mbyte x) 32 ltac:(lia)).
  replace (spanv - 1 + (mbyte x - mbyte x mod 32)) with ((spanv - 1) + (mbyte x / 32) * 32) by (Z.to_euclidean_division_equations; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_byteL x : ltac2:(tb__ "0|4|
S1S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS166Vx;A1A3M0S79S94SdVs;Vm0;Vx;A3A1M1S7cS1aVbyM0;VbyA;VbyB;VbyC;VbyP;Vx;A6M2S7dG2Z20M3A2A2A2A3S1S1S78Z0G0A2S7aG0Z100A2A2S0S69S7dG0G3A2G1A3A2A2").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_byteL. rewrite !ze_alu, ze_bits, ze_byte, !ze_lit. cbn [zalu].
  pose proof (Hbytes x) as (B1 & B2 & _). pose proof (mem_bits x) as (MB & _). pose proof (bits_mod32 x) as [L5 _].
  pose proof (mem_R x) as (_ & _ & _ & _ & RL & _).
  change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). change ((224 mod 2 ^ 64) mod 2 ^ 64) with 224.
  rewrite (Z.mod_small (meta_bits (mam x))) by lia.
  rewrite (Z.land_ones (meta_bits (mam x)) 5) by lia. change (2 ^ 5) with 32. rewrite L5.
  rewrite (Z.mod_small (am_last (mam x))) by lia.
  rewrite (Z.land_ones (am_last (mam x)) 5) by lia. change (2 ^ 5) with 32.
  rewrite (Z.mod_small (am_last (mam x)) 32) by lia. rewrite (Z.mod_small (am_last (mam x))) by lia. rewrite (Z.mod_small (mbyte x)) by lia.
  destruct (lor_low5 (am_last (mam x)) (mbyte x) ltac:(lia) ltac:(lia)) as [E R].
  rewrite (Z.mod_small (Z.land (mbyte x) 224)) by (pose proof (MallocWfSlot.land_le_l (mbyte x) 224 ltac:(lia)); pose proof (Z.land_nonneg (mbyte x) 224); lia).
  rewrite E. split; [reflexivity|]. split; [lia|].
  pose proof (Z.mod_pos_bound (mbyte x) 32 ltac:(lia)).
  replace (am_last (mam x) + (mbyte x - mbyte x mod 32)) with (am_last (mam x) + (mbyte x / 32) * 32) by (Z.to_euclidean_division_equations; lia).
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma ze_onesw_gen e b : ltac2:(tb__ "0|2|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM0S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM1Ve;A3Vb;A3S78Z0Vb;A2S0S69Se9G0G1S2eVe;A1A3SeeS95S7dVb;Z20A2A1A1A3F_;F_;").
Proof using . drop_sp.
  intros E Hb. unfold e_onesw. rewrite ze_aluw, ze_aluw, !ze_lit, E.
  change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2. change ((18446744073709551615 mod 2 ^ 64) mod 2 ^ 32) with (2 ^ 32 - 1).
  apply ones_w_val. exact Hb.
Qed.

Lemma ze_maskG x e b : ltac2:(tb__ "0|2|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM0S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM1Ve;A3Vb;A3S78Z0Vb;A2S0S69Se9G0G1S169Vx;Ve;A2A3SeeS81S93SdVs;Vm0;Vx;A3A1S95S7dVb;Z20A2A1A2A1A3F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros E Hb. unfold e_maskG, e_and. rewrite ze_alu, ze_sx_freed, (ze_onesw_gen e b E Hb). cbn [zalu].
  pose proof (mem_R x) as (_ & R2 & R3 & R4 & _). pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  pose proof (ones_u32 (b mod 32) ltac:(lia)).
  rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by (apply ZBits.sx32_range; lia).
  rewrite sx32_land by lia. reflexivity.
Qed.

Lemma maskG_range x b : ltac2:(tb__ "0|2|
S1S78Z0S81S93SdVs;Vm0;Vx;A3A1S95S7dVb;Z20M0A2A1A2M1A2S7aG1S7eZ2G0A2A2A2").
Proof using HI HMI Hbnc Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  pose proof (mem_R x) as (_ & R2 & R3 & R4 & _). pose proof (Z.mod_pos_bound b 32 ltac:(lia)). pose proof (ones_u32 (b mod 32) ltac:(lia)).
  split; [apply Z.land_nonneg; lia|]. pose proof (MallocWfSlot.land_le_l (am_freed (mam x)) (ones (b mod 32)) ltac:(lia)). lia.
Qed.

Lemma ze_freedG x e b : ltac2:(tb__ "0|3|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM0S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfM1Ve;A3Vb;A3S1S78Z0Vb;A2S7aVb;Z100A2A2S0S69S7dSe9G0G1S168Vx;Ve;A2A3S7eZ2Z20M2A2A2S86S93SdVs;Vm0;Vx;A3A1S95S7dVb;G2A2A1A2A3F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros E Hb. unfold e_freedG, e_and. rewrite ze_alu, ze_sx_freed, ze_aluw, ze_lit, ze_aluw, ze_lit, E. cbn [zalu].
  pose proof (mem_R x) as (R1 & R2 & _ & R4 & _).
  change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2. change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0.
  rewrite (Z.mod_small b (2 ^ 32)) by lia.
  set (XX := (Z.shiftl 2 (b mod 32)) mod 2 ^ 32).
  rewrite (ZBits.sx32_mod32 XX) by (subst XX; apply Z.mod_pos_bound; lia).
  set (YY := (0 - XX) mod 2 ^ 32). assert (HY : 0 <= YY < 2 ^ 32) by (subst YY; apply Z.mod_pos_bound; lia).
  rewrite !(Z.mod_small (sx32 _) (2 ^ 64)) by (apply WalkArith.sx32_range; lia).
  rewrite ZBits.sx32_land by lia. rewrite ZBits.sx32_mod32 by (pose proof (MallocWfSlot.land_le_l (am_freed (mam x)) YY ltac:(lia)); split; [apply Z.land_nonneg; lia | lia]).
  subst YY XX. rewrite negw_sll2_bits by lia. reflexivity.
Qed.

Definition e_last1 (x : member) : sv := ltac2:(tb__ "0|0|
S37Sb0S37SafS77S16Vx;A1A1S33Z1fA1A3S33Z1A1A3").
Lemma ze_last1 x : ltac2:(tb__ "0|0|
S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS160Vx;A1A3S79S94SdVs;Vm0;Vx;A3A1Z1A2A3").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold e_last1. rewrite !ze_alu, ze_bits, !ze_lit. cbn [zalu]. pose proof (mem_bits x) as (MB & _). pose proof (bits_mod32 x) as [L5 _].
  pose proof (mem_R x) as (_ & _ & _ & _ & RL & _).
  change ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5). change (1 mod 2 ^ 64) with 1.
  rewrite (Z.mod_small (meta_bits (mam x))) by lia. rewrite Z.land_ones by lia. change (2 ^ 5) with 32. rewrite L5.
  apply Z.mod_small. lia.
Qed.

Lemma cnt_lt_of x rhoX Lf w : ltac2:(tb__ "0|0|
SdbVrhoW;VrhoX;A2Se8Sa6VK;VLf;VrhoX;Vw;A5Sa1S34S39Sb2S77PacA1S160Vx;A1A3S36VLf;A1A3S7aVspanv;S79S94SdVs;Vm0;Vx;A3A1Z1A2A2F_;F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp Hspanv mW maskv req. try clear Hsp_high. try clear Hdepth.
  intros Hag HSP Hin. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin ltac:(destruct x; reflexivity) ltac:(destruct x; reflexivity)) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze172, ze_last1 in Z0. apply Z.ltb_lt in Z0. exact Z0.
Qed.
Lemma cnt_ge_of x rhoX Lf w : ltac2:(tb__ "0|0|
SdbVrhoW;VrhoX;A2Se8Sa6VK;VLf;VrhoX;Vw;A5Sa1S34S3dS39Sb2S77PacA1S160Vx;A1A3A1S36VLf;A1A3S78S79S94SdVs;Vm0;Vx;A3A1Z1A2Vspanv;A2F_;F_;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp Hspanv mW maskv req. try clear Hsp_high. try clear Hdepth.
  intros Hag HSP Hin. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin ltac:(destruct x; reflexivity) ltac:(destruct x; reflexivity)) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze172, ze_last1 in Z0. rewrite Z.ltb_lt in Z0. lia.
Qed.

Lemma eq0_of e rhoX Lf w : ltac2:(tb__ "0|1|
SdbVrhoW;VrhoX;A2Se8Sa6VK;VLf;VrhoX;Vw;A5Sa1S34S3dS39Sb8Ve;S33Z0M0A1A3A1S36VLf;A1A3S0S57S13aSd9Ve;A2S58A3S0S57SedVe;A1S58A3S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfVe;A3G0A3F_;F_;F_;F_;F_;").
Proof using mW. drop_sp.
  intros Hag HSP Hin Hv Hs. pose proof (zfact_of rhoX Lf w _ Hag HSP Hin ltac:(cbn; rewrite Hv; reflexivity) ltac:(cbn; rewrite Hs; reflexivity)) as Z0.
  cbn [zholds zcond] in Z0. rewrite ze_lit in Z0. change (0 mod 2 ^ 64) with 0 in Z0.
  destruct (Z.eqb_spec (zeval zr1 zl1 e) 0) as [E|E]; [exact E|]. exfalso. apply Z0. reflexivity.
Qed.
Lemma span_cnt_ge2 (am : ameta) : ltac2:(tb__ "0|4|
S78Z0M0S8eVam;A1M1A2S78G0S94Vam;A1A2S1S78Z1S177Vam;A1A2S78S79G1Z2A2M2S96U12cG2S79S9cS7bS91S9bVam;A1A1M3G2A2A2G3A4A2A2F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros Ha Hl. unfold span_cnt.
  pose proof (span_loop_ge 300 (am_aidx am + 2) (UNIT + class_size (am_sc am) * (am_aidx am + 2)) (class_size (am_sc am))).
  destruct (_ <? _); lia.
Qed.

Lemma diff_okb_sound sets xv xe d rhoB : ltac2:(tb__ "0|3|
S0S57S16cVsets;Vxv;Vxe;Vd;A4S58A3S0S57S140SbbS5dS6aS31A2M0S6aS60S6aS31A2Vsets;A4M1A1S58A3S6aS31Sa1G0S5eS6aS31R2R1A4Vsets;A3S0S57S13aS6aS64SdaG1R1A2A1Lu;M2R2A2S58A3F_;Fe;Fj;S0S57SdaG1Vxv;A2S62A3S0S57S13aG2Vxe;A2S58A3S0SabQ40A1S49VrhoB;Vxe;A2S38VrhoB;Vxv;A2A3S158S141VrhoB;Vsets;A2Vd;A2F_;F_;F_;F_;F_;F_;").
Proof using . drop_sp.
  intros Hd Hk Hsv Hxv Hxe Hx. unfold diffs_ok. apply Forall_forall. intros [e t] Hin.
  pose proof (proj1 (forallb_forall _ _) Hd _ Hin) as P. cbn [fst snd] in P.
  assert (AG : forall e0, sv_vars_all (fun u => negb (in_vars (map fst sets) u)) e0 = true -> eval (setp rhoB sets) e0 = eval rhoB e0).
  { intros e0 He0. apply (eval_agree_vars (fun u => negb (in_vars (map fst sets) u))); [| intros l0; rewrite setp_rl; reflexivity | exact He0].
    intros u Hu. apply setp_other. destruct (in_vars (map fst sets) u); [discriminate|reflexivity]. }
  destruct t as [z|j|op a1 b1|op a1 b1|mo a1 b1|mo a1 b1|sg wd a1|ll ii kk]; try discriminate. cbn [fst snd].
  apply Bool.orb_prop in P as [P|P].
  - apply existsb_exists in P as ([j' e'] & Hin' & P). cbn [fst snd] in P. apply andb_prop in P as [P1 P2].
    apply Pos.eqb_eq in P1. apply sv_eqb_sound in P2. subst j' e'.
    change (eval (setp rhoB sets) (SVar j)) with (rw (setp rhoB sets) j).
    rewrite (setp_get rhoB sets j e Hk Hin'). apply AG. exact (Hsv _ _ Hin').
  - apply andb_prop in P as [P1 P2]. apply Pos.eqb_eq in P1. apply sv_eqb_sound in P2. subst j e.
    change (eval (setp rhoB sets) (SVar xv)) with (rw (setp rhoB sets) xv).
    rewrite (AG xe Hxe), setp_other by exact Hxv. exact Hx.
Qed.

Lemma sets_vars_okb_sound sets : ltac2:(tb__ "0|2|
S0S57Sa2S5dS6aS31A2M0G0S13aS6aS64SdaSbbG0S6aS60S6aS31A2Vsets;A4R1A2A1Lu;M1S61S6aS31R1A3A2Lq;Vsets;A3S58A3S6aS31Sa1G0S5eS6aS31R2R1A4Vsets;A3S0S57S13aG1R2A2S58A3F_;Fe;Fj;F_;").
Proof using . drop_sp. intros H j e Hin. exact (proj1 (forallb_forall _ _) H _ Hin). Qed.

Lemma regs_okb_sound f S S' sets rhoA : ltac2:(tb__ "0|1|
S0S57S16dVf;VS;VS';Vsets;A4S58A3S0S57S140SbbS5dS6aS31A2S6aS60S6aS31A2Vsets;A4M0A1S58A3S6aS0S57Vf;R1A1S58A3S0S57SdaG0R2A2S62A3F_;Fu;S69S1S78Z1R1A2S78R1Z1fA2A2S0SabQ40A1S49S141VrhoA;Vsets;A2S3aVS';R2A2A2S49VrhoA;S3aVS;R2A2A2A3F_;Fr;F_;F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros H Hk Hf r Hr.
  assert (Hin : In r (map Z.of_nat (seq 1 31))).
  { apply in_map_iff. exists (Z.to_nat r). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) H r Hin) as P. cbn beta zeta in P.
  apply Bool.orb_prop in P as [P|P].
  - apply existsb_exists in P as ([j e] & Hq & P). cbn [fst snd] in P. apply andb_prop in P as [P1 P2].
    apply sv_eqb_sound in P1. apply sv_eqb_sound in P2. rewrite P1, <- P2.
    change (eval (setp rhoA sets) (SVar j)) with (rw (setp rhoA sets) j). apply setp_get; assumption.
  - apply andb_prop in P as [P1 P2]. apply sv_eqb_sound in P1. rewrite P1.
    apply (eval_agree_vars f); [| intros l0; rewrite setp_rl; reflexivity | exact P2].
    intros u Hu. apply setp_other. apply Hf. exact Hu.
Qed.

Definition rename_chk (f : positive -> bool) (S S' : sstate) (sets : list (positive * sv)) : bool := ltac2:(tb__ "0|2|
S63S63S63S63S63S63S63S63S63S54VS';A1S85S45VS';A1S45VS;A1A2A2Sa2S31S13aVf;A1S40VS;A1A3A2S43S57Lx;S3fVS;A1S58S31S13aVf;R1A2Le;M0X43x2A2S56S31A1S57Lx;S41VS;A1G0S58X56x2A2Sa2S32S139Vf;A1S3bVS;A1A3A2Sa2S34S13bVf;A1S36VS';A1M1A3A2Sa2S34S34Sa4S34S46R1A1S36VS;A1A3Lp;G1A3A2S16dVf;VS;VS';Vsets;A4A2S140SbbS5dS6aS31A2S6aS60S6aS31A2Vsets;A4A1A2").

Lemma rename_link f S S' sets rhoA w : ltac2:(tb__ "0|0|
S0S57S164Vf;VS;VS';Vsets;A4S58A3S6aS0S57Vf;R1A1S58A3S0S57SdaSbbS5dS6aS31A2S6aS60S6aS31A2Vsets;A4R2A2S62A3F_;Fu;S0S5bS31A1S40VS';A1S40VS;A1A3S0S43S3fVS';A1S3fVS;A1A3S0S56S31A1S41VS';A1S41VS;A1A3S0S5bS32A1S3bVS';A1S3bVS;A1A3Se8Sa6VK;VS;VrhoA;Vw;A5Se8Sa6VK;VS';S141VrhoA;Vsets;A2Vw;A5F_;F_;F_;F_;F_;F_;F_;").
Proof using Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hc Hf Efr Efc Ers Eob [Hsm HKw]. split; [|exact HKw].
  unfold rename_chk in Hc.
  apply andb_prop in Hc as [Hc Kd]. apply andb_prop in Hc as [Hc Rgs]. apply andb_prop in Hc as [Hc Inc]. apply andb_prop in Hc as [Hc Fv].
  apply andb_prop in Hc as [Hc Ob]. apply andb_prop in Hc as [Hc Rv]. apply andb_prop in Hc as [Hc Fc]. apply andb_prop in Hc as [Hc Fr].
  apply andb_prop in Hc as [Wf Pc]. apply Z.eqb_eq in Pc.
  apply (smatch_rename f rhoA (setp rhoA sets) S S' w); try assumption.
  - intros u Hu. symmetry. apply setp_other. apply Hf. exact Hu.
  - intros l. rewrite setp_rl. reflexivity.
  - rewrite setp_rm. reflexivity.
  - apply (facts_incl_sound _ _ Inc).
  - apply (regs_okb_sound f S S' sets rhoA Rgs Kd Hf).
Qed.

Lemma seg_runX : ltac2:(tb__ "0|2|
S66S47S5bS146A1M0S179S4eS0S57S53R4A1S62A3S0S6aS44R5A1Sc3A3S0S56G0A1S14aSa6R7SccR6S58A5S59G0R5A2A3SdbVrhoW;R4A2M1S146S4eS17aSa1S146R3RaA3S51Sc3R9R3A3G1Se8Sa6VK;S148R6A1R5R4A5RdR5A1F_;F_;F_;F_;Fw;Frho'';FLf;VTR;Z0Se8Sa6VK;R9R6A4R7A3F_;F_;F_;F_;F_;Frho';FQ;Fleaves;FS;Ffuel;").
Proof using HK Hbnc Hgd Hsc L RR byA byB byC byM0 byP m0 mW maskv req rho s spanv. drop_sp.
  intros fuel S leaves Q rho' Hl Hn Hrun Hag HQ.
  apply ((trr_run RR) 0 fuel CUTS K S leaves rho' Q (Z.le_refl 0) Hrun Hl HK).
  intros Lf rho'' Hin Hab. rewrite Hn in Hab. apply (trr_skip RR); [apply Z.le_refl|]. intros w HSP. apply (HQ Lf rho'' w Hin Hab); [|exact HSP].
  eapply agrees_below; [exact Hag | exact Hab | unfold NXA; lia].
Qed.

Lemma ev_addw rho'' j e a b : ltac2:(tb__ "0|3|
SdbVrhoW;Vrho'';A2S0S69SacQ40M0S38Vrho'';Vj;A2A2Va;A3S0S57S13aSd9Ve;A2S58A3S0S57SedVe;A1S58A3S0S69Se9S19Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfVe;A3Vb;A3S78Z0M1Va;A2S78G1Vb;A2S7aS79Va;Vb;A2M2S7eZ2Z1fA2A2S0S69SacG0S49Vrho'';S35Sb0S30Vj;A1Ve;A3A2A2G2A3F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Hbnc Hgd Hsc Hsp mW. try clear Hsp_high. try clear Hdepth.
  intros Hag Hj Hv Hs He Ha Hb Hab.
  rewrite eval_zeval by (cbn; exact Hs). cbn [zeval].
  assert (EE : zeval (zr_of rho'') (zl_of rho'') e = b).
  { rewrite <- He, <- (EVu rho'' e Hag Hv Hs). symmetry. apply eval_zeval. exact Hs. }
  rewrite EE. unfold zr_of. rewrite Hj. cbn [zalu].
  rewrite !Z.mod_small by lia. apply sx32_small. lia.
Qed.

Lemma test_holds rho'' a c : ltac2:(tb__ "0|6|
S0S69SacQ40M0S38Vrho'';Pd3M1A2A2Va;A3S0S69SacG0S38Vrho'';Pd2M2A2A2Vc;A3S1S78Z0M3Va;A2S7aVa;S7eZ2Z3eA2M4A2A2S1S78G3Vc;A2S7aVc;G4A2A2S5S52Vrho'';S39Sb5S37Sb4S30G1A1S30G2A1A3S33Z1000M5A1A3A2S7aS83Vc;Va;A2G5A2A2F_;F_;F_;F_;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros Ha Hc Ra Rc. rewrite holds_zholds by reflexivity. cbn [zholds zeval zcond zalu]. unfold zr_of. rewrite Ha, Hc.
  rewrite !Z.mod_small by lia.
  assert (XR : 0 <= Z.lxor a c < 2 ^ 62).
  { split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor a c) 0) as [->|]; [lia|].
    apply (Z.le_lt_trans _ (Z.lxor a c)); [lia|].
    apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
    pose proof (Z.log2_lxor a c ltac:(lia) ltac:(lia)) as LX.
    assert (Z.log2 a < 62) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
    assert (Z.log2 c < 62) by (destruct (Z.eq_dec c 0) as [->|]; [cbn; lia|]; apply Z.log2_lt_pow2; lia).
    lia. }
  change (toS 64 4096) with 4096.
  unfold toS. rewrite (Z.mod_small (Z.lxor a c)) by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
  replace (Z.lxor a c <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Z.lxor_comm. rewrite Z.ltb_lt. tauto.
Qed.

Section SpanLoop.
  Variable x : member.
  Variables (SL L0 L1 SX : sstate) (LL : list leaf) (dX : list (sv * sv)).
  Let size : Z := class_size sc.
  Let fB : positive -> bool := ltac2:(tb__ "0|0|
S6aS64SdaS55S6aPd2S55S6aPd5S55S6aPd4S55S6aPd3S5cS6aA1A3A3A3A3R1A2A1Lu;").
  Definition setsB : list (positive * sv) := ltac2:(tb__ "0|1|
S55S5dS6aS31A2M0S5eS6aS31Pd2S3aVL0;Z5A2A4S55G0S5eS6aS31Pd5S3aVL0;Z6A2A4S55G0S5eS6aS31Pd4S3aVL0;ZeA2A4S55G0S5eS6aS31Pd3S3aVL0;Z10A2A4S5cG0A1A3A3A3A3").
  Definition setsX : list (positive * sv) := scratch_of dX.

  Hypothesis HrunL : ltac2:(tb__ "0|1|
S0S56S5bS146A1M0A1S14aSa6U12cSccVSL;S58A5S59G0VLL;A2A3").
  Hypothesis HLL : ltac2:(tb__ "0|0|
S0S5bS146A1VLL;S55S146S149VL0;S147A2S55S146S149VL1;S147A2S5cS146A1A3A3A3").
  Hypothesis HSL_len : ss_lenient SL = false.
  Hypothesis HSL_next : ltac2:(tb__ "0|0|
S0S6aS44VSL;A1Sc3A3").
  Hypothesis HSL_regs : ltac2:(tb__ "0|0|
S1S0S31S3aVSL;Z5A2S30Pd2A1A3S1S0S31S3aVSL;Z10A2S30Pd3A1A3S0S31S3aVSL;ZeA2S30Pd4A1A3A2A2").
  Hypothesis Hren : ltac2:(tb__ "0|0|
S0S57S164VfB;VL0;VSL;S156A4S58A3").
  Hypothesis HL0_same : ltac2:(tb__ "0|0|
S1S0S5bS31A1S40VSL;A1S40VL0;A1A3S1S0S43S3fVSL;A1S3fVL0;A1A3S1S0S56S31A1S41VSL;A1S41VL0;A1A3S0S5bS32A1S3bVSL;A1S3bVL0;A1A3A2A2A2").
  Hypothesis HL0_5 : ltac2:(tb__ "0|0|
S0S31S3aVL0;Z5A2S35Sb0S30Pd2A1S15eVx;A1A3A3").
  Hypothesis HL0_14 : ltac2:(tb__ "0|0|
S0S31S3aVL0;ZeA2S35Sb0S30Pd4A1S33Z1A1A3A3").
  Hypothesis HL0_16 : ltac2:(tb__ "0|0|
S0S31S3aVL0;Z10A2S35Sb0S30Pd3A1S15eVx;A1A3A3").
  Hypothesis HT0 : ltac2:(tb__ "0|0|
Sa1S34S39Sb5S37Sb4S30Pd3A1S30Pd2A1A3S33Z1000A1A3S36VL0;A1A3").
  Hypothesis HT1 : ltac2:(tb__ "0|0|
Sa1S34S3dS39Sb5S37Sb4S30Pd3A1S30Pd2A1A3S33Z1000A1A3A1S36VL1;A1A3").
  Hypothesis HL1_14 : ltac2:(tb__ "0|0|
S0S31S3aVL1;ZeA2S35Sb0S30Pd4A1S33Z1A1A3A3").

  Hypothesis Hswf_SX : swf SX = true.
  Hypothesis HsdX : ltac2:(tb__ "0|3|
S0S56S5dS5bS5dS31S31A2A1M0S5bS34A1M1A2M2A1S157VL1;VSX;A2S59G2S5eG0G1VdX;S55S34S50S77PacA1S33Z12cA1A2S5cS34A1A3A4A2A3").
  Hypothesis HdX : ltac2:(tb__ "0|0|
S0S57S16cS154PacS3aVL1;ZeA2VdX;A4S58A3").
  Hypothesis HkeysX : ltac2:(tb__ "0|0|
S0S57S140SbbS5dS6aS31A2S6aS60S6aS31A2S154A4A1S58A3").
  Hypothesis HsetsX_vars : ltac2:(tb__ "0|1|
S0S57Sa2S5dS6aS31A2M0G0S13aS6aS64SdaSbbG0S6aS60S6aS31A2S154A4R1A2A1Lu;S61S6aS31R1A3A2Lq;S154A3S58A3").
  Hypothesis HsetsX_hi : ltac2:(tb__ "0|0|
S0S57Sa2S6aS6aS64Sd9R1A1A1Lj;SbbS5dS6aS31A2S6aS60S6aS31A2S154A4A3S58A3").
  Hypothesis HvarsX : ltac2:(tb__ "0|0|
S0S57S13cS6aS64SdaSbbS5dS6aS31A2S6aS60S6aS31A2S154A4R1A2A1Lu;VL1;A2S58A3").
  Hypothesis HxeX : ltac2:(tb__ "0|1|
S1S0S57S13aS6aS64SdaSbbS5dS6aS31A2S6aS60S6aS31A2S154A4M0R1A2A1Lu;S3aVL1;ZeA2A2S58A3S0S57SdaG0PacA2S62A3A2").

  Definition LINV (span cnt : Z) (rho' : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0S69SacQ40M0S38Vrho';Pd2A2A2Vspan;A3S1S0S69SacG0S38Vrho';Pd3A2A2S7cS79Vspan;Vsize;A2Z1M1A2A3S0S69SacG0S38Vrho';Pd4A2A2S7cVcnt;G1A2A3A2A2").

  Lemma e_size_sem : ltac2:(tb__ "0|1|
S1S0S57S13aSd9S15eVx;A1M0A2S58A3S0S57SedG0A1S58A3A2").
  Proof using HL0_16 HL0_5. drop_sp. destruct x; split; reflexivity. Qed.

  Lemma fB_keys u : ltac2:(tb__ "0|0|
S0S57VfB;Vu;A1S58A3S0S57SdaSbbS5dS6aS31A2S6aS60S6aS31A2S156A4Vu;A2S62A3F_;").
  Proof using . drop_sp. unfold fB, setsB. cbn [map fst]. intros H. destruct (in_vars _ u); [discriminate|reflexivity]. Qed.

  Lemma back_edge rho'' w span cnt : ltac2:(tb__ "0|5|
SdbVrhoW;Vrho'';A2S155Vspan;Vcnt;Vrho'';A3S78Z10Vspan;A2S78Z1M0Vcnt;A2S7aS79Vspan;S7bZ2M1Vsize;A2A2S7eG1Z1fA2M2A2S7aS79Vcnt;G0A2M3G2A2Se8Sa6VK;VL0;Vrho'';Vw;A5S1SdbVrhoW;S141Vrho'';S156A2M4A2S1S155S79Vspan;Vsize;A2G3G4A3Se8Sa6VK;VSL;G4Vw;A5A2A2F_;F_;F_;F_;F_;F_;F_;").
  Proof using HI HL0_14 HL0_16 HL0_5 HL0_same HMI HSL_next HSL_regs Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hren Hreq Hsc Hsp Hspanv HxeX mW. try clear Hsp_high.
    intros Hag (I1 & I2 & I3) Hspn Hc Hb1 Hb2 HSP. pose proof size_range as [SR _]. fold size in SR.
    destruct e_size_sem as [Sv Ss].
    split; [|split].
    - apply agrees_setp; [exact Hag | reflexivity].
    - unfold LINV.
      rewrite (setp_get rho'' setsB 210%positive (reg_sv L0 5) eq_refl ltac:(cbn; tauto)).
      rewrite (setp_get rho'' setsB 211%positive (reg_sv L0 16) eq_refl ltac:(cbn; tauto)).
      rewrite (setp_get rho'' setsB 212%positive (reg_sv L0 14) eq_refl ltac:(cbn; tauto)).
      rewrite HL0_5, HL0_14, HL0_16.
      rewrite (ev_addw rho'' 210%positive (e_size x) span size Hag I1 Sv Ss (ze_size x)) by lia.
      rewrite (ev_addw rho'' 211%positive (e_size x) (span + size - 1) size Hag I2 Sv Ss (ze_size x)) by lia.
      rewrite (ev_addw rho'' 212%positive (SLit 1) (cnt - 1) 1 Hag I3 eq_refl eq_refl eq_refl) by lia.
      lia.
    - destruct HL0_same as (E1 & E2 & E3 & E4).
      apply (rename_link fB L0 SL setsB rho'' w Hren fB_keys E1 E2 E3 E4 HSP).
  Qed.

  Lemma exit_edge rho'' w span cnt : ltac2:(tb__ "0|1|
SdbVrhoW;Vrho'';A2S155Vspan;Vcnt;Vrho'';A3S78Z1M0Vcnt;A2S7aS79Vcnt;G0A2S7eZ2Z1fA2A2S0S69Vcnt;Vspanv;A3Se8Sa6VK;VL1;Vrho'';Vw;A5S144Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;VmW;VK;VSX;Vw;A13F_;F_;F_;F_;F_;F_;").
  Proof using HL1_14 HSL_next Hbnc HdX Hgd HkeysX Hsc HsdX HsetsX_hi HsetsX_vars Hsp Hspanv Hswf_SX HvarsX HxeX. try clear Hsp_high. try clear Hdepth.
    intros Hag (I1 & I2 & I3) Hc Hb Ecnt HSP.
    eapply (linkp L1 SX setsX dX [SPUle (v 172) (SLit 300)] rho'' w HvarsX HsetsX_hi Hswf_SX HsdX Hag); [|exact HSP].
    intros HagS _. split.
    - apply (diff_okb_sound setsX 172%positive (reg_sv L1 14) dX rho'' HdX HkeysX (sets_vars_okb_sound setsX HsetsX_vars) (proj2 HxeX) (proj1 HxeX)).
      rewrite HL1_14. apply bv_eq. rewrite (ev_addw rho'' 212%positive (SLit 1) (cnt - 1) 1 Hag I3 eq_refl eq_refl eq_refl) by lia.
      rewrite (rw_agrees rho'' 172%positive Hag eq_refl). change (bv_unsigned (rw1 172%positive)) with (zr1 172%positive). rewrite zr1_172. lia.
    - constructor; [|constructor]. apply (proj2 (HOLDS _ (SPUle (v 172) (SLit 300)) HagS eq_refl eq_refl)). cbn [zholds]. rewrite ze172, ze_lit.
      change (300 mod 2 ^ 64) with 300. pose proof Hspanv. lia.
  Qed.

  Theorem span_loop_sound : ltac2:(tb__ "0|3|
S66S69S69S4eSdbVrhoW;R1A2S155R4R3R2A3S78Z10R5A2S78Z1M0R5A2S7aS79S79R6S84R8A1A2G0A2S7eZ2M1Z1fA2M2A2S7aS79R8S7bS79S84R9A1G1A2Vsize;A2A2G2A2S0S57S16bRaR9Vsize;A3S58A3S0S69S96RbR9RaVsize;A4Vspanv;A3VTR;Z0Se8Sa6VK;VSL;R9A4S144Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;VmW;VK;VSX;A12A3F_;F_;F_;F_;F_;F_;F_;F_;Frho';Fcnt;Fspan;Ffuel;").
  Proof using HI HK HL0_14 HL0_16 HL0_5 HL0_same HL1_14 HLL HMI HSL_len HSL_next HSL_regs HT0 HT1 Hbnc Hbnc_val Hbytes HdX Hdepth Hgd Hhd HkeysX Hmaskv Hren Hreq HrunL Hsc HsdX HsetsX_hi HsetsX_vars Hsp Hspanv Hswf_SX HvarsX HxeX RR. try clear Hsp_high.
    induction fuel as [|fuel IH]; intros span cnt rho' Hag HINV Hspn Hc Bc Bs Hex Hsl; [discriminate|].
    pose proof size_range as [SR _]. fold size in SR.
    rewrite span_exits_S in Hex. rewrite span_loop_S in Hsl.
    apply (tr_seq _ (fun w => POST SX w \/ (exists rho_n, (agrees rhoW rho_n /\ LINV (span + size) (cnt + 1) rho_n /\ Z.lxor span (span + size - 1) < 4096) /\ SymSoundR.SP segsU K SL rho_n w))).
    - apply (seg_runX 300 SL LL _ rho' HSL_len HSL_next HrunL Hag).
      intros Lf rho'' w Hin Hab Hag'' HSP. rewrite HLL in Hin.
      assert (HINV'' : LINV span cnt rho'').
      { destruct HINV as (I1 & I2 & I3). destruct Hab as (Aw & _ & _). unfold LINV.
        rewrite <- (Aw 210%positive), <- (Aw 211%positive), <- (Aw 212%positive) by (unfold NXA; lia). auto. }
      pose proof HINV'' as (I1 & I2 & I3).
      pose proof (test_holds rho'' (span + size - 1) span I2 I1 ltac:(lia) ltac:(lia)) as TT.
      destruct Hin as [<-|[<-|[]]]; cbn [lf_state] in HSP.
      +
        pose proof (proj1 TT (proj1 (Forall_forall _ _) (SP_facts_hold segsU K rho'' L0 w HSP) _ HT0)) as T1.
        destruct (back_edge rho'' w span cnt Hag'' HINV'' Hspn Hc ltac:(lia) ltac:(lia) HSP) as (HagB & HINVB & HSPB).
        right. exists (setp rho'' setsB). split; [split; [exact HagB | split; [exact HINVB | exact T1]] | exact HSPB].
      +
        assert (T1 : ~ Z.lxor span (span + size - 1) < 4096).
        { intros T1. apply (proj1 (Forall_forall _ _) (SP_facts_hold segsU K rho'' L1 w HSP) _ HT1). cbn [SymState.holds]. apply (proj2 TT). exact T1. }
        replace (Z.lxor span (span + size - 1) <? 4096) with false in Hex, Hsl by (symmetry; apply Z.ltb_ge; lia).
        left. exact (exit_edge rho'' w span cnt Hag'' HINV'' Hc ltac:(lia) Hsl HSP).
    - apply tr_disj; [apply tr_refl|]. apply tr_ex. intros rho_n. apply tr_pure. intros (HagB & HINVB & T1).
      replace (Z.lxor span (span + size - 1) <? 4096) with true in Hex, Hsl by (symmetry; apply Z.ltb_lt; exact T1).
      exact (IH (span + size) (cnt + 1) rho_n HagB HINVB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hex Hsl).
  Qed.
End SpanLoop.

Section Entry.
  Variable x : member.
  Variables (LAs SL : sstate) (dA : list (sv * sv)).
  Definition setsA : list (positive * sv) := scratch_of dA.
  Hypothesis Hswf_SL : swf SL = true.
  Hypothesis HsdA : ltac2:(tb__ "0|3|
S0S56S5dS5bS5dS31S31A2A1M0S5bS34A1M1A2M2A1S157VLAs;VSL;A2S59G2S5eG0G1VdA;S5cS34A1A4A2A3").
  Hypothesis HdA : ltac2:(tb__ "0|1|
S0S57S16cS145P1M0S30G0A1VdA;A4S58A3").
  Hypothesis HkeysA : ltac2:(tb__ "0|0|
S0S57S140SbbS5dS6aS31A2S6aS60S6aS31A2S145A4A1S58A3").
  Hypothesis HsetsA_vars : ltac2:(tb__ "0|1|
S0S57Sa2S5dS6aS31A2M0G0S13aS6aS64SdaSbbG0S6aS60S6aS31A2S145A4R1A2A1Lu;S61S6aS31R1A3A2Lq;S145A3S58A3").
  Hypothesis HsetsA_hi : ltac2:(tb__ "0|0|
S0S57Sa2S6aS6aS64Sd9R1A1A1Lj;SbbS5dS6aS31A2S6aS60S6aS31A2S145A4A3S58A3").
  Hypothesis HvarsA : ltac2:(tb__ "0|0|
S0S57S13cS6aS64SdaSbbS5dS6aS31A2S6aS60S6aS31A2S145A4R1A2A1Lu;VLAs;A2S58A3").
  Hypothesis HinA : ltac2:(tb__ "0|1|
S1Sa1S5dS6aS31A2M0S5eS6aS31Pd2S163Vx;A1A4S145A3S1Sa1G0S5eS6aS31Pd3S162Vx;A1A4S145A3Sa1G0S5eS6aS31Pd4S161Vx;A1A4S145A3A2A2").
  Hypothesis Hno1 : ltac2:(tb__ "0|0|
S0S57SdaSbbS5dS6aS31A2S6aS60S6aS31A2S145A4P1A2S62A3").

  Theorem loop_entry rhoA w : ltac2:(tb__ "0|2|
SdbVrhoW;VrhoA;A2Se8Sa6VK;VLAs;VrhoA;Vw;A5S1SdbVrhoW;S141VrhoA;S145A2M0A2S1S165S16aVsc;S8eSdVs;Vm0;Vx;A3A1M1A2S79G1Z2A2G0A3Se8Sa6VK;VSL;G0Vw;A5A2A2F_;F_;").
  Proof using HI HMI Hbnc Hbytes HdA Hgd Hhd HinA HkeysA Hno1 Hsc HsdA HsetsA_hi HsetsA_vars Hsp Hswf_SL HvarsA mW maskv req spanv. try clear Hsp_high. try clear Hdepth.
    intros Hag HSP. pose proof (agrees_setp rhoA setsA Hag HsetsA_hi) as HagS.
    split; [exact HagS|]. split.
    - destruct HinA as (In1 & In2 & In3). unfold LINV.
      rewrite (setp_get rhoA setsA 210%positive (e_span0 x) HkeysA In1), (setp_get rhoA setsA 211%positive (e_a60 x) HkeysA In2), (setp_get rhoA setsA 212%positive (e_a40 x) HkeysA In3).
      rewrite !(EVu rhoA _ Hag) by (destruct x; reflexivity). rewrite ze_span0, ze_a60, ze_a40. lia.
    - apply (relinkp rhoA LAs SL w setsA dA [] HvarsA Hswf_SL HsdA); [| constructor | exact HSP].
      apply (diff_okb_sound setsA 1%positive (SVar 1%positive) dA rhoA HdA HkeysA (sets_vars_okb_sound setsA HsetsA_vars) Hno1); [|reflexivity].
      cbn [sv_vars_all]. rewrite Hno1. reflexivity.
  Qed.
End Entry.

End L.
End Mal_aslot_L.
