(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MM0"; "MA_"; "OD_meta"; "pA"; "MB"; "MP"; "vptr"; "pM0"; "MC"; "mam"; "vbits"; "vmem"; "od_ok_at"; "vavail"; "vfreed"; "pP"; "OD_act"; "OD_bnc"; "OD_mem"; "mptr"; "pC"; "OD_ctz"; "OD_got"; "OD_guard"; "OD_sct"; "obj_of"; "pB"; "O_stk"; "mbyte"; "e_bncidx"; "member"; "zl1"; "zr1"; "od_range"; "vbyte"; "e_ctz"; "od_ok"; "zA"; "e_sx"; "D0"; "e_lowbit"; "sp0"; "@Corelib.Init.Datatypes"; "cons"; "app"; "option"; "Some"; "list"; "true"; "nil"; "bool"; "prod"; "pair"; "None"; "snd"; "fst"; "length"; "false"; "nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sobj"; "sprop"; "SLit"; "sv"; "SAluW"; "ss_facts"; "rw"; "SAlu"; "ss_objs"; "SPBranch"; "smatch"; "SExt"; "SPNot"; "FcsrFrm0"; "reg_sv"; "rm"; "mkSS"; "ob_cells"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "sprop_eqb"; "ss_next"; "ss_pc"; "ss_resv"; "sstate"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "LCtx"; "CTX_active"; "keys"; "active_hd"; "loc_addr"; "CTX_bounces"; "Inv"; "alinks"; "ring_ok"; "memb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "modulo"; "opp"; "to_nat"; "pow"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "mslot"; "sptr"; "astate"; "MUsed"; "st_bounces"; "IRet"; "itree"; "lowbit"; "am_aidx"; "am_avail"; "am_freed"; "am_set_links"; "try_avail"; "IB"; "am_maplen"; "am_mem"; "class_size"; "znth"; "am_last"; "am_sc"; "ones"; "zset"; "am_next"; "am_prev"; "ctz32"; "am_set_avail"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "hd"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "set_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "callee_saved"; "pre_reg"; "pre_regs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_AND"; "ALU_SLL"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD"; "lfs"; "ST_D4sr"; "ST_D5nh"; "ST_D5nr"; "LT_D4sr"; "LT_D5nh"; "LT_D5nr"; "NXA"; "SA_D4sr"; "SA_D5nh"; "SA_D5nr"; "DT_D4sr"; "DT_D5nh"; "DT_D5nr"; "LA_D4srs"; "LA_D5nhs"; "LA_D5nrs"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "maskA"; "e_avT"; "e_bncdec"; "e_freedT"; "e_maskA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nr.VD5nr"; "sR'"; "s1V"; "s3V"; "am1_B"; "xp"; "am1_A"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "am1_P"; "dsC1"; "S0R";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD4sr.VD4sr"; "sR'"; "s1V"; "s3V"; "am1_C"; "xp"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "am1_A"; "am1_B"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VD5nh.VD5nh"; "sR'"; "am1_A"; "s1V"; "s3V"; "xp"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "xn"; "dsC2"; "LT1"; "LT2"; "LT0"; "am1_M0"; "am1_P"; "dsC1"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sprop_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "ST_R1nh"; "lfs"; "LT_R1nh"; "LA_Hs"; "SA_H"; "SA_R1nh"; "NXA"; "DT_R1nh"; "LA_R1nhs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "HITP"; "oStkF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VR1nh.VR1nh"; "am1_M0"; "sR'"; "s3V"; "s1V"; "dsR"; "dsC0"; "dsF0"; "dsF1"; "dsF2"; "s2V"; "dsC2"; "LT1"; "LT2"; "LT0"; "dsC1"; "S0R"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zholds"; "psupported"; "zeval"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "s1_deq"; "s1a"; "am_final"; "s4"; "s5"; "s6"; "step1"; "step2"; "step3"; "t_mask"; "s1b"; "hit_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G5.Mal_aslot_VH.VH"; "sH'"; "dsHF"; "E_avH"; "dsHC"; "amH'"; "objsH"; "S0H"; "dsH"; "stkH"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "as_stack"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "stop_reason"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs"; "sh"].
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

Module Mal_aslot_VD5nh.

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

Section VD5nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;S3aS38S74S68A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S6aZ0Vreq;A2S6aS6bVreq;S80A2S83Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S32S74A1S60Vs;Vsc;A2S33S74Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S65S64VX;Vs;Vsc;A3S33S74Vm0;A2S30S74Vm0;Vrest;A3A3").
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
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§2§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§2§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§2§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S148S125VX;S3aS38S74S68A2A1VU;S124Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S6aZ0M0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S6cG1Z100A2A2S1S0S68S6fG1Z20A2S7bSfVs;Vm0;R1A3M2A1A3S2S0S68S81G2A1G0A3A1S0S68S22VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bSfVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§3§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§3§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§4§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§5§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§5§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§4§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Notation "§6§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze161 := (§6§ U.Mal_aslot__G1.Mal_aslot_I.ze161).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S6aZ1000S9bQ40S47Vrho;PaA2A2M0A2S0S68S6fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S6aS12aZ40S9bQ40S47Vrho;PfA2A2A2M0S70S147Z0A1A1A2S6aS70S72Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6aS129VL;A1S6bS9bQ40M0S47Vrho;PaA2A2S12aZ40S9bG0S47Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§7§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§7§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§8§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§5§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;Vrd0;Sb9S95VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S9aQ40A1S37F_;Vwok0;SbaS95VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z60A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ecR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z20A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ccR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS2bVL;S82SfVs;Vm0;R1A3A1A2Z8A2A2A3S33G1S9cG0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS6bZ5a3d0Z369A2Vsc;A2A2A3S33G1S9cG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S127S126Vrd0;S9aQ40A1S35L_;A2S128S125A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S126Sb9S95VmW;A2SbaS95VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§9§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§9§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§1§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§10§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§10§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§5§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§5§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§5§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S0S68Vbnc;S84S6dVsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§11§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§11§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S149S95VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S34Sb5A1Sb6OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§12§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§12§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§13§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§13§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§14§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§14§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§15§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§15§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§1§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§8§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§8§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§16§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§16§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§17§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§17§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§18§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§18§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§19§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§19§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§19§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§16§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§13§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§20§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§20§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§20§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§20§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
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
Local Abbreviation nonhead_avail0 := (§3§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;VmW;S50Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Sb7Vvm;Sb8Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S34Sb5A1M0Sb6VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Sb6R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4bS95Vrho;S146S145A1S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S68S7cSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S68S7dSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S68S7dSfVs;Vm0;S7A3M0A1S87S85G0A1A1A3A1").
Hypothesis HVact : maskA MA_ <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S68Vmaskv;SbcVs;Vm0;S7A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;SdVm0;A1A2S33S73S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MP).
Definition xn : mslot := (MUsed (mam MA_)).
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|1|
S7eS33S74S15Vs;Vm0;A2A2S89SfVs;Vm0;S7A3M0A1G0A3").
Definition am1_P : ameta := ltac2:(tb__ "0|1|
S7eS8aSfVs;Vm0;SbA3M0A1S33S74S9Vs;Vm0;A2A2G0A3").
Definition s1V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sf2Sf9A8").
Definition s2V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sf2Sf9A8").
Definition s3V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sf2Sf9A8").
Lemma HXp : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;S15Vs;Vm0;A2A2S33S73Sf2A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MP))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S32S73A1S5cS12fVs;S15Vs;Vm0;A2S9Vs;Vm0;A2M0Sf2A4G0A2S33S73Sf9A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|0|
S0S34S74A1S5fS12fVs;S15Vs;Vm0;A2S9Vs;Vm0;A2Sf2A4A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MP). Qed.
Lemma K1b : ltac2:(tb__ "0|0|
S0S34S74A1S5fS138Vs;S15Vs;Vm0;A2S9Vs;Vm0;A2Sf2Sf9A5A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S34S74A1S5fSf0A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf0S19Vs;Vm0;S6A3A2S33S73S76SfeA1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf0S19Vs;Vm0;S7A3A2S33S73S76SefA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_P : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf0S19Vs;Vm0;SbA3A2S33S73S76SffA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_P, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MP)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf1Vq;A2S5cSf0Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S34S68A1S77Sf1A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S32S74A1S60Sf1Vsc;A2S33S74S9Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S38S32S74A1M0S75A2M1A2S134Vsc;SdVm0;A1Vam0;Vs;A4S78S75G1S39G0S75S33S74S9Vs;Vm0;A2A2Sf0A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pP pA xp xn).
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
S0S74S9Vs;Vm0;A2S19Vs;Vm0;S7A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf0S9Vs;Vm0;A2A2S33S73S76SefA1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S38S74S75A2M0A2S135Vsc;S9Vs;Vm0;A2M1SefSf0A4S78S75G0S39S74S75G1Sf8A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf8S9Vs;Vm0;A2A2S33S73S76SefA1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S79S75S38S74S75A2M0A2S136Vsc;S9Vs;Vm0;A2M1SefSf8A4S78S75G0S39S74S75G1Sf1A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_A. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSf1S9Vs;Vm0;A2A2S33S73S76SefA1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_A. Qed.
Lemma Hav3 : am_avail am1_A = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_A. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S68S137SefA1SbcVs;Vm0;S7A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MA_ <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S133Sf1S9Vs;Vm0;A2SefA3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75S7aSbcVs;Vm0;S7A3A1SeeA4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V am1_A S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S68S7aSbcVs;Vm0;S7A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MA_). pose proof (lowbit_range (maskA MA_) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S13aVX;VU;Vs;Vsc;S7aSbcVs;Vm0;S7A3A1SeeA6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S32S74A1S60SeeVsc;A2S33S74S9Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA am1_A). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S32S73A1S5cSeeS9Vs;Vm0;A2A2S33S73S76S130SefA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S68S86SefA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSeeS19Vs;Vm0;S6A3A2S33S73S76SfeA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_P : ltac2:(tb__ "0|0|
S0S32S73A1S5cSeeS19Vs;Vm0;SbA3A2S33S73S76SffA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA am1_A); [rewrite MT3; exact MT1_P | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
S93Vs;Sf0S31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3S92SdVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pP pA xp xn))); [apply (delta_trans _ (s1b s pP pA xp xn)); [apply (delta_trans _ (s1a s pP pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pP (mam MP)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
S93Sf0Sf8S36S5bA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S93Sf8Sf1S36S5bA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
S93Vs;Sf1S31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M0A3A3S92SdVm0;A1A1A3G0A3G0A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|1|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1M0A1S30S5S8S6S67ScSbA1A1S67ScS7A1A1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7G0S67ScSaA1A1S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7S30S5S18S7S67S28S7A1A1A2S30S5S8SbS67Pa1A1G0S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7S30S5S1eS30S5S1bS30S5S17S7S67PaaA1A2S36S5A1A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49SadA1S30S41S21Sc1S5S41S1fSf3A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D5nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [exact ze161 | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46SadA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D5nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MP)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MA_)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S51Z2126cS99S96S4eS3aS44A1S30S41S21S36S41A1A3S46SadA1SabS3eA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4bS95VrhoW;S101S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4M0A4S4bS95VrhoW;SadG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D5nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S32S38S34S38S44S44A2M0A1M1S34S42A1M2A2M3A1S14aSb3Sa6A2S33G3S39G1G2S30G0S39S44S44Sc0S7A1S40PabA1A4S36G0A1A3S3bG1G2Sb0A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D5nh)). Qed.
Lemma swf_ST : swf ST_D5nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S37S8eS42S42S91S42S56R1A1S46Sa6A1A3Lp;S3bS34S38S44S44A2A1S34S42A1Sb0A3A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S37S8eS42S103SedA1S46Sa6A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S37S8eS42S12cS46Sa6A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46Sa6A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D5nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MP)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D5nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S69S57Sa6A1SabA3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D5nh 0 ST_D5nh.
Definition LT1 : sstate := lfs LT_D5nh 1 ST_D5nh.
Definition LT2 : sstate := lfs LT_D5nh 2 ST_D5nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49SfdA1A2Sf5A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49SfbA1A2Sf6A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49SfcA1A2Sf7A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSf5A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSf6A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSf7A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSf5A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSf6A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSf7A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSf3Sf5A2Sf4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSf3Sf6A2S100A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSf3Sf7A2SfaA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|2|
S0S34S5A1Sf4S30S5S16S67ScS7A1A1M0A1S30S5S8S6S43Z0A1M1G1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7S67ScSbA1A1S67ScSaA1A1S67S11S7A1A1SbdSbfS7A1S67S10S7A1A1A7S30S5S8SbS67Pa1A1G0S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7S36S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S34S5A1SfaS31S5Sf4S30S5S17S7SbeA2S36S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S3fS3dS5VdsF;A2S3dS5Sf3A2A3S5S8dS5R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S8dS5R2SbbSf3VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S34S5A1M0G0S5S8dS5R1SbbR3R2A2A3S8dS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sa3Vk;U3A2S0S34S41A1S49Sa4Sa9Vk;Sa6A3A1M0S30S41S111S52S90S41S21G0A3A1A1S8fS41G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S68S58Sa4Sa9Vk;Sa6A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S34S44A1S55Sa4Sa9Vk;Sa6A3A1S96A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S53S54Sa4Sa9Vk;Sa6A3A1S4eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S32S44A1S59Sa4Sa9Vk;Sa6A3A1S3aS44A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S44S4fSa4Sa9Vk;Sa6A3ZaA2S29S67PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S68S1S6aZ1R1A2S6aR1Z1fA2A2S0S37S97S71R2A1A1S35A3S0S44S4fSa4Sa9Vk;Sa6A3R3A2S98S71R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D5nh k ST_D5nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S8dS42S4aSa0S43Z1fA1S23S7A1A3S46SfdA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S8dS42S4aSa1S67PaaA1S43Z0A1A3S46SfbA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23S7A1A3A1S46SfbA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa1S67PaaA1S43Z0A1A3A1S46SfcA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23S7A1A3A1S46SfcA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S0S75S132Sf1S9Vs;Vm0;A2M1SefA3S131Sf1G1SefA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA am1_A (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S93Vs;SeeS31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1M1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M2A3A3S92SdVm0;A1A1A3G2A3G2A3S31S5bS31S5bG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA am1_A ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S93Vs;SeeS31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1M1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M2A3A3S92SdVm0;A1A1A3G2A3G2A3S31S5bS31S5bG1S30S5bS5dS6bS62S6dVsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA am1_A ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S0S34S68A1S77SeeA1S88S6dVsc;G0A2S6dVbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA am1_A (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeS8S7S67ScSbA1A1S67ScSaA1A1S67S11S7A1A1SbdSbfS7A1S67S10S7A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_A). split; [exact MT_R'|].
  pose proof (am_final_fields am1_A) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MP); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_A; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_A; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeS16S67ScS7A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeS17S7SbeA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeS8S6S43Z0A1M0G0S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7A11").
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
Lemma ok_P' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeS8SbS67Pa1A1S67ScS7A1A1S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_P. split; [exact MTF_P|].
  split; [rewrite ze161; unfold am1_P, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MP), ?(am_next_mam MP); cbn [optrZ]; reflexivity|].
  split; [rewrite (ze_ptr MA_); unfold am1_P, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MP), ?(am_next_mam MP); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_P, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MP); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MP); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact ok_P' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1Sf4A3S1S8dS5R2Sf5A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeR2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1S100A3S1S8dS5R2Sf6A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeR2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S5S8dS5R1SfaA3S1S8dS5R2Sf7A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;SeeR2A11S10eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1M0A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3A3S92SdVm0;A1A1A3G1A3G1A3S31S5bS31S5bG0G1A3G0A3A3A3S4S5S5S1S8dS5R1Sf4A3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M2A3S61VL;R3A2M3A2S6cG3S3bS68S68G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pP with (mptr MP) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MP)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MP l Hl) as R_; exists (OD_meta MP (v 161) (v (vptr MA_)) (v (vmem MP)) (v (vavail MP)) (v (vfreed MP)) (v (vbits MP))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1M0A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3A3S92SdVm0;A1A1A3G1A3G1A3S31S5bS31S5bG0S30S5bS5dS6bS62S6dVsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S8dS5R1SfaA3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M2A3S61VL;R3A2M3A2S6cG3S3bS68S68G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pP with (mptr MP) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MP)) (v (vptr MB)) (v (vmem MA_)) e_avT (e_freedT MA_) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MP l Hl) as R_; exists (OD_meta MP (v 161) (v (vptr MA_)) (v (vmem MP)) (v (vavail MP)) (v (vfreed MP)) (v (vbits MP))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D5nh : ltac2:(tb__ "0|0|
VTR;Z0S144S95VK;SadVrhoW;A4S110VX;VU;S124Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D5nh)).
  { apply (seg_run 300 SA_D5nh LA_D5nh _ rhoW eq_refl eq_refl runA_D5nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D5nh _ SA_D5nh LfA LA_D5nh_shape HinA) in HSPA. change (lfs LA_D5nh 0 SA_D5nh) with LA_D5nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D5nhs ST_D5nh (e_maskA MA_) (snd DT_D5nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D5nh LT_D5nh _ rhoA ST_len ST_next runT_D5nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MA_)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D5nh _ _ _ ST_D5nh Lf LT_D5nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nh 0 ST_D5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nh 0 ST_D5nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nh 1 ST_D5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nh 1 ST_D5nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nh 2 ST_D5nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nh 2 ST_D5nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final am1_A)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD5nh.
End Mal_aslot_VD5nh.

Module Mal_aslot_VD4sr.

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

Section VD4sr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;S3aS38S74S68A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S6aZ0Vreq;A2S6aS6bVreq;S80A2S83Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S32S74A1S60Vs;Vsc;A2S33S74Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S65S64VX;Vs;Vsc;A3S33S74Vm0;A2S30S74Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§21§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§21§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§21§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§21§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§21§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§21§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§21§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls4 := (@U.Mal_aslot__G1.Mal_aslot_I.cls4 s X sc Hsc m0 rest Rg).
Local Notation "§22§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§22§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§22§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S148S125VX;S3aS38S74S68A2A1VU;S124Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S6aZ0M0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S6cG1Z100A2A2S1S0S68S6fG1Z20A2S7bSfVs;Vm0;R1A3M2A1A3S2S0S68S81G2A1G0A3A1S0S68S22VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bSfVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§23§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§23§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§24§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§24§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§24§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§24§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§25§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§25§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§25§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§25§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§25§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§25§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§24§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S6aZ1000S9bQ40S47Vrho;PaA2A2M0A2S0S68S6fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S6aS12aZ40S9bQ40S47Vrho;PfA2A2A2M0S70S147Z0A1A1A2S6aS70S72Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6aS129VL;A1S6bS9bQ40M0S47Vrho;PaA2A2S12aZ40S9bG0S47Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§26§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§26§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§27§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§27§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§25§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§27§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§27§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§27§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§27§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;Vrd0;Sb9S95VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S9aQ40A1S37F_;Vwok0;SbaS95VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z60A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ecR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z20A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ccR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS2bVL;S82SfVs;Vm0;R1A3A1A2Z8A2A2A3S33G1S9cG0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS6bZ5a3d0Z369A2Vsc;A2A2A3S33G1S9cG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S127S126Vrd0;S9aQ40A1S35L_;A2S128S125A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S126Sb9S95VmW;A2SbaS95VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§28§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§28§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§21§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§29§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§29§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§25§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§25§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§25§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S0S68Vbnc;S84S6dVsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§30§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§30§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§24§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S149S95VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S34Sb5A1Sb6OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§31§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§31§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§32§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§32§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§33§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§33§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§34§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§34§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§21§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Abbreviation maskA_range := (@U.Mal_aslot__G3.Mal_aslot_T.maskA_range s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp).
Local Abbreviation ze_maskA := (§27§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§27§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§35§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§35§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§36§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§36§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§37§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§37§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§38§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§38§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§38§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§35§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§32§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§39§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§39§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§39§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§39§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§22§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§22§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§22§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§23§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;VmW;S50Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Sb7Vvm;Sb8Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S34Sb5A1M0Sb6VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Sb6R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4bS95Vrho;S146S145A1S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 4%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S68S7cSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S68S7dSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S0S68S7dSfVs;Vm0;S7A3M0A1S87S85G0A1A1A3").
Hypothesis HVact : maskA MB = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S68Vmaskv;SbcVs;Vm0;SeA3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;SdVm0;A1A2S33S73S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls4 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls4 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MC).
Definition xn : mslot := (MUsed (mam MA_)).
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|1|
S7eS33S74S1aVs;Vm0;A2A2S89SfVs;Vm0;S7A3M0A1G0A3").
Definition am1_C : ameta := ltac2:(tb__ "0|1|
S7eS8aSfVs;Vm0;SeA3M0A1S33S74S9Vs;Vm0;A2A2G0A3").
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S1aVs;Vm0;A2S9Vs;Vm0;A2SdcSe3A8").
Definition s2V : astate := ltac2:(tb__ "0|0|
S94Vsc;S33S74S20Vs;Vm0;A2A2S12eVs;Vsc;SdVm0;A1Vam0;S1aVs;Vm0;A2S9Vs;Vm0;A2SdcSe3A8A3").
Definition s3V : astate := ltac2:(tb__ "0|1|
S94Vsc;S33S74S1aVs;Vm0;A2M0A2S94Vsc;S33S74S20Vs;Vm0;A2A2S12eVs;Vsc;SdVm0;A1Vam0;G0S9Vs;Vm0;A2SdcSe3A8A3A3").
Lemma HXp : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;S1aVs;Vm0;A2A2S33S73SdcA2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MC))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S32S73A1S5cS12fVs;S1aVs;Vm0;A2S9Vs;Vm0;A2M0SdcA4G0A2S33S73Se3A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|0|
S0S34S74A1S5fS12fVs;S1aVs;Vm0;A2S9Vs;Vm0;A2SdcA4A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MC). Qed.
Lemma K1b : ltac2:(tb__ "0|0|
S0S34S74A1S5fS138Vs;S1aVs;Vm0;A2S9Vs;Vm0;A2SdcSe3A5A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S34S74A1S5fSd9A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd9S19Vs;Vm0;S6A3A2S33S73S76SeaA1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd9S19Vs;Vm0;S7A3A2S33S73S76Se4A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_C : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd9S19Vs;Vm0;SeA3A2S33S73S76SdbA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_C, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MC)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd9S19Vs;Vm0;SaA3A2S33S73S76Se5A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1V, am1_B, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S32S73A1S5cSdaVq;A2S5cSd9Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S34S68A1S77SdaA1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S32S74A1S60SdaVsc;A2S33S74S1aVs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S38S32S74A1M0S75A2M1A2S134Vsc;SdVm0;A1Vam0;Vs;A4S78S75G1S39G0S75S33S74S9Vs;Vm0;A2A2Sd9A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pC pA xp xn).
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
S0S74S9Vs;Vm0;A2S19Vs;Vm0;S7A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd9S9Vs;Vm0;A2A2S33S73S76Se4A1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0S79S75S38S74S75A2M0A2S135Vsc;S9Vs;Vm0;A2Se4Sd9A4S78S75G0S39S74S75S20Vs;Vm0;A2Se2A4A3A3").
Proof using HI HVskip Hhd Hsc. drop_sp. unfold s2V. apply (step2_skip s1V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_last am_set_links]; exact HVskip | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link]]. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSe2S20Vs;Vm0;A2A2S33S73S76Se5A1A2A3"). Proof using HI Hhd Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_B. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S79S75S38S74S75A2M0A2S136Vsc;S20Vs;Vm0;A2Se5Se2A4S78S75G0S39S74S75S1aVs;Vm0;A2SdaA4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pB am1_B pC); [unfold am1_B; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_B; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MB); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSdaS1aVs;Vm0;A2A2S33S73S76SdbA1A2A3"). Proof using Hr Hsc Rg. rewrite MT3. exact MT1_C. Qed.
Lemma Hav3 : am_avail am1_C = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_C. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S68S137SdbA1SbcVs;Vm0;SeA3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MC <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S133SdaS1aVs;Vm0;A2SdbA3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75S7aSbcVs;Vm0;SeA3A1Sd8A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pB s2V am1_B pC s3V am1_C S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S68S7aSbcVs;Vm0;SeA3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MC). pose proof (lowbit_range (maskA MC) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S13aVX;VU;Vs;Vsc;S7aSbcVs;Vm0;SeA3A1Sd8A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S32S74A1S60Sd8Vsc;A2S33S74S1aVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pC am1_C). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd8S1aVs;Vm0;A2A2S33S73S76S130SdbA1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MC)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S68S86SdbA1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_C. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MC))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd8S19Vs;Vm0;S6A3A2S33S73S76SeaA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd8S19Vs;Vm0;S7A3A2S33S73S76Se4A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_B : ltac2:(tb__ "0|0|
S0S32S73A1S5cSd8S19Vs;Vm0;SaA3A2S33S73S76Se5A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pC am1_C); [rewrite MT3; exact MT1_B | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
S93Vs;Sd9S31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3S92SdVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pC pA xp xn))); [apply (delta_trans _ (s1b s pC pA xp xn)); [apply (delta_trans _ (s1a s pC pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pC (mam MC)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
S93Sd9Se2S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s2V. apply delta_sh. lia. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S93Se2SdaS30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
S93Vs;SdaS31S5bS31S5bS31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3M0A3S92SdVm0;A1A1A3G0A3G0A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|4|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1M0A1S30S5S8S6S67ScSeA1A1M1S67ScS7A1A1M2S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7G0S67ScSaA1A1M3S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7S30S5S8SeG3G0S67S11SeA1A1S67S13SeA1A1S67S14SeA1A1S67S10SeA1A1A7S30S5S18SeS67S28SeA1A1A2S30S5S8SaG2G1S67S11SaA1A1S67S13SaA1A1S67S14SaA1A1S67S10SaA1A1A7S30S5S18SaS67S28SaA1A1A2S30S5S1eS30S5S1bS30S5S17SeS67PaaA1A2S36S5A1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49SacA1S30S41S21Sc1S5S41S1fSddA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D4sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MC); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46SacA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D4sr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MC)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MC))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MC))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MC)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S51Z2126cS99S96S4eS3aS44A1S30S41S21S36S41A1A3S46SacA1SabS3eA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4bS95VrhoW;SecS39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4M0A4S4bS95VrhoW;SacG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D4sr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S32S38S34S38S44S44A2M0A1M1S34S42A1M2A2M3A1S14aSb2Sa5A2S33G3S39G1G2S30G0S39S44S44Sc0SeA1S40PabA1A4S36G0A1A3S3bG1G2SafA3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D4sr)). Qed.
Lemma swf_ST : swf ST_D4sr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S37S8eS42S42S91S42S56R1A1S46Sa5A1A3Lp;S3bS34S38S44S44A2A1S34S42A1SafA3A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S37S8eS42S103SedA1S46Sa5A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S37S8eS42S12cS46Sa5A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46Sa5A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D4sr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MC)) (SLit 0)); SPUle (v (vbyte MC)) (SLit 255); SPAlign (vptr MC) 3; SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MC)) (v (vptr MB))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MC)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D4sr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S69S57Sa5A1SabA3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D4sr 0 ST_D4sr.
Definition LT1 : sstate := lfs LT_D4sr 1 ST_D4sr.
Definition LT2 : sstate := lfs LT_D4sr 2 ST_D4sr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Se9A1A2SdfA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Se7A1A2Se0A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Se8A1A2Se1A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSdfA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSe0A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSe1A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSdfA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSe0A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSe1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSddSdfA2SdeA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSddSe0A2SebA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSddSe1A2Se6A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|3|
S0S34S5A1SdeS30S5S16S67ScSeA1A1M0A1S30S5S8S6S43Z0A1M1G1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7G0S67ScSaA1A1M2S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7S30S5S8SeG2S67ScS7A1A1S67S11SeA1A1SbdSbfSeA1S67S10SeA1A1A7S36S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S34S5A1Se6S31S5SdeS30S5S17SeSbeA2S36S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S3fS3dS5VdsF;A2S3dS5SddA2A3S5S8dS5R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S8dS5R2SbbSddVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S34S5A1M0G0S5S8dS5R1SbbR3R2A2A3S8dS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sa3Vk;U3A2S0S34S41A1S49Sa4Sa8Vk;Sa5A3A1M0S30S41S111S52S90S41S21G0A3A1A1S8fS41G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S68S58Sa4Sa8Vk;Sa5A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S34S44A1S55Sa4Sa8Vk;Sa5A3A1S96A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S53S54Sa4Sa8Vk;Sa5A3A1S4eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S32S44A1S59Sa4Sa8Vk;Sa5A3A1S3aS44A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S44S4fSa4Sa8Vk;Sa5A3ZaA2S29S67PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S68S1S6aZ1R1A2S6aR1Z1fA2A2S0S37S97S71R2A1A1S35A3S0S44S4fSa4Sa8Vk;Sa5A3R3A2S98S71R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D4sr k ST_D4sr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S8dS42S4aSa0S43Z1fA1S23SeA1A3S46Se9A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S8dS42S4aSa1S67PaaA1S43Z0A1A3S46Se7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23SeA1A3A1S46Se7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa1S67PaaA1S43Z0A1A3A1S46Se8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23SeA1A3A1S46Se8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S0S75S132SdaS1aVs;Vm0;A2M1SdbA3S131SdaG1SdbA3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pC am1_C (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S93Vs;Sd8S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1M1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M2A3M3A3S92SdVm0;A1A1A3G3A3G3A3S31S5bS31S5bG1G2A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pC am1_C ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S93Vs;Sd8S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1M1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M2A3M3A3S92SdVm0;A1A1A3G3A3G3A3S31S5bS31S5bG1S30S5bS5dS6bS62S6dVsc;G0A2A2A1G2A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pC am1_C ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S0S34S68A1S77Sd8A1S88S6dVsc;G0A2S6dVbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pC am1_C (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8S8SeS67ScSaA1A1S67ScS7A1A1S67S11SeA1A1SbdSbfSeA1S67S10SeA1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_C). split; [exact MT_R'|].
  pose proof (am_final_fields am1_C) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MB); unfold am1_C, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold am1_C, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MC), ?(am_next_mam MC); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_C; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_C; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_C, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_act' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8S16S67ScSeA1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MC). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8S17SeSbeA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8S8S6S43Z0A1M0G0S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7A11").
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
Lemma ok_A' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8S8S7S67ScSeA1A1S67ScSaA1A1S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_A. split; [exact MTF_A|].
  split; [rewrite (ze_ptr MC); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_A, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact ok_A' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1SdeA3S1S8dS5R2SdfA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1SebA3S1S8dS5R2Se0A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S5S8dS5R1Se6A3S1S8dS5R2Se1A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd8R2A11S10eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1M0S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3M2A3S92SdVm0;A1A1A3G2A3G2A3S31S5bS31S5bG0G1A3G0A3A3A3S4S5S5S1S8dS5R1SdeA3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M3A3S61VL;R3A2M4A2S6cG4S3bS68S68G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MC)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v (vptr MA_)) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S1aVs;Vm0;A2A1M0S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3M2A3S92SdVm0;A1A1A3G2A3G2A3S31S5bS31S5bG0S30S5bS5dS6bS62S6dVsc;Z7A2A2A1G1A3A3G0A3A3A3S4S5S5S1S8dS5R1Se6A3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M3A3S61VL;R3A2M4A2S6cG4S3bS68S68G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pC with (mptr MC) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MC)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MC l Hl) as R_; exists (OD_meta MC (v (vptr MB)) (v (vptr MA_)) (v (vmem MC)) e_avT (e_freedT MC) (v (vbits MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MC e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MC))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D4sr : ltac2:(tb__ "0|0|
VTR;Z0S144S95VK;SacVrhoW;A4S110VX;VU;S124Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D4sr)).
  { apply (seg_run 300 SA_D4sr LA_D4sr _ rhoW eq_refl eq_refl runA_D4sr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D4sr _ SA_D4sr LfA LA_D4sr_shape HinA) in HSPA. change (lfs LA_D4sr 0 SA_D4sr) with LA_D4srs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D4srs ST_D4sr (e_maskA MC) (snd DT_D4sr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D4sr LT_D4sr _ rhoA ST_len ST_next runT_D4sr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MC)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D4sr _ _ _ ST_D4sr Lf LT_D4sr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MC rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D4sr 0 ST_D4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D4sr 0 ST_D4sr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D4sr 1 ST_D4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D4sr 1 ST_D4sr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MC rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D4sr 2 ST_D4sr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D4sr 2 ST_D4sr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pC (am_final am1_C)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD4sr.
End Mal_aslot_VD4sr.

Module Mal_aslot_VH.

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

Lemma single_leaf (l : list leaf) pcr d Lf : ltac2:(tb__ "0|1|
S0S34S38S68S14dA2M0A1Sc1S14bG0S151Vl;A4S30G0Vpcr;S36G0A1A3A3S8dS14bVLf;Vl;A3S0S5aS14cVLf;A1S105Vl;U0Vd;A3A3F_;F_;").
Proof.
  intros E Hin. destruct l as [|L0 [|L1 t]]; cbn in E; try discriminate.
  destruct Hin as [<-|[]]. reflexivity.
Qed.

Lemma ctz32_lowbit m : ltac2:(tb__ "0|0|
S6cZ0Vm;A2S0S68S8bS7aVm;A1A1S8bVm;A1A3F_;").
Proof.
  intros Hm. destruct (lowbit_spec m Hm) as (k & Hk & Hl & _). unfold ctz32. rewrite Hl.
  f_equal. destruct (lowbit_spec (bit k) ltac:(unfold bit; apply Z.pow_pos_nonneg; lia)) as (k' & Hk' & Hl' & Hb' & _).
  rewrite Hl'. rewrite testbit_bit in Hb' by lia. apply Z.eqb_eq in Hb'. subst k'. reflexivity.
Qed.

Section VH.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;S3aS38S74S68A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S6aZ0Vreq;A2S6aS6bVreq;S80A2S83Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S32S74A1S60Vs;Vsc;A2S33S74Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S65S64VX;Vs;Vsc;A3S33S74Vm0;A2S30S74Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Abbreviation mptr := (@U.Mal_aslot__G1.Mal_aslot_I.mptr s m0).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (@U.Mal_aslot__G1.Mal_aslot_I.mam s m0).
Local Notation "§40§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§40§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mnext_used := (§40§ U.Mal_aslot__G1.Mal_aslot_I.mnext_used).
Local Abbreviation mprev_used := (§40§ U.Mal_aslot__G1.Mal_aslot_I.mprev_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S148S125VX;S3aS38S74S68A2A1VU;S124Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S6aZ0M0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S6cG1Z100A2A2S1S0S68S6fG1Z20A2S7bSfVs;Vm0;R1A3M2A1A3S2S0S68S81G2A1G0A3A1S0S68S22VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bSfVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Abbreviation mem_R := (@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Notation "§41§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§41§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§41§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§41§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_aluw := (§41§ U.Mal_aslot__G1.Mal_aslot_I.ze_aluw).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Notation "§42§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§42§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§42§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_freed := (§42§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§42§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation e_sx := (@U.Mal_aslot__G1.Mal_aslot_I.e_sx).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation ze_sx_avail := (§42§ U.Mal_aslot__G1.Mal_aslot_I.ze_sx_avail).
Local Abbreviation ze_lowbit_sx := (@U.Mal_aslot__G1.Mal_aslot_I.ze_lowbit_sx s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S6aZ1000S9bQ40S47Vrho;PaA2A2M0A2S0S68S6fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S6aS12aZ40S9bQ40S47Vrho;PfA2A2A2M0S70S147Z0A1A1A2S6aS70S72Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6aS129VL;A1S6bS9bQ40M0S47Vrho;PaA2A2S12aZ40S9bG0S47Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Abbreviation ZF_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.ZF_base5 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high).
Local Abbreviation zf_ptr_ne0 := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_hit := (§42§ U.Mal_aslot__G1.Mal_aslot_I.zf_hit).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;Vrd0;Sb9S95VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S9aQ40A1S37F_;Vwok0;SbaS95VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z60A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ecR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z20A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ccR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS2bVL;S82SfVs;Vm0;R1A3A1A2Z8A2A2A3S33G1S9cG0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS6bZ5a3d0Z369A2Vsc;A2A2A3S33G1S9cG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S127S126Vrd0;S9aQ40A1S35L_;A2S128S125A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S126Sb9S95VmW;A2SbaS95VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§43§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§43§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (@U.Mal_aslot__G1.Mal_aslot_I.od_pairwise s m0).
Local Abbreviation sp0 := (@U.Mal_aslot__G1.Mal_aslot_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_aslot__G1.Mal_aslot_I.D0 rho).
Local Notation "§44§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§44§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§42§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§42§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S0S68Vbnc;S84S6dVsc;G0A2S77Vs;A1A2A3F_;").
Local Abbreviation od_ok_got := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§41§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S149S95VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S34Sb5A1Sb6OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Abbreviation seg_run := (@U.Mal_aslot__G2.Mal_aslot_W.seg_run s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§45§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§45§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;VmW;S50Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Sb7Vvm;Sb8Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S34Sb5A1M0Sb6VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Sb6R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4bS95Vrho;S146S145A1S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PdA2A2Vreq;A3").

Lemma Hfr_pre : ltac2:(tb__ "0|1|
S9aQ40M0A1S6cS9bG0R1A2S6bS2fVrho;A1S2dVrho;A1A2A2S0S32S9aQ8A1A1S14eVms;R2A2S50Vrho;R2A2A3F_;Fa;").
Proof using Hbnc Hgd Hsc Hsm_pre. drop_sp.
  intros a Ha. pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr.
  apply Hfr. cbn [ss_objs Pre_as]. constructor; [|constructor].
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval fst snd]. unfold soff. cbn [eval].
  rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH. unfold U.Mal_aslot__G1.Mal_aslot_I.sp0, U.Mal_aslot__G1.Mal_aslot_I.D0 in Ha. lia.
Qed.

Lemma ND : List.NoDup (keys s). Proof using HI. exact (proj1 (inv_keys HI)). Qed.

Lemma xraw_upd_meta q x : ltac2:(tb__ "0|0|
S0S37S66Vq;VX;A2S3eA3S150VX;S14fVq;Vx;Vs;A3A2F_;").
Proof using HXr. drop_sp.
  intros Hq p Hp. rewrite MT_upd_other; [exact (HXr p Hp)|]. intros ->.
  unfold memb in Hq. assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hp | apply sptr_eqb_refl]).
  rewrite E in Hq. discriminate.
Qed.

Lemma ta_post_of f s' : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75Vf;Vs';A4A3A3S2S0S68Vf;Z0A3A1S13aVX;VU;Vs;Vsc;Vf;Vs';A6F_;F_;").
Proof using HI Hsc. drop_sp.
  intros E Hf.
  pose proof (try_avail_spec X U s sc (fun r => fst r <> 0 -> ta_post X U s sc (fst r) (snd r)) HI Hsc
                ltac:(intros s1 _ _ _ _ H; exfalso; exact (H eq_refl)) ltac:(intros f1 s1 H _; exact H)) as T.
  rewrite E in T. cbn [itok fst snd] in T. exact (T Hf).
Qed.

Hypothesis HVh : ltac2:(tb__ "0|0|
S2S0S68S7cSfVs;Vm0;S6A3A1Z0A3A1").

Definition E_avH : sv := ltac2:(tb__ "0|1|
S45S9dS2cS67S13S6A1A1A1M0S2eG0A1A3").
Definition dsH : list od := ltac2:(tb__ "0|0|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1A1S30S5S8S6S67ScSbA1A1S67ScS7A1A1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S1eS30S5S1bS36S5A1A3A3A3A3A3A3").
Definition dsHF : list od := ltac2:(tb__ "0|0|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1A1S30S5S8S6S67ScSbA1A1S67ScS7A1A1S67S11S6A1A1S13dS67S14S6A1A1S67S10S6A1A1A7S30S5S1eS30S5S1bS36S5A1A3A3A3A3A3A3").
Definition dsHC : list od := ltac2:(tb__ "0|0|
S30S5S8S6S67ScSbA1A1S67ScS7A1A1S67S11S6A1A1S13dS67S14S6A1A1S67S10S6A1A1A7S36S5A1A3").
Definition stkH : list cell := ltac2:(tb__ "0|0|
S52S90S41S21S49S107A1A3A1").
Definition objsH : list sobj := tl (ss_objs LA_Hs).

Lemma SA_H_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49S108A1S30S41S21Sc1S5S41S1fS142A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma LA_H_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49S107A1S30S41S111S143A1S140A3A3"). Proof using . reflexivity. Qed.
Lemma LA_H_match : ltac2:(tb__ "0|0|
S0S37S10dS140S13cA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsHF_vars : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fS13cA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsHF_sem : ltac2:(tb__ "0|0|
S0S37S8eS5S10fS13cA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LA_H_pc : ss_pc LA_Hs = 0x21b08. Proof using . reflexivity. Qed.
Lemma LA_H_fregs : ltac2:(tb__ "0|0|
S0S34S44A1S55S107A1S96A3"). Proof using . reflexivity. Qed.
Lemma LA_H_fcsr : ltac2:(tb__ "0|0|
S0S53S54S107A1S4eA3"). Proof using . reflexivity. Qed.
Lemma LA_H_resv : ss_resv LA_Hs = None. Proof using . reflexivity. Qed.
Lemma LA_H_cs : ltac2:(tb__ "0|0|
S68S1S6aZ1R1A2S6aR1Z1fA2A2S0S37S97S71R2A1A1S35A3S0S44S4fS107R3A2S98S71R3A1A1A3F_;F_;Fz;").
Proof using Hbnc Hgd Hsc rho. drop_sp.
  intros z Hz Hcs.
  pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LA_Hs z) (pre_reg (Z.to_nat z)))%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
Qed.
Lemma LA_H_a0 : ltac2:(tb__ "0|0|
S0S44S4fS107ZaA2S29S2cS67S13S6A1A1A1A1A3"). Proof using . reflexivity. Qed.
Lemma swf_SA_H : swf SA_H = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SA_H_facts_sup : ltac2:(tb__ "0|0|
S0S37S8eS42S12cS46S108A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okH : Forall od_ok dsH.
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  unfold dsH. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got. - apply od_ok_guard. - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [exact (ze_ptr MP) | exact (ze_ptr MA_)].
  - apply od_ok_sct. - apply od_ok_ctz.
Qed.
Lemma pwH : od_pairwise dsH.
Proof using . drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; exact I|]); apply Forall_nil. Qed.
Lemma ZF_H : ltac2:(tb__ "0|0|
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46S108A1A3").
Proof using HI HMI HVh Hbnc Hbytes Hdepth Hgd Hhd Hsc Hsp Hsp_high.
  change (ss_facts SA_H) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0))] ++
     [SPNot (SPBranch BC_EQ (e_sx (v (vavail MM0))) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (e_sx (v (vavail MM0)))) (SLit 0)); SPUle (e_dbidx (e_sx (v (vavail MM0)))) (SLit 31)]).
  apply Forall_app. split; [apply ZF_base5|]. apply Forall_app. split; [repeat constructor; apply zf_ptr_ne0|]. apply zf_hit. exact HVh.
Qed.

Definition S0H : sstate := ltac2:(tb__ "0|0|
S51Z2126cS99S96S4eS3aS44A1S30S41S21S36S41A1A3S46S108A1S10aS3eA9").

Lemma carve_H : ltac2:(tb__ "0|1|
S4bS95VrhoW;S141S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4M0A4S4bS95VrhoW;S108G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hreq Hrom Hsc Hsp Hsp_high Hspanv.
  intros Hsm. change SA_H with (mkSS (ss_pc S0H) (ss_regs S0H) (ss_fregs S0H) (ss_fcsr S0H) (ss_resv S0H) (ss_objs S0H ++ map obj_of dsH) (ss_facts S0H) NXA (ss_lenient S0H)).
  apply (carve S0H dsH NXA tr md eq_refl okH pwH swf_SA_H Hsm).
Qed.

Definition amH' : ameta := ltac2:(tb__ "0|2|
S8cS6dS7cSfVs;Vm0;S6A3M0A1M1S7aG1A1A2G0A2").
Definition sH' : astate := ltac2:(tb__ "0|0|
S139Vs;Vm0;SfVs;Vm0;S6A3A3").
Lemma HM0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;Vm0;A2S33S73S76SfVs;Vm0;S6A3A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Lemma taH : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75S7aS7cSfVs;Vm0;S6A3A1A1S13bA4A3A3").
Proof using HI HVh Hhd Hsc. drop_sp. exact (ta_hit s sc m0 (mam MM0) Hhd HM0 HVh). Qed.
Lemma avail0_range : ltac2:(tb__ "0|1|
S1S6cZ0S7cSfVs;Vm0;S6A3A1M0A2S6cG0S72Z2Z20A2A2A2"). Proof using HI HMI HVh Hbnc Hgd Hhd Hsc rho. pose proof (mem_R MM0) as (R1 & _). lia. Qed.
Lemma postH : ltac2:(tb__ "0|0|
S13aVX;VU;Vs;Vsc;S7aS7cSfVs;Vm0;S6A3A1A1S13bA6").
Proof using HI HMI HVh Hbnc Hgd Hhd Hsc rho. drop_sp. apply (ta_post_of _ _ taH). pose proof (lowbit_range _ avail0_range). lia. Qed.
Lemma MT_H' : ltac2:(tb__ "0|0|
S0S32S73A1S5cS13bVm0;A2S33S73S76S13fA1A2A3"). Proof using . unfold sH', hit_post. apply MT_upd_same. Qed.
Lemma hd_H' : ltac2:(tb__ "0|0|
S0S32S74A1S60S13bVsc;A2S33S74Vm0;A2A3"). Proof using Hhd. unfold sH', hit_post. rewrite active_hd_upd_meta. exact Hhd. Qed.
Lemma xraw_H' : xraw X sH'. Proof using HI HXr Hhd Hsc. unfold sH', hit_post. apply xraw_upd_meta. exact (proj2 (usedX_MT _ _ _ _ (proj1 (mam_used MM0)))). Qed.
Lemma delta_H : ltac2:(tb__ "0|0|
S93Vs;S13bS92Vm0;A1A3"). Proof using HI Hhd Hsc. exact (delta_hit s ND m0 (mam MM0) HM0). Qed.

Lemma ze_avH : ltac2:(tb__ "0|0|
S0S68S6fS12dS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS13dA3S72Z2Z20A2A2S7cS13fA1A3").
Proof using HI HMI HVh Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold E_avH. rewrite ze_aluw, ze_sx_avail, (ze_lowbit_sx _ _ (ze_sx_avail MM0) avail0_range). cbn [zalu am_avail amH' am_set_avail].
  pose proof avail0_range as R. pose proof (lowbit_range _ R) as LR.
  rewrite (ZBits.sx32_mod32 (am_avail (mam MM0))) by lia. rewrite (ZBits.sx32_mod32 (lowbit (am_avail (mam MM0)))) by lia.
  rewrite (Z.mod_small (am_avail (mam MM0) - lowbit (am_avail (mam MM0)))) by lia. rewrite ZBits.sx32_mod32 by lia. reflexivity.
Qed.

Lemma okH' : ltac2:(tb__ "0|0|
S5S8dS5R1S13eA3S1S8dS5R2S13cA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S13bR2A11S10eVsc;R2A2A2A2F_;Fd;").
Proof using HI HMI HVh Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros d [<-|[]]. split; [cbn; tauto|]. split; [|exact I].
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists amH'. split; [exact MT_H'|].
  destruct (mprev_used MM0) as (p & Hp & Ep). destruct (mnext_used MM0) as (n & Hn & En).
  cbn [amH' am_set_avail am_prev am_next am_mem am_freed am_last am_sc am_maplen]. rewrite Hp, Hn. cbn [optrZ].
  rewrite (ze_ptr MP), (ze_ptr MA_), ze_mem, ze_freed, ze_bits, ze_avH.
  pose proof (mem_R MM0) as R.
  repeat split; try reflexivity.
  all: try (cbn [mptr]; rewrite <- Ep; reflexivity).
  all: try (cbn [mptr]; rewrite <- En; reflexivity).
  all: try (apply Z.mod_small; lia).
  all: unfold meta_bits; reflexivity.
Qed.

Lemma entH : ltac2:(tb__ "0|0|
S5S8dS5R1S13cA3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S8dS5R2S13eA3A2F_;Fd;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc. drop_sp.
  intros d Hd. cbn in Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try (left; first [apply od_ok_got | apply od_ok_guard | apply od_ok_act_entry | apply od_ok_sct | apply od_ok_ctz]).
  right. left. reflexivity.
Qed.

Lemma locsH : ltac2:(tb__ "0|2|
S5bS8dS5bR1S92Vm0;A1A3S4S5S5S1S8dS5R1S13eA3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M0A3S61VL;R3A2M1A2S6cG1S3bS68S68G0A3A2A2A2Ld;A2F_;Fl;").
Proof using HVh Hbnc Hbytes Hbytes_rd Hgd Hhd Hsc Rg maskv req rho spanv. drop_sp.
  intros l Hl. exists (OD_meta MM0 (v (vptr MP)) (v (vptr MA_)) (v (vmem MM0)) E_avH (v (vfreed MM0)) (v (vbits MM0))). split; [left; reflexivity|].
  cbn [od_range fst snd mptr]. unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
  assert (AG : forall dd, loc_addr L (LMem (padd m0 dd)) = zA (U.Mal_aslot__G1.Mal_aslot_I.pM0 m0) + dd) by (intros dd; unfold zA, U.Mal_aslot__G1.Mal_aslot_I.pM0, addr_of, loc_addr; destruct m0; cbn [padd]; lia).
  destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AG; lia.
Qed.

Theorem variant_H : ltac2:(tb__ "0|0|
VTR;Z0S144S95VK;S108VrhoW;A4S110VX;VU;S124Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVh HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg.
  apply (seg_run 300 SA_H LA_H _ rhoW eq_refl eq_refl runA_H (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  rewrite (single_leaf LA_H _ SA_H Lf LA_H_shape Hin) in HsmF. change (lfs LA_H 0 SA_H) with LA_Hs in HsmF.
  pose proof postH as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hd_H' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_H' in MU. injection MU as <-.
  pose proof avail0_range as AR.
  destruct (ze_ctz (e_sx (v (vavail MM0))) (am_avail (mam MM0)) (ze_sx_avail MM0) AR) as [EC RC].
  assert (EI : bv_unsigned (eval rhoF (reg_sv LA_Hs 10)) = ctz32 (am_avail (mam MM0))).
  { rewrite LA_H_a0. rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
  rewrite ctz32_lowbit in HI', Hidx' by lia.
  eapply (post_okH tr md msF rhoF EmW Evm HagF LA_Hs stkH objsH dsHF dsHC LA_H_objs LA_H_match HsmF dsHF_vars dsHF_sem entH
            (fun d Hd Hok => od_hold d Hok) sH' _ (meta_locs m0) HI' xraw_H' delta_H okH' locsH
            LA_H_pc LA_H_cs LA_H_fregs LA_H_fcsr LA_H_resv Hsm_pre ltac:(rewrite EI; lia) HKc' Hsc_rho Hreq_rho m0 amH').
  - rewrite EI. reflexivity.
  - exact hd_H'.
  - exact Hu'.
  - exact Hsc'.
  - pose proof Hreq. lia.
  - rewrite EI. exact Hidx'.
  - intros c Hc. apply Hheads'; lia.
  - exact Hub'.
  - exact taH.
  - exact avail0_range.
  - exact EI.
Qed.

End VH.
End Mal_aslot_VH.

Module Mal_aslot_VD5nr.

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

Section VD5nr.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;S3aS38S74S68A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S6aZ0Vreq;A2S6aS6bVreq;S80A2S83Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S32S74A1S60Vs;Vsc;A2S33S74Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S65S64VX;Vs;Vsc;A3S33S74Vm0;A2S30S74Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§46§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§46§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§46§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§46§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§46§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§46§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§46§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls5 := (@U.Mal_aslot__G1.Mal_aslot_I.cls5 s X sc Hsc m0 rest Rg).
Local Notation "§47§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§47§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§47§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S148S125VX;S3aS38S74S68A2A1VU;S124Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S6aZ0M0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S6cG1Z100A2A2S1S0S68S6fG1Z20A2S7bSfVs;Vm0;R1A3M2A1A3S2S0S68S81G2A1G0A3A1S0S68S22VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bSfVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§48§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§48§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§49§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§49§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§49§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§49§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§49§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§50§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§50§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§50§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§50§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§50§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§50§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§49§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Notation "§51§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze161 := (§51§ U.Mal_aslot__G1.Mal_aslot_I.ze161).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S6aZ1000S9bQ40S47Vrho;PaA2A2M0A2S0S68S6fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S6aS12aZ40S9bQ40S47Vrho;PfA2A2A2M0S70S147Z0A1A1A2S6aS70S72Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6aS129VL;A1S6bS9bQ40M0S47Vrho;PaA2A2S12aZ40S9bG0S47Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§52§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§52§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§53§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§53§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§50§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§53§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§53§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§53§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§53§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;Vrd0;Sb9S95VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S9aQ40A1S37F_;Vwok0;SbaS95VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z60A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ecR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z20A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ccR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS2bVL;S82SfVs;Vm0;R1A3A1A2Z8A2A2A3S33G1S9cG0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS6bZ5a3d0Z369A2Vsc;A2A2A3S33G1S9cG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S127S126Vrd0;S9aQ40A1S35L_;A2S128S125A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S126Sb9S95VmW;A2SbaS95VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§54§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§54§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§46§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§55§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§55§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§56§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§56§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§50§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§50§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§50§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S0S68Vbnc;S84S6dVsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§57§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§57§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§49§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S149S95VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S34Sb5A1Sb6OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§58§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§58§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§59§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§59§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§60§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§60§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§61§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§61§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§46§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§62§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§62§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§53§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§53§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§63§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§63§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§64§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§64§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§65§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§65§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§66§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§66§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§67§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§67§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§67§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§63§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§59§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§68§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§68§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§68§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§68§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§47§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§47§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§47§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§48§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;VmW;S50Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Sb7Vvm;Sb8Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S34Sb5A1M0Sb6VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Sb6R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4bS95Vrho;S146S145A1S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 5%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S68S7cSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S68S7dSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S68S7dSfVs;Vm0;S7A3M0A1S87S85G0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S68Vmaskv;SbcVs;Vm0;SaA3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;SdVm0;A1A2S33S73S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls5 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls5 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MP).
Definition xn : mslot := (MUsed (mam MA_)).
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|1|
S7eS33S74S15Vs;Vm0;A2A2S89SfVs;Vm0;S7A3M0A1G0A3").
Definition am1_P : ameta := ltac2:(tb__ "0|1|
S7eS8aSfVs;Vm0;SbA3M0A1S33S74S9Vs;Vm0;A2A2G0A3").
Definition am1_B : ameta := (mam MB).
Definition s1V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sc7ScfA8").
Definition s2V : astate := ltac2:(tb__ "0|0|
S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sc7ScfA8").
Definition s3V : astate := ltac2:(tb__ "0|0|
S94Vsc;S33S74S20Vs;Vm0;A2A2S12eVs;Vsc;SdVm0;A1Vam0;S15Vs;Vm0;A2S9Vs;Vm0;A2Sc7ScfA8A3").
Lemma HXp : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;S15Vs;Vm0;A2A2S33S73Sc7A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MP))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S32S73A1S5cS12fVs;S15Vs;Vm0;A2S9Vs;Vm0;A2M0Sc7A4G0A2S33S73ScfA2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|0|
S0S34S74A1S5fS12fVs;S15Vs;Vm0;A2S9Vs;Vm0;A2Sc7A4A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MP). Qed.
Lemma K1b : ltac2:(tb__ "0|0|
S0S34S74A1S5fS138Vs;S15Vs;Vm0;A2S9Vs;Vm0;A2Sc7ScfA5A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S34S74A1S5fSc4A1S5fVs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc4S19Vs;Vm0;S6A3A2S33S73S76Sd4A1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc4S19Vs;Vm0;S7A3A2S33S73S76Sc8A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma MT1_P : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc4S19Vs;Vm0;SbA3A2S33S73S76Sd5A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_P, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MP)))]. Qed.
Lemma MT1_B : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc4S19Vs;Vm0;SaA3A2S33S73S76Sc6A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s1V, am1_B, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MB)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc5Vq;A2S5cSc4Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S34S68A1S77Sc5A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S32S74A1S60Sc5Vsc;A2S33S74S20Vs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S38S32S74A1M0S75A2M1A2S134Vsc;SdVm0;A1Vam0;Vs;A4S78S75G1S39G0S75S33S74S9Vs;Vm0;A2A2Sc4A4A3A3").
Proof using HI HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. apply (step1_deq s sc pM0 am0 HM0 pP pA xp xn).
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
S0S74S9Vs;Vm0;A2S19Vs;Vm0;S7A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc4S9Vs;Vm0;A2A2S33S73S76Sc8A1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0S79S75S38S74S75A2M0A2S135Vsc;S9Vs;Vm0;A2M1Sc8Sc4A4S78S75G0S39S74S75G1SceA4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSceS9Vs;Vm0;A2A2S33S73S76Sc8A1A2A3"). Proof using Hr Hsc Rg. unfold s2V. rewrite ?MT_set_hd. exact MT1_A. Qed.
Lemma S3 : ltac2:(tb__ "0|1|
S0S79S75S38S74S75A2M0A2S136Vsc;S9Vs;Vm0;A2Sc8SceA4S78S75G0S39S74S75S20Vs;Vm0;A2Sc5A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V. apply (step3_rot s2V sc pA am1_A pB); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | unfold am1_A; cbn [am_next am_set_links]; first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link | f_equal; cbn [mptr]; solve_link] | cbn [mptr]; solve_neq]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc5S20Vs;Vm0;A2A2S33S73S76Sc6A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite MT3. exact MT1_B. Qed.
Lemma Hav3 : am_avail am1_B = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold am1_B. cbn [am_avail am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S68S137Sc6A1SbcVs;Vm0;SaA3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MB <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S133Sc5S20Vs;Vm0;A2Sc6A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75S7aSbcVs;Vm0;SaA3A1Sc3A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pB s3V am1_B S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S68S7aSbcVs;Vm0;SaA3A1Z0A3A1").
Proof using HI HMI Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MB). pose proof (lowbit_range (maskA MB) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S13aVX;VU;Vs;Vsc;S7aSbcVs;Vm0;SaA3A1Sc3A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S32S74A1S60Sc3Vsc;A2S33S74S20Vs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pB am1_B). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc3S20Vs;Vm0;A2A2S33S73S76S130Sc6A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MB)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S68S86Sc6A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_B. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MB))). Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc3S19Vs;Vm0;S6A3A2S33S73S76Sd4A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_M0 | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_A : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc3S19Vs;Vm0;S7A3A2S33S73S76Sc8A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_A | cbn [mptr]; solve_neq]. Qed.
Lemma MTF_P : ltac2:(tb__ "0|0|
S0S32S73A1S5cSc3S19Vs;Vm0;SbA3A2S33S73S76Sd5A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pB am1_B); [rewrite MT3; exact MT1_P | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|0|
S93Vs;Sc4S31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3S92SdVm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pP pA xp xn))); [apply (delta_trans _ (s1b s pP pA xp xn)); [apply (delta_trans _ (s1a s pP pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pP (mam MP)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
S93Sc4SceS36S5bA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S93SceSc5S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1A3A3"). Proof using Hbnc Hgd Hr Hsc Hsp. unfold s3V. apply delta_sh. lia. Qed.
Lemma delta03 : ltac2:(tb__ "0|2|
S93Vs;Sc5S31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M0A3M1A3S92SdVm0;A1A1A3G0A3G1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [eapply delta_trans; [exact delta1 | exact delta2] | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1M0A1S30S5S8S6S67ScSbA1A1S67ScS7A1A1M1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7G0S67ScSaA1A1S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7S30S5S18S7S67S28S7A1A1A2S30S5S8SbS67Pa1A1G0S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7S30S5S8SaG1S67ScSeA1A1S67S11SaA1A1S67S13SaA1A1S67S14SaA1A1S67S10SaA1A1A7S30S5S18SaS67S28SaA1A1A2S30S5S1eS30S5S1bS30S5S17SaS67PaaA1A2S36S5A1A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49SaeA1S30S41S21Sc1S5S41S1fSc9A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D5nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MP); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MA_); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MB); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_meta_entry; [exact ze161 | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
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
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46SaeA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D5nr) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MP)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (v (vavail MB)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MB))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MB))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MB)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S51Z2126cS99S96S4eS3aS44A1S30S41S21S36S41A1A3S46SaeA1SabS3eA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4bS95VrhoW;Sd7S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4M0A4S4bS95VrhoW;SaeG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D5nr with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S32S38S34S38S44S44A2M0A1M1S34S42A1M2A2M3A1S14aSb4Sa7A2S33G3S39G1G2S30G0S39S44S44Sc0SaA1S40PabA1A4S36G0A1A3S3bG1G2Sb1A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_D5nr)). Qed.
Lemma swf_ST : swf ST_D5nr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S37S8eS42S42S91S42S56R1A1S46Sa7A1A3Lp;S3bS34S38S44S44A2A1S34S42A1Sb1A3A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S37S8eS42S103SedA1S46Sa7A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S37S8eS42S12cS46Sa7A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46Sa7A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST_D5nr) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MP)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MB)) (SLit 0)); SPUle (v (vbyte MB)) (SLit 255); SPAlign (vptr MB) 3; SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MB)) (v (vptr MA_))); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MB)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_D5nr = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S69S57Sa7A1SabA3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_D5nr 0 ST_D5nr.
Definition LT1 : sstate := lfs LT_D5nr 1 ST_D5nr.
Definition LT2 : sstate := lfs LT_D5nr 2 ST_D5nr.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Sd3A1A2ScbA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Sd1A1A2SccA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49Sd2A1A2ScdA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fScbA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fSccA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fScdA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fScbA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fSccA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fScdA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSc9ScbA2ScaA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSc9SccA2Sd6A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S34S5A1SbbSc9ScdA2Sd0A3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|3|
S0S34S5A1ScaS30S5S16S67ScSaA1A1M0A1S30S5S8S6S43Z0A1M1G1S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S8S7S67ScSbA1A1G0S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7S30S5S8SbS67Pa1A1S67ScS7A1A1M2S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7S30S5S8SaG2S67ScSeA1A1S67S11SaA1A1SbdSbfSaA1S67S10SaA1A1A7S36S5A1A3A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S34S5A1Sd0S31S5ScaS30S5S17SaSbeA2S36S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S3fS3dS5VdsF;A2S3dS5Sc9A2A3S5S8dS5R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S8dS5R2SbbSc9VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S34S5A1M0G0S5S8dS5R1SbbR3R2A2A3S8dS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sa3Vk;U3A2S0S34S41A1S49Sa4SaaVk;Sa7A3A1M0S30S41S111S52S90S41S21G0A3A1A1S8fS41G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S68S58Sa4SaaVk;Sa7A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S34S44A1S55Sa4SaaVk;Sa7A3A1S96A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S53S54Sa4SaaVk;Sa7A3A1S4eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S32S44A1S59Sa4SaaVk;Sa7A3A1S3aS44A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S44S4fSa4SaaVk;Sa7A3ZaA2S29S67PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S68S1S6aZ1R1A2S6aR1Z1fA2A2S0S37S97S71R2A1A1S35A3S0S44S4fSa4SaaVk;Sa7A3R3A2S98S71R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_D5nr k ST_D5nr) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S8dS42S4aSa0S43Z1fA1S23SaA1A3S46Sd3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S8dS42S4aSa1S67PaaA1S43Z0A1A3S46Sd1A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23SaA1A3A1S46Sd1A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa1S67PaaA1S43Z0A1A3A1S46Sd2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23SaA1A3A1S46Sd2A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S0S75S132Sc5S20Vs;Vm0;A2M1Sc6A3S131Sc5G1Sc6A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pB am1_B (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S93Vs;Sc3S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3M2A3S92SdVm0;A1A1A3G1A3G2A3S31S5bS31S5bS92S20Vs;Vm0;A2A1M3G1A3G3A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pB am1_B ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S93Vs;Sc3S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M1A3M2A3S92SdVm0;A1A1A3G1A3G2A3S31S5bS31S5bS92S20Vs;Vm0;A2A1M3S30S5bS5dS6bS62S6dVsc;G0A2A2A1G1A3A3G3A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pB am1_B ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S0S34S68A1S77Sc3A1S88S6dVsc;G0A2S6dVbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pB am1_B (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S8SaS67ScS7A1A1S67ScSeA1A1S67S11SaA1A1SbdSbfSaA1S67S10SaA1A1A7A11").
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
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S16S67ScSaA1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MB). Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S17SaSbeA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma ok_M0' : ltac2:(tb__ "0|1|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S8S6S43Z0A1M0G0S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7A11").
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
Lemma ok_A' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S8S7S67ScSbA1A1S67ScSaA1A1S67S11S7A1A1S67S13S7A1A1S67S14S7A1A1S67S10S7A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_A. split; [exact MTF_A|].
  split; [rewrite (ze_ptr MP); unfold am1_A, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MB); unfold am1_A, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_A, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MA_); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_P' : ltac2:(tb__ "0|0|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3S8SbS67Pa1A1S67ScS7A1A1S67S11SbA1A1S67S13SbA1A1S67S14SbA1A1S67S10SbA1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_P. split; [exact MTF_P|].
  split; [rewrite ze161; unfold am1_P, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MP), ?(am_next_mam MP); cbn [optrZ]; reflexivity|].
  split; [rewrite (ze_ptr MA_); unfold am1_P, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MP), ?(am_next_mam MP); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  unfold am1_P, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MP); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MP); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Ltac ok_changed := first [exact ok_meta' | exact ok_act' | exact ok_M0' | exact ok_A' | exact ok_P' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1ScaA3S1S8dS5R2ScbA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1Sd6A3S1S8dS5R2SccA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S5S8dS5R1Sd0A3S1S8dS5R2ScdA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sc3R2A11S10eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|5|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M0A3M1A3S92SdVm0;A1A1A3G0A3G1A3S31S5bS31S5bS92S20Vs;Vm0;A2A1M2G0A3G2A3A3A3S4S5S5S1S8dS5R1ScaA3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M3A3S61VL;R3A2M4A2S6cG4S3bS68S68G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pP with (mptr MP) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MP)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MP l Hl) as R_; exists (OD_meta MP (v 161) (v (vptr MA_)) (v (vmem MP)) (v (vavail MP)) (v (vfreed MP)) (v (vbits MP))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|5|
S5bS8dS5bR1S31S5bS31S5bS31S5bS31S5bS31S5bS31S5bS92S15Vs;Vm0;A2A1S92S9Vs;Vm0;A2A1A3S30S5bS5dS6bS5eS6eZ8Vsc;A2A2A1S36S5bA1M0A3M1A3S92SdVm0;A1A1A3G0A3G1A3S31S5bS31S5bS92S20Vs;Vm0;A2A1M2S30S5bS5dS6bS62S6dVsc;Z7A2A2A1G0A3A3G2A3A3A3S4S5S5S1S8dS5R1Sd0A3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M3A3S61VL;R3A2M4A2S6cG4S3bS68S68G3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl. change pP with (mptr MP) in Hl. change pB with (mptr MB) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MP)) (v (vptr MB)) (v (vmem MA_)) (v (vavail MA_)) (v (vfreed MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MP l Hl) as R_; exists (OD_meta MP (v 161) (v (vptr MA_)) (v (vmem MP)) (v (vavail MP)) (v (vfreed MP)) (v (vbits MP))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MB l Hl) as R_; exists (OD_meta MB (v (vptr MA_)) (v (vptr MC)) (v (vmem MB)) e_avT (e_freedT MB) (v (vbits MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MB e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MB))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Theorem variant_D5nr : ltac2:(tb__ "0|0|
VTR;Z0S144S95VK;SaeVrhoW;A4S110VX;VU;S124Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_D5nr)).
  { apply (seg_run 300 SA_D5nr LA_D5nr _ rhoW eq_refl eq_refl runA_D5nr (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_D5nr _ SA_D5nr LfA LA_D5nr_shape HinA) in HSPA. change (lfs LA_D5nr 0 SA_D5nr) with LA_D5nrs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_D5nrs ST_D5nr (e_maskA MB) (snd DT_D5nr) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_D5nr LT_D5nr _ rhoA ST_len ST_next runT_D5nr HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MB)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_D5nr _ _ _ ST_D5nr Lf LT_D5nr_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MB rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nr 0 ST_D5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nr 0 ST_D5nr) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nr 1 ST_D5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nr 1 ST_D5nr) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MB rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_D5nr 2 ST_D5nr) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_D5nr 2 ST_D5nr) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pB (am_final am1_B)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VD5nr.
End Mal_aslot_VD5nr.

Module Mal_aslot_VR1nh.

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

Section VR1nh.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;S3aS38S74S68A2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S6aZ0Vreq;A2S6aS6bVreq;S80A2S83Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S32S74A1S60Vs;Vsc;A2S33S74Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S65S64VX;Vs;Vsc;A3S33S74Vm0;A2S30S74Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§69§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§69§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§69§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§69§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§69§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§69§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§69§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls1 := (@U.Mal_aslot__G1.Mal_aslot_I.cls1 s X sc Hsc m0 rest Rg).
Local Notation "§70§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§70§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S148S125VX;S3aS38S74S68A2A1VU;S124Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S24S1S1S6aZ0M0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S6cG1Z100A2A2S1S0S68S6fG1Z20A2S7bSfVs;Vm0;R1A3M2A1A3S2S0S68S81G2A1G0A3A1S0S68S22VbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S7bSfVs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§71§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§71§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§71§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§71§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§72§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§72§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§72§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§72§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§71§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S6aZ1000S9bQ40S47Vrho;PaA2A2M0A2S0S68S6fG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S6aS12aZ40S9bQ40S47Vrho;PfA2A2A2M0S70S147Z0A1A1A2S6aS70S72Z2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S6aS129VL;A1S6bS9bQ40M0S47Vrho;PaA2A2S12aZ40S9bG0S47Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§73§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§73§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§74§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§72§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§74§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;Vrd0;Sb9S95VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S9aQ40A1S37F_;Vwok0;SbaS95VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z60A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ecR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S68S1S6aZ0R1A2S6cR1Z20A2A2S0S32S9aQ8A1M0A1VmW;S9cQ40S6bZ108ccR2A2A2A1S3aG0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S24S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS2bVL;S82SfVs;Vm0;R1A3A1A2Z8A2A2A3S33G1S9cG0S22VbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S32S9aQ8M0A1M1A1Sb9S95VmW;S9cQ40S6bS6bZ5a3d0Z369A2Vsc;A2A2A3S33G1S9cG0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S127S126Vrd0;S9aQ40A1S35L_;A2S128S125A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S126Sb9S95VmW;A2SbaS95VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§75§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§75§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§69§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§76§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§76§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§77§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§77§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§72§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§72§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§72§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S0S68Vbnc;S84S6dVsc;G0A2S77Vs;A1A2A3F_;").
Local Notation "§78§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§78§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§71§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S149S95VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S34Sb5A1Sb6OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§79§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§79§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Abbreviation tr_seq := (@U.Mal_aslot__G2.Mal_aslot_W.tr_seq Kc RF GF TR RR).
Local Notation "§80§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§80§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§81§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§81§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§82§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§82§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_maskA := (@U.Mal_aslot__G3.Mal_aslot_T.e_maskA).
Local Abbreviation e_freedT := (@U.Mal_aslot__G3.Mal_aslot_T.e_freedT).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§69§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§83§ h__" := (h__ s L X U sc rho bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation maskA_range := (§83§ U.Mal_aslot__G3.Mal_aslot_T.maskA_range).
Local Abbreviation ze_maskA := (§74§ U.Mal_aslot__G3.Mal_aslot_T.ze_maskA).
Local Abbreviation ze_freedT := (§74§ U.Mal_aslot__G3.Mal_aslot_T.ze_freedT).
Local Notation "§84§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§84§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§85§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§85§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§86§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§86§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§87§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§87§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§88§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§88§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§88§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§84§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§80§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§89§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§89§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§89§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§89§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§70§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§70§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§70§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (@U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0 s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S9aQ40A1S32S9aQ8A1A1F_;VmW;S50Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0Sb7Vvm;Sb8Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S34Sb5A1M0Sb6VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0Sb6R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4bS95Vrho;S146S145A1S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S68S9bQ40S47Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 1%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S68S7cSfVs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S68S7dSfVs;Vm0;S6A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S68S7dSfVs;Vm0;S6A3M0A1S87S85G0A1A1A3A1").
Hypothesis HVact : maskA MM0 <> 0.
Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S68Vmaskv;SbcVs;Vm0;S6A3A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cVs;SdVm0;A1A2S33S73S76Vam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls1 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls1 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.

Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition s1V : astate := ltac2:(tb__ "0|0|
S94Vsc;S33S74S9Vs;Vm0;A2A2Vs;A3").
Definition s2V : astate := ltac2:(tb__ "0|0|
S94Vsc;S33S74S9Vs;Vm0;A2A2Vs;A3").
Definition s3V : astate := ltac2:(tb__ "0|0|
S94Vsc;S33S74S9Vs;Vm0;A2A2Vs;A3").
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S32S73A1S5cS115S19Vs;Vm0;S6A3A2S33S73S76S112A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT3 q : ltac2:(tb__ "0|0|
S0S32S73A1S5cS114Vq;A2S5cS115Vq;A2A3"). Proof using . unfold s3V, s2V. rewrite ?MT_set_hd. reflexivity. Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI. unfold s3V, s2V. rewrite ?keys_set_hd. exact ND1. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S34S68A1S77S114A1S77Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HXr. unfold s3V, s2V. repeat apply xraw_set_hd. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S32S74A1S60S114Vsc;A2S33S74SdVm0;A1A2A3").
Proof using HI Hbnc Hgd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. replace (Some pM0) with (Some pA) by (f_equal; solve_link). apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0S79S75S38S32S74A1M0S75A2M1A2S134Vsc;SdVm0;A1Vam0;Vs;A4S78S75G1S39G0S75S33S74S9Vs;Vm0;A2A2S115A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S74S9Vs;Vm0;A2S19Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S32S73A1S5cS115S9Vs;Vm0;A2A2S33S73S76S112A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_M0. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0S79S75S38S74S75A2M0A2S135Vsc;S9Vs;Vm0;A2S112S115A4S78S75G0S39S74S75SdVm0;A1S11bA4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V, s1V. rewrite E_m1. apply step2_stay. unfold am1_M0. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S32S73A1S5cS11bSdVm0;A1A2S33S73S76S112A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. rewrite ?MT_set_hd. exact MT1_M0. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0S79S75S38S74S75A2M0A2S136Vsc;SdVm0;A1M1S112S11bA4S78S75G0S39S74S75G1S114A4A3A3").
Proof using HVact. drop_sp. unfold s3V, s2V. apply step3_hit. unfold am1_M0. cbn [am_freed am_aidx am_set_links]. exact HVact. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S32S73A1S5cS114SdVm0;A1A2S33S73S76S112A1A2A3"). Proof using HI Hhd Hsc. rewrite MT3. exact MT1_M0. Qed.
Lemma Hav3 : am_avail am1_M0 = 0. Proof using HVa0. unfold am1_M0. cbn [am_avail am_set_links]. exact HVa0. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S68S137S112A1SbcVs;Vm0;S6A3A3"). Proof using . reflexivity. Qed.

Lemma HVmask3 : maskA MM0 <> 0.
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp. rewrite <- Emask. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_M0 pM0 s2V am1_M0 pM0 s3V am1_M0 S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S133S114SdVm0;A1S112A3").
Lemma taR : ltac2:(tb__ "0|1|
S0S79S75S38S68S75A2M0A2S7fVsc;Vs;A2S78S75G0S39S68S75S7aSbcVs;Vm0;S6A3A1S113A4A3A3").
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_M0 pM0 s2V am1_M0 pM0 s3V am1_M0 S1 HM1 S2 HM2 S3 HM3 Hav3 ltac:(rewrite Emask; exact HVmask3)).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S68S7aSbcVs;Vm0;S6A3A1Z0A3A1").
Proof using HI HMI HVact Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth. pose proof (maskA_range MM0). pose proof (lowbit_range (maskA MM0) ltac:(lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S13aVX;VU;Vs;Vsc;S7aSbcVs;Vm0;S6A3A1S113A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S32S74A1S60S113Vsc;A2S33S74SdVm0;A1A2A3"). Proof using HI Hbnc Hgd Hr Hsc Hsp Rg. unfold sR'. rewrite (active_hd_s6 s3V pM0 am1_M0). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S32S73A1S5cS113SdVm0;A1A2S33S73S76S130S112A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MM0)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S68S86S112A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_M0. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MM0))). Qed.

Lemma delta1 : ltac2:(tb__ "0|0|
S93Vs;S115S36S5bA1A3").
Proof using Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. unfold s1V. replace (Some pA) with (Some pM0) by (f_equal; symmetry; solve_link). change pM0 with m0. rewrite <- Hhd. apply delta_sh_same; [lia|]. left. rewrite Hhd. discriminate. Qed.
Lemma delta2 : ltac2:(tb__ "0|0|
S93S115S11bS36S5bA1A3"). Proof using . unfold s2V. apply delta_refl. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S93S11bS114S36S5bA1A3"). Proof using . unfold s3V. apply delta_refl. Qed.
Lemma delta03 : ltac2:(tb__ "0|0|
S93Vs;S114S36S5bA1A3").
Proof using Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s3V, s2V, s1V. rewrite ?set_hd_set_hd. replace (Some pA) with (Some pM0) by (f_equal; symmetry; solve_link). change pM0 with m0. rewrite <- Hhd. apply delta_sh_same; [lia|]. left. rewrite Hhd. discriminate.
Qed.

Definition dsR : list od := ltac2:(tb__ "0|1|
S30S5S1cS30S5S1dS30S5S16S67ScS6A1A1M0A1S30S5S8S6G0G0S67S11S6A1A1S67S13S6A1A1S67S14S6A1A1S67S10S6A1A1A7S30S5S18S6S67S28S6A1A1A2S30S5S1eS30S5S1bS30S5S17S6S67PaaA1A2S36S5A1A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S34S41A1S49S109A1S30S41S21Sc1S5S41S1fS116A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R1nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_mem_entry.
  - apply od_ok_sct.
  - apply od_ok_ctz.
  - apply od_ok_bnc_entry.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using . drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

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
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46S109A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hsc Hsp Hsp_high.
  change (ss_facts SA_R1nh) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MM0)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MM0))) (SLit 18446744073709551615)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MM0)))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615))) (SLit 0)); SPUle (v (vavail MM0)) (SLit 0); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615))) (SLit 0)); SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MM0)))) (SLit 0))]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S51Z2126cS99S96S4eS3aS44A1S30S41S21S36S41A1A3S46S109A1S10aS3eA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4bS95VrhoW;S121S39S34Sb5A1S122Vtr;S123Vms;Vmd;A2A4M0A4S4bS95VrhoW;S109G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R1nh with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma sd_R : ltac2:(tb__ "0|4|
S0S32S38S34S38S44S44A2M0A1M1S34S42A1M2A2M3A1S14aS10cS104A2S33G3S39G1G2S30G0S39S44S44Sc0S6A1S40PabA1A4S36G0A1A3S3bG1G2S10bA3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT_R1nh)). Qed.
Lemma swf_ST : swf ST_R1nh = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl : ltac2:(tb__ "0|0|
S0S37S8eS42S42S91S42S56R1A1S46S104A1A3Lp;S3bS34S38S44S44A2A1S34S42A1S10bA3A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_vars : ltac2:(tb__ "0|0|
S0S37S8eS42S103SedA1S46S104A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST_sup : ltac2:(tb__ "0|0|
S0S37S8eS42S12cS46S104A1A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST : ltac2:(tb__ "0|0|
Sc2S42S12bS26Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS25Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S46S104A1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST_R1nh) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MM0)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST_len : ss_lenient ST_R1nh = false. Proof using . reflexivity. Qed.
Lemma ST_next : ltac2:(tb__ "0|0|
S0S69S57S104A1S10aA3"). Proof using . reflexivity. Qed.

Definition LT0 : sstate := lfs LT_R1nh 0 ST_R1nh.
Definition LT1 : sstate := lfs LT_R1nh 1 ST_R1nh.
Definition LT2 : sstate := lfs LT_R1nh 2 ST_R1nh.
Definition dsF0 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT0))) in exact x).
Definition dsF1 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT1))) in exact x).
Definition dsF2 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT2))) in exact x).
Definition dsC0 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF0) in exact x).
Definition dsC1 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF1) in exact x).
Definition dsC2 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF2) in exact x).
Lemma match0 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49S11fA1A2S118A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match1 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49S11dA1A2S119A2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match2 : ltac2:(tb__ "0|0|
S0S37S10dS8fS41S49S11eA1A2S11aA2S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars0 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fS118A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars1 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fS119A4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars2 : ltac2:(tb__ "0|0|
S0S37S8eS41S102SedA1Sc1S5S41S1fS11aA4A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem0 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fS118A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem1 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fS119A3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem2 : ltac2:(tb__ "0|0|
S0S37S8eS5S10fS11aA3S35A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg0 : ltac2:(tb__ "0|0|
S0S34S5A1SbbS116S118A2S117A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg1 : ltac2:(tb__ "0|0|
S0S34S5A1SbbS116S119A2S120A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg2 : ltac2:(tb__ "0|0|
S0S34S5A1SbbS116S11aA2S11cA3"). Proof using . vm_compute. reflexivity. Qed.

Lemma dsC0_eq : ltac2:(tb__ "0|1|
S0S34S5A1S117S30S5S8S6S67ScS6A1A1M0G0S67S11S6A1A1SbdSbfS6A1S67S10S6A1A1A7S36S5A1A3A3"). Proof using . reflexivity. Qed.
Lemma dsC1_eq : dsC1 = dsC0. Proof using . reflexivity. Qed.
Lemma dsC2_eq : ltac2:(tb__ "0|0|
S0S34S5A1S11cS31S5S117S30S5S17S6SbeA2S36S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S3fS3dS5VdsF;A2S3dS5S116A2A3S5S8dS5R1VdsF;A3S3S2aVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S8dS5R2SbbS116VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S34S5A1M0G0S5S8dS5R1SbbR3R2A2A3S8dS5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Lemma LT_objs k : ltac2:(tb__ "0|1|
Sa3Vk;U3A2S0S34S41A1S49S105S106Vk;S104A3A1M0S30S41S111S52S90S41S21G0A3A1A1S8fS41G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_pc k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S68S58S105S106Vk;S104A3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fregs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S34S44A1S55S105S106Vk;S104A3A1S96A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_fcsr k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S53S54S105S106Vk;S104A3A1S4eA3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_resv k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S32S44A1S59S105S106Vk;S104A3A1S3aS44A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_a0 k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S0S44S4fS105S106Vk;S104A3ZaA2S29S67PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT_cs k : ltac2:(tb__ "0|0|
Sa3Vk;U3A2S68S1S6aZ1R1A2S6aR1Z1fA2A2S0S37S97S71R2A1A1S35A3S0S44S4fS105S106Vk;S104A3R3A2S98S71R3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT_R1nh k ST_R1nh) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f0 : ltac2:(tb__ "0|0|
S8dS42S4aSa0S43Z1fA1S23S6A1A3S46S11fA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1a : ltac2:(tb__ "0|0|
S8dS42S4aSa1S67PaaA1S43Z0A1A3S46S11dA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f1b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23S6A1A3A1S46S11dA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2a : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa1S67PaaA1S43Z0A1A3A1S46S11eA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f2b : ltac2:(tb__ "0|0|
S8dS42S4dS4aSa0S43Z1fA1S23S6A1A3A1S46S11eA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S0S75S132S114SdVm0;A1M1S112A3S131S114G1S112A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pM0 am1_M0 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S93Vs;S113S31S5bS36S5bA1M1S31S5bS31S5bS92SdVm0;A1A1M2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pM0 am1_M0 ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S93Vs;S113S31S5bS36S5bA1M1S31S5bS31S5bS92SdVm0;A1A1M2S30S5bS5dS6bS62S6dVsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pM0 am1_M0 ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S6aZ7M0Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S0S34S68A1S77S113A1S88S6dVsc;G0A2S6dVbnc;Z1A2S77Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pM0 am1_M0 (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.

Lemma ok_meta' : ltac2:(tb__ "0|1|
S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S113S8S6S67ScS6A1A1M0G0S67S11S6A1A1SbdSbfS6A1S67S10S6A1A1A7A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final am1_M0). split; [exact MT_R'|].
  pose proof (am_final_fields am1_M0) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold am1_M0, am0; cbn [am_prev am_set_links]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold am1_M0, am0; cbn [am_next am_set_links]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold am1_M0; cbn [am_mem am_set_links]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; rewrite Emask; reflexivity|].
  split; [rewrite ze_freedT; unfold am1_M0; cbn [am_freed am_aidx am_set_links]; reflexivity|].
  rewrite ze_bits. unfold am1_M0, meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S113S17S6SbeA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Ltac ok_changed := first [exact ok_meta' | exact I].
Lemma okC_0 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1S117A3S1S8dS5R2S118A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S113R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg0 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_1 : ltac2:(tb__ "0|1|
S3S2S1S6aZ7Vsc;A2S6cVsc;Z27A2A2M0A1S1G0S0S68Vbnc;Z0A3A2A2S5S8dS5R1S120A3S1S8dS5R2S119A3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S113R2A11S10eVsc;R2A2A2A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg1 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC1_eq, dsC0_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed | exact I]|]). destruct Hd. Qed.
Lemma okC_2 : ltac2:(tb__ "0|0|
S1S6aZ7Vsc;A2S6cVsc;Z27A2A2S2S0S68Vbnc;Z0A3A1S5S8dS5R1S11cA3S1S8dS5R2S11aA3S1S12Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S113R2A11S10eVsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg2 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC2_eq, dsC0_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs_01 : ltac2:(tb__ "0|4|
S5bS8dS5bR1S31S5bS36S5bA1M0S31S5bS31S5bS92SdVm0;A1A1M1G0A3G1A3A3A3S4S5S5S1S8dS5R1S117A3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M2A3S61VL;R3A2M3A2S6cG3S3bS68S68G2A3A2A2A2Ld;A2F_;Fl;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC0_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedT MM0) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
              ].
Qed.
Lemma locs_2 : ltac2:(tb__ "0|4|
S5bS8dS5bR1S31S5bS36S5bA1M0S31S5bS31S5bS92SdVm0;A1A1M1S30S5bS5dS6bS62S6dVsc;Z7A2A2A1G0A3A3G1A3A3A3S4S5S5S1S8dS5R1S11cA3S1S6aS3cS68S68S27Vs;VL;Vsc;Vm0;R1A5M2A3S61VL;R3A2M3A2S6cG3S3bS68S68G2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC2_eq, dsC0_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedT MM0) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MM0 e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
              ].
Qed.

Theorem variant_R1nh : ltac2:(tb__ "0|0|
VTR;Z0S144S95VK;S109VrhoW;A4S110VX;VU;S124Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  apply (tr_seq _ (POST ST_R1nh)).
  { apply (seg_run 300 SA_R1nh LA_R1nh _ rhoW eq_refl eq_refl runA_R1nh (agrees_refl rhoW)).
    intros LfA rhoA [trA [msA mdA]] HinA HagA HSPA.
    rewrite (single_leaf LA_R1nh _ SA_R1nh LfA LA_R1nh_shape HinA) in HSPA. change (lfs LA_R1nh 0 SA_R1nh) with LA_R1nhs in HSPA.
    exists rhoA. split; [exact HagA|].
    apply (linkT LA_R1nhs ST_R1nh (e_maskA MM0) (snd DT_R1nh) rhoA _ swf_ST sd_R HagA eq_refl eq_refl); try assumption.
    - rewrite ze_maskA, Hmv. reflexivity.
    - exact nf_incl. - exact ST_vars. - exact ST_sup. - exact ZF_ST. }
  apply from_POST. intros rhoA HagA.
  apply (seg_run 300 ST_R1nh LT_R1nh _ rhoA ST_len ST_next runT_R1nh HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (maskA MM0)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT_R1nh _ _ _ ST_R1nh Lf LT_R1nh_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MM0 rhoF _ _ HagF (conj HsmF HK') f0).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R1nh 0 ST_R1nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R1nh 0 ST_R1nh) _ _ dsF0 dsC0 (LT_objs 0%nat ltac:(repeat constructor)) match0 HsmF vars0 sem0
              ltac:(rewrite <- chg0; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_0 (or_introl OUT)) locs_01
              (LT_pc 0%nat ltac:(repeat constructor)) (LT_cs 0%nat ltac:(repeat constructor)) (LT_fregs 0%nat ltac:(repeat constructor)) (LT_fcsr 0%nat ltac:(repeat constructor)) (LT_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f1b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f1a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R1nh 1 ST_R1nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R1nh 1 ST_R1nh) _ _ dsF1 dsC1 (LT_objs 1%nat ltac:(repeat constructor)) match1 HsmF vars1 sem1
              ltac:(rewrite <- chg1; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_1 (or_intror (conj IN B0))) locs_01
              (LT_pc 1%nat ltac:(repeat constructor)) (LT_cs 1%nat ltac:(repeat constructor)) (LT_fregs 1%nat ltac:(repeat constructor)) (LT_fcsr 1%nat ltac:(repeat constructor)) (LT_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f2b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f2a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT_R1nh 2 ST_R1nh) 10)) = ctz32 maskv).
    { rewrite (LT_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT_R1nh 2 ST_R1nh) _ _ dsF2 dsC2 (LT_objs 2%nat ltac:(repeat constructor)) match2 HsmF vars2 sem2
              ltac:(rewrite <- chg2; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_2 IN BN) locs_2
              (LT_pc 2%nat ltac:(repeat constructor)) (LT_cs 2%nat ltac:(repeat constructor)) (LT_fregs 2%nat ltac:(repeat constructor)) (LT_fcsr 2%nat ltac:(repeat constructor)) (LT_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final am1_M0)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.

End VR1nh.
End Mal_aslot_VR1nh.
