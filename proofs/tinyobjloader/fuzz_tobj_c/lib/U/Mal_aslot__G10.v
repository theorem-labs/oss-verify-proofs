(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "od"; "MM0"; "MA_"; "mam"; "pM0"; "pA"; "OD_meta"; "od_ok_at"; "OD_act"; "OD_mem"; "obj_of"; "OD_bnc"; "OD_got"; "OD_guard"; "OD_ctz"; "OD_sct"; "vbits"; "vmem"; "zl1"; "zr1"; "O_stk"; "vptr"; "e_bncidx"; "mbyte"; "od_range"; "vavail"; "vfreed"; "member"; "mptr"; "zA"; "od_ok"; "e_ctz"; "O_act"; "O_ctz"; "O_got"; "O_guard"; "O_sct"; "vbyte"; "@Corelib.Init.Datatypes"; "cons"; "list"; "bool"; "true"; "prod"; "app"; "option"; "nil"; "pair"; "fst"; "Some"; "None"; "snd"; "nat"; "negb"; "false"; "andb"; "length"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "sprop"; "sobj"; "SAlu"; "ss_facts"; "SAluW"; "rw"; "SPBranch"; "reg_sv"; "ss_objs"; "cell"; "SPNot"; "smatch"; "mkCell"; "FcsrFrm0"; "SExt"; "ss_fcsr"; "ss_fregs"; "valuation"; "obj_holds"; "sfcsr"; "ss_resv"; "rm"; "ss_next"; "ob_cells"; "obj_range"; "mkSS"; "ss_pc"; "DUnknown"; "eval"; "mkObj"; "sprop_eqb"; "SPUle"; "c_off"; "c_val"; "mkVal"; "odefault"; "rl"; "sstate"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_lenient"; "ss_regs"; "sv_eqb"; "swf"; "tfact"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "active_hd"; "MT"; "LMem"; "LCtx"; "keys"; "loc_addr"; "CTX_active"; "Inv"; "CTX_bounces"; "alinks"; "ring_ok"; "MCell"; "VZ"; "image"; "layout"; "mcell"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "modulo"; "opp"; "to_nat"; "pow"; "ltb"; "of_nat"; "eqb"; "land"; "leb"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "mslot"; "am_mem"; "am_aidx"; "MUsed"; "padd"; "am_last"; "IRet"; "itree"; "st_bounces"; "am_freed"; "class_size"; "am_maplen"; "lowbit"; "try_avail"; "IB"; "am_sc"; "am_set_links"; "ones"; "znth"; "am_avail"; "am_next"; "UNIT"; "am_prev"; "am_set_aidx"; "span_loop"; "st_regions"; "zset"; "region"; "st_init_done"; "st_metas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "pre_regs"; "callee_saved"; "pre_reg"; "NF"; "setregs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_SUB"; "ALU_ADD"; "BC_LTU"; "ALU_SLL"; "ALU_OR"; "BC_EQ"; "ALU_XOR"; "BC_LT"; "BC_NE"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "seq"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VD2ns.VD2ns"; "am1_A"; "sR'"; "AM3"; "L0"; "s3V"; "s1V"; "dsR"; "EB0"; "EB2"; "L1"; "cnt1"; "dsC00"; "dsC20"; "dsF00"; "dsF01"; "dsF02"; "dsF20"; "dsF21"; "dsF22"; "xp"; "dsC02"; "dsC22"; "s2V"; "LT01"; "LT02"; "LT21"; "LT22"; "xn"; "LT00"; "LT20"; "am1_M0"; "dsC01"; "dsC21"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VR1ns.VR1ns"; "am1_M0"; "sR'"; "AM3"; "L0"; "s3V"; "dsR";
"s1V"; "EB0"; "EB2"; "L1"; "cnt1"; "dsC00"; "dsC20"; "dsF00"; "dsF01"; "dsF02"; "dsF20"; "dsF21"; "dsF22"; "dsC02"; "dsC22"; "s2V"; "LT01"; "LT02"; "LT21"; "LT22"; "LT00"; "LT20"; "dsC01"; "dsC21"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "set_hd"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "in_vars"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "lfs"; "ST0_R1ns"; "ST2_R1ns"; "SA_R1ns"; "SL_R1ns"; "DL_R1ns"; "LX_R1ns"; "NXA"; "DX_R1ns"; "LT0_R1ns"; "LT2_R1ns"; "SA_E"; "SA_N"; "DT0_R1ns"; "DT2_R1ns"; "LA_R1nss"; "SX_R1ns"; "LL_R1ns"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD"; "lfs"; "ST0_D2ns"; "ST2_D2ns"; "SA_D2ns"; "SL_D2ns"; "DL_D2ns"; "LX_D2ns"; "DX_D2ns"; "LT0_D2ns"; "LT2_D2ns"; "NXA"; "DT0_D2ns"; "DT2_D2ns"; "LA_D2nss"; "SX_D2ns"; "LL_D2ns"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "span_cnt"; "t_mask"; "am_final"; "s1a"; "s4"; "s5"; "s6"; "step1"; "step2"; "step3"; "s1_deq"; "s1_empty"; "s1b"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T"; "changed"; "e_avT"; "e_bncdec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "sv_vars_all"; "sprop_vars_all"; "state_vars_all"; "agree_vals"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_s"; "MA"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "mc_chk_guard"; "holds"; "topL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W"; "objs_matchb"; "od_chg_ok"; "od_sem"; "oStkF"; "HITP"; "keys_distinct"; "NREL"; "m'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L"; "setsA"; "e_maskG"; "setsX"; "e_freedG"; "e_last1"; "diff_okb"; "e_size"; "e_a40"; "e_a60"; "e_span0"; "rename_chk"; "setsB"; "span0_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zeval"; "zholds"; "psupported"; "sx32"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VE.VE"; "sE"; "dsF"; "LE"; "dsC"; "dsR"; "S0R"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsCut"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "as_stack"; "IEC_U"; "Pre_as"; "tier"; "AS_D"; "J_as_pre"; "auxv_init"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G"; "sv_nolist"; "fG"; "stkcG"; "SG"; "GX"; "obj_nolist"; "factsG"; "oAct0"; "oGot"; "oGuard"; "oStkG"; "regsG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN.N"; "LN"; "dsN"; "S0N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.G.ReabG"; "rhoG"; "rwG"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "ltb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "mem_kept_owned"; "rd_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN.N.PostN"; "rhoN"; "rwN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "pdr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot"; "ta_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_VN"; "m0d"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_aslot_G.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition stkcG : list cell := ltac2:(tb__ "0|1|
S2bS4dS50S43N60A1Z8M0S42PaeA1A3S2bS4dS50S43N58A1G0S42P2dA1A3S2bS4dS50S43N50A1G0S42P2cA1A3S2bS4dS50S43N48A1G0S42P2bA1A3S2bS4dS50S43N40A1G0S42P2aA1A3S2bS4dS50S43N38A1G0S42P29A1A3S2bS4dS50S43N30A1G0S42P28A1A3S2bS4dS50S43N28A1G0S42P27A1A3S2bS4dS50S43N20A1G0S42P26A1A3S2bS4dS50S43N18A1G0S42P1dA1A3S2bS4dS50S43N10A1G0S42P1cA1A3S2bS4dS50S43N8A1G0S42PbA1A3S32S4dA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition oStkG : sobj := ltac2:(tb__ "0|0|
S61S42PaA1S42PfA1S43Z0A1S18fS5fA5").
Definition oGot : sobj := ltac2:(tb__ "0|2|
S61S43Z28d50A1S43Z0A1M0S43Z8M1A1S2bS4dS50G0G1S42PadA1A3S32S4dA1A3S5fA5").
Definition oGuard : sobj := ltac2:(tb__ "0|2|
S61S42PadA1S43Z0A1M0S43Z8M1A1S2bS4dS50G0G1S42PaeA1A3S32S4dA1A3S5fA5").

Definition oAct0 : sobj := ltac2:(tb__ "0|2|
S61S43Z5a3c8A1S46Sc4S46Sc6S42PcA1S43Z3A1A3M0S43Z58A1A3M1S46Sc4G0S43Z60A1A3S2bS4dS50G1Z8S43Z0A1A3S32S4dA1A3S5fA5").

Definition regsG : list sv := ltac2:(tb__ "0|4|
SbeSbaS2bS2fS38S41A2M0S33S38S41U2S46Sc4S42PaA1S43N90A1A3A4S2bG0S33S38S41U8S42PcA1M1A4S2bG0S33S38S41U9S42P1dA1A4S2bG0S33S38S41UaS42Pd2A1A4S2bG0S33S38S41UbS42Pd3A1A4S2bG0S33S38S41UcS42Pd4A1A4S2bG0S33S38S41U12S42PdA1A4S2bG0S33S38S41U14S42PadA1A4S2bG0S33S38S41U15S46Sc4S46Sc6G1S43Z3A1A3M2S43Z5a420A1A3A4S2bG0S33S38S41U16S43Z5a3c8A1M3A4S2bG0S33S38S41U17S46Sc4G2G3A3A4S32G0A1A3A3A3A3A3A3A3A3A3A3A3A2").

Definition factsG : list sprop := ltac2:(tb__ "0|1|
S30S44S30S44S2bS44S1a5S2bS44S1a6S18aA1S32S44A1M0A3A3S1a4S18aA1A3S2bS44S63S42PcA1S43Z2fA1A2G0A3A3").

Definition SG : sstate := ltac2:(tb__ "0|0|
S5dZ2144cS198Sb9S51S36S41A1S2bS45S197S2bS45S195S2bS45S196S2bS45S194S32S45A1A3A3A3A3S193S122S3aA9").

Definition GX (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho : valuation) : assn := ltac2:(tb__ "0|9|
S1b1Sc0Q40M0S49Vrho;PcA2A2S3eS4S158S158S4S55S55S1S153SbdVrho;R1A3S1S0S82S159R2A1S159VA;A1A3S1S3eS84Z0M1R1A2S2S0S3eR2R5A3A1S0S31S98A1M2S74S157R5A1R3A2S74S157VA;A1M3R3A2A3F_;F_;Fc;S1S1a9G3S157R2A1M4A2S1S1a7S15aVA;R2S59Vrho;A1M5S59R1A1A5S1S0G2S74G4R3A2S36S98A1A3S1S0SbfG0A1M6S49R1PadA2Sc1G0S15cS15aA1M7A2A3S1S0Sa1S99S2fS3eS99A2M8A2Sa7R3G3A2Sa0S99G8S33S3eS99G1G4A4A3A3S1S0S2cSb5A1Sb3G4A1Sb3G3A1A3S1S15dS15bS1a8Sb8G5A2G6S2eL_;A2G7U8Sc0G0S49R1PaeA2A2A4S182Sb8S18bSb8S15aVX;VU;R2VKc;A6S190R1R4A5A2A2A2A2A2A2A2A2A2A2LrhoG;A2LA_G;A2Tsc;Lw;").

Definition regsG_okb (SF : sstate) : bool := ltac2:(tb__ "0|0|
S93S3eS3eS3dS95S3eS8fR1A1S2bS3eZaS2bS3eZbS2bS3eZcS32S3eA1A3A3A3A3S70S4bVSF;R1A2S4bS190R1A2A2A2Lr;SccS38S3eS8eSceU1U1fA2A4A3").

Fixpoint sv_nolist (e : sv) : bool :=
  match e with
  | SLBytes _ _ _ => false
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => sv_nolist a && sv_nolist b
  | SExt _ _ a => sv_nolist a
  | _ => true
  end.
Definition obj_nolist (o : sobj) : bool := ltac2:(tb__ "0|1|
S3bS3bS3bS3bS18dS6aVo;A1A1S18dS6dVo;A1A1A2S18dS6cVo;A1A1A2S93S4dS4dS3bS18dS64R1A1A1S18dS65R1A1A1A2Lc;S5bVo;A1A3A2S67S2dLx;S6bVo;A1S2eS3aS3aS3fS3aLl;M0G0S3eS41S2cS2fS3eS3eA2A1S2cS72A1S3aLtmpl;Lflds;Lcnt;Lesz;X67x6A2").

Lemma eval_agree_vars_nl : ltac2:(tb__ "0|1|
S3fS2dF_;S55S55S41S3fS0S2dR5R1A1S2eA3S0SbfQ40A1M0S49R5R2A2S49R4R2A2A3F_;Fv;S0S2dS150R5R2A2S2eA3S0S2dS18dR3A1S2eA3S0G0S60R6R4A2S60R5R4A2A3F_;F_;F_;Fe;Frho';Frho;Ff;").
Proof.
  intros f rho rho' e Hv. induction e; cbn; intros H Hn; try discriminate;
    try (apply andb_prop in H as [H1 H2]; apply andb_prop in Hn as [N1 N2]; rewrite (IHe1 H1 N1), (IHe2 H2 N2)); try reflexivity.
  - apply Hv. exact H.
  - rewrite (IHe H Hn). reflexivity.
Qed.

Section NoList.
  Context (segs : list Segment).
  Lemma obj_holds_agree_vars_nl : ltac2:(tb__ "0|0|
S3fS2dF_;S55S55S1b0S45S3fS0S2dR6R1A1S2eA3S0SbfQ40A1S49R6R2A2S49R5R2A2A3F_;Fv;S0S2dS14fR6R2A2S2eA3S0S2dS192R3A1S2eA3S56Vsegs;R7R5R4A4S56Vsegs;R7R6R5A4F_;F_;F_;F_;Fo;Fms;Frho';Frho;Ff;").
  Proof using .
    intros f rho rho' ms o Hv Ho Hn (Hb & Hw & Hc & Hd & Hdl).
    unfold obj_vars_all in Ho. apply andb_prop in Ho as [Ho Hdv]. apply andb_prop in Ho as [Ho Hcells]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
    unfold obj_nolist in Hn. apply andb_prop in Hn as [Hn Ndf]. apply andb_prop in Hn as [Hn Ncells]. apply andb_prop in Hn as [Hn Nhi]. apply andb_prop in Hn as [Nbase Nlo].
    pose proof (eval_agree_vars_nl f rho rho' _ Hv Hbase Nbase) as EB.
    assert (ELO : obj_lo_of rho' o = obj_lo_of rho o).
    { unfold obj_lo_of, soff. rewrite (eval_agree_vars_nl f rho rho' _ Hv Hlo Nlo). reflexivity. }
    assert (EHI : obj_hi_of rho' o = obj_hi_of rho o).
    { unfold obj_hi_of, soff. rewrite (eval_agree_vars_nl f rho rho' _ Hv Hhi Nhi). reflexivity. }
    assert (EC : forall c, In c (ob_cells o) -> soff rho' (c_off c) = soff rho (c_off c) /\ eval rho' (c_val c) = eval rho (c_val c)).
    { intros c Hin. pose proof (proj1 (forallb_forall _ _) Hcells c Hin) as W. apply andb_prop in W as [W1 W2].
      pose proof (proj1 (forallb_forall _ _) Ncells c Hin) as WN. apply andb_prop in WN as [WN1 WN2].
      unfold soff. rewrite (eval_agree_vars_nl f rho rho' _ Hv W1 WN1), (eval_agree_vars_nl f rho rho' _ Hv W2 WN2). auto. }
    assert (COV : forall off, covered rho' (ob_cells o) off <-> covered rho (ob_cells o) off).
    { intros off. unfold covered. rewrite !Exists_exists. split; intros (c & Hin & Hic); exists c; split; auto;
        unfold in_cell in *; destruct (EC c Hin) as [E1 _]; [rewrite <- E1 | rewrite E1]; exact Hic. }
    unfold obj_holds. rewrite <- EB, ELO, EHI. split; [exact Hb|]. split; [exact Hw|]. split; [|split].
    - apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (A & B & C).
      destruct (EC c Hin) as [E1 E2]. unfold SymState.cell_holds, SymState.oaddr in *. rewrite E1, E2, <- EB. repeat split; assumption.
    - intros off Hoff Hnc. specialize (Hd off Hoff ltac:(intros X; apply Hnc; apply COV; exact X)).
      destruct (ob_dflt o); try discriminate. exact Hd.
    - destruct (ob_dflt o); try discriminate. exact I.
  Qed.
End NoList.

Lemma obj_range_agree_vars_nl : ltac2:(tb__ "0|0|
S3fS2dF_;S55S55S45S3fS0S2dR5R1A1S2eA3S0SbfQ40A1S49R5R2A2S49R4R2A2A3F_;Fv;S0S2dS14fR5R2A2S2eA3S0S2dS192R3A1S2eA3S0S2fS3eS3eA2S5cR5R4A2S5cR6R4A2A3F_;F_;F_;Fo;Frho';Frho;Ff;").
Proof.
  intros f rho rho' o Hv Ho Hn.
  unfold obj_vars_all in Ho. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho Hhi]. apply andb_prop in Ho as [Hbase Hlo].
  unfold obj_nolist in Hn. apply andb_prop in Hn as [Hn _]. apply andb_prop in Hn as [Hn _]. apply andb_prop in Hn as [Hn Nhi]. apply andb_prop in Hn as [Nbase Nlo].
  unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite (eval_agree_vars_nl f rho rho' _ Hv Hbase Nbase), (eval_agree_vars_nl f rho rho' _ Hv Hlo Nlo), (eval_agree_vars_nl f rho rho' _ Hv Hhi Nhi).
  reflexivity.
Qed.

Definition fG (u : positive) : bool := ltac2:(tb__ "0|0|
S3dS3dS1a2Vu;P64A2S1a1Vu;PadA2A2S1a1Vu;PaeA2A2").
Lemma SG_regs_vars : ltac2:(tb__ "0|1|
S0S2dS93S3eS3eS3dS95S3eS8fR1A1S2bS3eZaS2bS3eZbS2bS3eZcS32S3eA1A3A3A3A3S3bS150S18eS4bS190R1A2M0A2S18dG0A1A2A2Lr;SccS38S3eS8eSceU1U1fA2A4A3S2eA3").
Proof. vm_compute. reflexivity. Qed.
Lemma SG_stk_vars : ltac2:(tb__ "0|0|
S0S2dS93S4dS4dS3bS150S18eS64R1A1A2S150S18eS65R1A1A2A2Lc;S18fA3S2eA3").
Proof. vm_compute. reflexivity. Qed.

Lemma pdr_prefix4 (r0 r1 r2 r3 : Z * Z) t : ltac2:(tb__ "0|1|
S1adS2bS2fS3eS3eA2M0Vr0;S2bG0Vr1;S2bG0Vr2;S2bG0Vr3;Vt;A3A3A3A3A1S1adS2bG0Vr0;S2bG0Vr1;S2bG0Vr2;S2bG0Vr3;S32G0A1A3A3A3A3A1F_;").
Proof.
  cbn. intros (A & B & C & _).
  apply Forall_cons_iff in A as [A1 A]. apply Forall_cons_iff in A as [A2 A]. apply Forall_cons_iff in A as [A3 _].
  apply Forall_cons_iff in B as [B1 B]. apply Forall_cons_iff in B as [B2 _]. apply Forall_cons_iff in C as [C1 _].
  repeat split.
  - constructor; [exact A1|]. constructor; [exact A2|]. constructor; [exact A3|]. constructor.
  - constructor; [exact B1|]. constructor; [exact B2|]. constructor.
  - constructor; [exact C1|]. constructor.
  - constructor.
Qed.

Section G.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S84Z0Vreq;A2S84S85Vreq;Sa8A2Sa4Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs;Vsc;A2S35S98Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S7eS7dVX;Vs;Vsc;A3S35S98Vm0;A2S2bS98Vm0;Vrest;A3A3").
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (@U.Mal_aslot__G1.Mal_aslot_I.mam s m0).
Local Abbreviation mptr_key := (@U.Mal_aslot__G1.Mal_aslot_I.mptr_key s X U sc HI Hsc m0 Hhd).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S199S15aVX;S36S2fS98S3eA2A1VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S20S1S1S84Z0M0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S9cS8Vs;Vm0;R1A3M2A1A3S2S0S3eSa5G2A1G0A3A1S0S3eS1cVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S9cS8Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§1§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rw1 := (§1§ U.Mal_aslot__G1.Mal_aslot_I.rw1).
Local Abbreviation rho1 := (§1§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Notation "§2§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation rw1_low := (§2§ U.Mal_aslot__G1.Mal_aslot_I.rw1_low).
Local Abbreviation zr1 := (§1§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zr1_12 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zr1_12).
Local Abbreviation zr1_13 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_13 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc Hreq m0 Hbnc Hgd).
Local Abbreviation zr1_173 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zr1_173).
Local Abbreviation zr1_174 := (§2§ U.Mal_aslot__G1.Mal_aslot_I.zr1_174).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sc0Q40S49Vrho;PaA2A2M0A2S0S3eS89G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S174Z40Sc0Q40S49Vrho;PfA2A2A2M0S8aS186Z0A1A1A2S84S8aS8cZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S84S15eVL;A1S85Sc0Q40M0S49Vrho;PaA2A2S174Z40Sc0G0S49Vrho;PfA2A2A2A2A2").
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;Vrd0;S13dSb8VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SbfQ40A1S2dF_;Vwok0;S13eSb8VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z60A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ecR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z20A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ccR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S20S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S22VL;S9bS8Vs;Vm0;R1A3A1A2Z8A2A2A3S35G1Sc1G0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S85Z5a3d0Z369A2Vsc;A2A2A3S35G1Sc1G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S15dS15bVrd0;SbfQ40A1S2eL_;A2S15cS15aA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S15bS13dSb8VmW;A2S13eSb8VmW;A2A2").
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§1§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§1§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S0S3eVbnc;SacS87Vsc;G0A2Sa2Vs;A1A2A3F_;").
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S19aSb8VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cS114A1S115OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Notation "§3§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW) (at level 10, h__ global).
Local Abbreviation rw_agrees := (§3§ U.Mal_aslot__G2.Mal_aslot_W.rw_agrees).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation objs_matchb_holds := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb_holds).
Local Abbreviation objs_matchb_ranges := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb_ranges).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Abbreviation NREL := (@U.Mal_aslot__G2.Mal_aslot_W.NREL).
Local Abbreviation rmF := (§3§ U.Mal_aslot__G2.Mal_aslot_W.rmF).
Local Abbreviation HfrF := (§3§ U.Mal_aslot__G2.Mal_aslot_W.HfrF).
Local Abbreviation m' := (@U.Mal_aslot__G2.Mal_aslot_W.m').
Local Abbreviation minvI' := (@U.Mal_aslot__G2.Mal_aslot_W.minvI' s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val).
Local Abbreviation rho' := (@U.Mal_aslot__G2.Mal_aslot_W.rho' rho).
Local Abbreviation freg_sv_ok := (@U.Mal_aslot__G2.Mal_aslot_W.freg_sv_ok sc rho bnc gd Hsc Hbnc Hgd).
Local Abbreviation kept := (@U.Mal_aslot__G2.Mal_aslot_W.kept s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Hm_sct Hm_ctz Hbnc_val).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Section ReabG.
Variables (tr : list event) (md : Model) (msF : machine_state) (rhoF : valuation).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;VmW;S59Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S116Vvm;S117Vmd;A1A3").
Hypothesis HagF : agrees rhoW rhoF.
Variables (SF : sstate) (objsF : list sobj) (dsF dsC : list od).
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cVSF;A1S2bS45S162S18fA1VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S2dS15fVobjsF;VdsF;A2S2eA3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S4fSb8VrhoF;VSF;S33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1S165VdsF;A1A3S2eA3").
Hypothesis HdsF_sem : ltac2:(tb__ "0|0|
S0S2dS93S5S161VdsF;A3S2eA3").
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S5S92S5R1VdsF;A3S3S23Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S92S5R2VdsC;A3A2F_;Fd;").
Hypothesis Hent_hold : ltac2:(tb__ "0|0|
S5S92S5R1VdsF;A3S23Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S56Sb8VrhoW;S180Vms;VmW;A2SfR3A1A4F_;F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs';A4").
Hypothesis HXr' : xraw X s'.
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S112Vs;Vs';Vlocs;A3").
Hypothesis HdsC : ltac2:(tb__ "0|0|
S5S92S5R1VdsC;A3S1S92S5R2VdsF;A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Vs';R2A11S160Vsc;R2A2A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|2|
S73S92S73R1Vlocs;A3S4S5S5S1S92S5R1VdsC;A3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M0A3S79VL;R3A2M1A2S86G1S37S3eS3eG0A3A2A2A2Ld;A2F_;Fl;").

Hypothesis HSF_pc : ss_pc SF = 0x2144c.
Hypothesis HSF_regs : regsG_okb SF = true.
Hypothesis HSF_fregs : ltac2:(tb__ "0|0|
S0S2cS41A1S54VSF;A1Sb9A3").
Hypothesis HSF_fcsr : ltac2:(tb__ "0|0|
S0S57S53VSF;A1S51A3").
Hypothesis HSF_resv : ss_resv SF = None.
Hypothesis HdsF_head : ltac2:(tb__ "0|1|
S4S2cS5A1M0G0S0G0VdsF;S2bS5S11S2bS5S12S2bS5SdS43Z0A1A1R1A3A3A3A3Lt;A2").
Lemma HdsF_fixed : ltac2:(tb__ "0|0|
S1S92S5S11VdsF;A3S1S92S5S12VdsF;A3S92S5SdS43Z0A1A1VdsF;A3A2A2").
Proof using HSF_match HdsC HdsF_ent HdsF_head HdsF_sem HdsF_vars Hent_hold. drop_sp. destruct HdsF_head as [t ->]. split; [left | split; [right; left | right; right; left]]; reflexivity. Qed.
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4fSb8Vrho;S188S187A1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PdA2A2Vreq;A3").
Hypothesis Htier : ltac2:(tb__ "0|0|
S84S174Z40Sc0Q40S49Vrho;S1a3A2A2A2S8aS186S8eS189Vsc;A1A1A1A1A2").
Hypothesis Htp : tp_ok C_U rho.
Hypothesis HKc : Kc tr md.

Hypothesis Hhd' : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs';Vsc;A2S36S98A1A3").
Hypothesis Hheads' : ltac2:(tb__ "0|0|
S3eS84Z0R1A2S2S0S3eR2Vsc;A3A1S0S31S98A1S74Vs';R3A2S74Vs;R3A2A3F_;F_;Fc;").
Hypothesis Hub' : ub_same s s'.
Hypothesis Hta0 : ltac2:(tb__ "0|1|
S0Sa1S99S2fS3eS99A2M0A2Sa7Vsc;Vs;A2Sa0S99G0S33S3eS99Z0Vs';A4A3A3").

Let mG : word -> option byte := ltac2:(tb__ "0|0|
S166VmsF;VrhoF;VdsF;A3").

Definition rwG (j : positive) : word := ltac2:(tb__ "0|3|
S2dSbfQ40A1L_;M0S8dS40Vj;A1M1Z64A2S49Vrho;Vj;A2G0S3bS91Zc8M2G1A2S8dG1Ze8A2A2S60VrhoF;S4bVSF;S87G1G2A2A2A2S49VrhoF;Vj;A2X2dx2X2dx2").
Definition rhoG : valuation := ltac2:(tb__ "0|0|
S66S19fS68Vrho;A1VmG;A3").

Lemma rwG_low j : ltac2:(tb__ "0|0|
S1a0Vj;P64A2S0SbfQ40A1S19fVj;A1S49Vrho;Vj;A2A3F_;").
Proof using Hbnc Hgd Hsc. drop_sp. intros Hj. unfold rwG. replace (Z.pos j <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma agree_vals_rhoG : ltac2:(tb__ "0|0|
S153SbdVrho;S19eA3").
Proof using Hbnc Hgd Hsc. drop_sp. split; [|reflexivity]. intros j Hj. cbn [rw rhoG]. symmetry. apply rwG_low. exact Hj. Qed.

Lemma rwF_low_all j : ltac2:(tb__ "0|0|
S1a0Vj;P64A2S0SbfQ40A1S49VrhoF;Vj;A2S49Vrho;Vj;A2A3F_;").
Proof using HagF Hbnc Hgd Hreq Hreq_rho Hsc Hsc_rho Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hj. rewrite (rw_agrees rhoF j HagF) by (unfold below200; apply Pos.ltb_lt; lia).
  destruct (Pos.eq_dec j 12) as [->|N12].
  { rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 12%positive)), Hsc_rho. apply bv_eq. change (bv_unsigned (rw1 12%positive)) with (zr1 12%positive). rewrite zr1_12, u64 by (pose proof Hsc; lia). reflexivity. }
  destruct (Pos.eq_dec j 13) as [->|N13].
  { rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 13%positive)), Hreq_rho. apply bv_eq. change (bv_unsigned (rw1 13%positive)) with (zr1 13%positive).
    pose proof (MallocWfArith.class_size_bounds sc ltac:(pose proof Hsc; lia)). pose proof Hreq. unfold IB in *. rewrite zr1_13, u64 by lia. reflexivity. }
  apply rw1_low; assumption.
Qed.

Lemma rhoG_F u : ltac2:(tb__ "0|0|
S0S2dS18eVu;A1S2eA3S0SbfQ40A1S49VrhoF;Vu;A2S49S19eVu;A2A3F_;").
Proof using HagF Hbnc Hgd Hreq Hreq_rho Hsc Hsc_rho Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hu. unfold fG in Hu. cbn [rw rhoG]. unfold rwG.
  destruct (Z.pos u <? 100) eqn:E.
  - apply Z.ltb_lt in E. apply rwF_low_all. lia.
  - apply Bool.orb_prop in Hu as [Hu|Hu]; [apply Bool.orb_prop in Hu as [Hu|Hu]|].
    + apply Pos.ltb_lt in Hu. apply Z.ltb_ge in E. lia.
    + apply Pos.eqb_eq in Hu. subst u. reflexivity.
    + apply Pos.eqb_eq in Hu. subst u. reflexivity.
Qed.

Lemma HOF_G : ltac2:(tb__ "0|0|
ScdS45S56Sb8VrhoF;VmsF;A3S2bS45S162S18fA1S165VdsF;A1A3A3").
Proof using HSF_match HSF_objs HsmF. drop_sp.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _) & _). cbn [fst snd cfg_ms] in Hall.
  rewrite HSF_objs in Hall. apply Forall_cons_iff in Hall as [H1 H2]. constructor; [exact H1|].
  exact (objs_matchb_holds rhoF msF objsF dsF HSF_match H2).
Qed.
Lemma HOF_Gd d : ltac2:(tb__ "0|0|
S92S5Vd;VdsF;A3S56Sb8VrhoF;VmsF;SfVd;A1A4F_;").
Proof using HSF_match HSF_objs HsmF. drop_sp. intros Hd. apply (proj1 (Forall_forall _ _) HOF_G). right. unfold NREL. apply in_map. exact Hd. Qed.

Lemma obj_G_transfer o : ltac2:(tb__ "0|0|
S0S2dS14fS18eVo;A2S2eA3S0S2dS192Vo;A1S2eA3S56Sb8VrhoF;VmsF;Vo;A4S56Sb8S19eVmsF;Vo;A4F_;F_;F_;").
Proof using HagF Hbnc Hgd Hreq Hreq_rho Hsc Hsc_rho Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hv Hn Ho. eapply (obj_holds_agree_vars_nl segsU fG rhoF rhoG); [apply rhoG_F | exact Hv | exact Hn | exact Ho].
Qed.

Theorem smatch_G : ltac2:(tb__ "0|0|
S4fSb8S19eS190S33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A4").
Proof using EmW Erd Evm Ewok HMI HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_regs HSF_resv HagF Hbnc Hbnc_rd Hbnc_val Hbytes_rd HdsC HdsF_ent HdsF_head HdsF_sem HdsF_vars Hent_hold Hgd Hgd_holds Hhd Hhd' Hheads' Hlocs Hm_ctz Hm_sct Hreq Hreq_rho Hsc Hsc_rho HsmF Hsm_pre Hsp Hta0 Htier Rg. try clear Hsp_high. try clear Hdepth.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, HSF_pc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    assert (Hin : In (bv_unsigned r) (map Z.of_nat (seq 1 31))) by (apply in_map_iff; exists (Z.to_nat (bv_unsigned r)); split; [lia|]; apply in_seq; lia).
    pose proof (proj1 (forallb_forall _ _) HSF_regs _ Hin) as P1. pose proof (proj1 (forallb_forall _ _) SG_regs_vars _ Hin) as P2. cbn beta in P1, P2.
    destruct (existsb (Z.eqb (bv_unsigned r)) [10; 11; 12]) eqn:E3.
    -
      cbn [existsb orb] in E3.
      assert (E : reg_sv SG (bv_unsigned r) = SVar (Z.to_pos (200 + bv_unsigned r)) /\ 10 <= bv_unsigned r <= 12).
      { destruct (Z.eqb_spec (bv_unsigned r) 10) as [->|]; [split; [reflexivity|lia]|].
        destruct (Z.eqb_spec (bv_unsigned r) 11) as [->|]; [split; [reflexivity|lia]|].
        destruct (Z.eqb_spec (bv_unsigned r) 12) as [->|]; [split; [reflexivity|lia]|]. cbn in E3. discriminate. }
      destruct E as [-> Rr]. cbn [eval rhoG rw]. unfold rwG.
      replace (Z.pos (Z.to_pos (200 + bv_unsigned r)) <? 100) with false by (symmetry; apply Z.ltb_ge; lia).
      replace ((200 <=? Z.pos (Z.to_pos (200 + bv_unsigned r))) && (Z.pos (Z.to_pos (200 + bv_unsigned r)) <? 232))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (Z.pos (Z.to_pos (200 + bv_unsigned r)) - 200) with (bv_unsigned r) by lia. reflexivity.
    - cbn [orb] in P1, P2. apply sv_eqb_sound in P1. rewrite P1. apply andb_prop in P2 as [P2 P3].
      apply (eval_agree_vars_nl fG rhoF rhoG); [apply rhoG_F | exact P2 | exact P3]. }
  split.
  {   intros r. rewrite (Hf r). unfold freg_sv. rewrite HSF_fregs. change (ss_fregs SG) with pre_fregs.
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    destruct (freg_sv_ok (bv_unsigned r) ltac:(lia)) as (vv & _ & E2 & Hvv). rewrite E2.
    cbn [eval rhoG rw]. rewrite rwG_low by lia. apply rwF_low_all. lia. }
  split. { rewrite HSF_fcsr in Hc. exact Hc. }
  split. { unfold resv_match in *. rewrite HSF_resv in Hv. cbn [ss_resv SG]. exact Hv. }
  split.
  { destruct HdsF_fixed as (Dg & Dd & Da).
    split; [|split].
    -
      constructor. { apply obj_G_transfer; [vm_compute; reflexivity | vm_compute; reflexivity |]. apply (proj1 (Forall_forall _ _) HOF_G). left. reflexivity. }
      constructor. { apply obj_G_transfer; [reflexivity | reflexivity |]. exact (HOF_Gd _ Dg). }
      constructor. { apply obj_G_transfer; [reflexivity | reflexivity |]. exact (HOF_Gd _ Dd). }
      constructor. { apply obj_G_transfer; [reflexivity | reflexivity |]. exact (HOF_Gd _ Da). }
      constructor.
    -
      assert (RG : forall o, In o [oStkG; oGot; oGuard; oAct0] -> obj_range rhoG o = obj_range rhoF o).
      { intros o Ho. apply (obj_range_agree_vars_nl fG rhoF rhoG); [apply rhoG_F | |]; destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. }
      apply pairwise_disjoint_pdr. erewrite map_ext_in by exact RG.
      pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _). cbn [fst snd cfg_ms] in Hpd.
      rewrite HSF_objs in Hpd. apply pairwise_disjoint_pdr in Hpd.
      cbn [map] in Hpd. rewrite (objs_matchb_ranges rhoF objsF dsF HSF_match) in Hpd.
      destruct HdsF_head as [t Et]. rewrite Et in Hpd. cbn [map] in Hpd.
      change [oStkG; oGot; oGuard; oAct0] with [oStkF stkcG; obj_of OD_got; obj_of OD_guard; obj_of (OD_act (SLit 0))]. cbn [map].
      exact (pdr_prefix4 _ _ _ _ _ Hpd).
    -
      intros a Ha. cbn [rm rhoG]. unfold mG.
      destruct (in_ranges_dec rhoF (NREL dsF) a) as [IN|OUT].
      + unfold m'. rewrite (release_in _ _ _ _ IN). reflexivity.
      + unfold m'. rewrite (release_out _ _ _ _ OUT). rewrite (rmF rhoF EmW HagF).
        apply (HfrF tr md msF rhoF EmW HagF SF stkcG objsF dsF HSF_objs HSF_match HsmF).
        constructor.
        * apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS |- *.
          change (oStkF stkcG) with oStkG. rewrite <- (obj_range_agree_vars_nl fG rhoF rhoG oStkG rhoG_F ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). exact HaS.
        * apply Forall_forall. intros o Ho. cbn zeta. intros R. apply OUT. exists o. auto. }

  unfold SG. cbn [ss_facts]. unfold factsG.
  assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rhoG f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rhoG f agree_vals_rhoG Hb) Hh). }
  pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts Pre_as] in HF0.
  apply Forall_app. split.
  - apply Forall_forall. intros f Hf0. apply AGR; [|exact (proj1 (Forall_forall _ _) HF0 f Hf0)].
    cbn in Hf0. decompose [or] Hf0; subst; try reflexivity; contradiction.
  - constructor; [|constructor]. cbn [SymState.holds eval rhoG rw]. rewrite rwG_low by lia. rewrite (u64 47) by lia. pose proof Hsc. lia.
Qed.

Theorem post_G : ltac2:(tb__ "0|0|
S191VX;VU;S156Vs;VL;A2VKc;Vrho;S33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A6").
Proof using EmW Erd Evm Ewok HI HI' HKc HMI HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_regs HSF_resv HXr HXr' HagF Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdelta Hdepth HdsC HdsF_ent HdsF_head HdsF_sem HdsF_vars Hent_hold Hgd Hgd_holds Hhd Hhd' Hheads' Hlocs Hm_ctz Hm_sct Hmaskv Hreq Hreq_rho Hrom Hsc Hsc_rho HsmF Hsm_pre Hsp Hsp_high Hspanv Hta0 Htier Htp Hub' Rg mG.
  unfold GX. cbn [ma_s ma_L]. rewrite Hsc_rho.
  exists (mkMA s' L), rhoG.
  split; [exact agree_vals_rhoG|]. split; [reflexivity|]. split; [exact Hheads'|]. split; [exact Hub'|].
  split; [exact (kept tr md msF rhoF EmW HagF SF dsF HsmF HdsF_vars s')|].
  split; [exact Hhd'|].
  split. { cbn [rw rhoG]. unfold rwG. cbn. rewrite (rw_agrees rhoF 173%positive HagF eq_refl). apply bv_eq. change (bv_unsigned (rw1 173%positive)) with (zr1 173%positive). rewrite zr1_173, u64; [reflexivity|]. cbn. lia. }
  split; [exact Hta0|].
  split; [destruct Hdelta as (_ & _ & _ & _ & Dregs & _); exact Dregs|].
  split. { cbn [rw rhoG]. unfold rwG. cbn. rewrite (rw_agrees rhoF 174%positive HagF eq_refl). change (bv_unsigned (rw1 174%positive)) with (zr1 174%positive). rewrite zr1_174.
           rewrite <- EmW. pose proof Hgd_holds as HG. rewrite Erd in HG. exact HG. }
  split; [exact smatch_G|].

  unfold J_as_pre. cbn [w_tr w_cfg cfg_model fst snd ma_s].
  split. { unfold MInvIR. cbn [rm rhoG]. unfold mG. rewrite <- Evm.
           exact (minvI' tr md msF rhoF EmW HagF SF stkcG objsF dsF dsC HSF_objs HSF_match HsmF HdsF_vars HdsF_sem HdsF_ent Hent_hold s' None locs HI' HXr' Hdelta HdsC Hlocs). }
  split; [exact HXr'|]. split; [exact HKc|].
  cbn [rw rhoG]. rewrite !rwG_low by (unfold V_DEPTH; lia). rewrite Hsc_rho, Hreq_rho. pose proof Hsc. pose proof Hreq.
  split; [repeat split; try lia; try exact Htier|].
  split. {   unfold tp_ok. cbn [rw rhoG]. rewrite rwG_low by lia. exact Htp. }

  split. { intros Hinit. exfalso.
  destruct Hdelta as (_ & _ & Dinit & _ & _ & _ & Dkeys & _). rewrite Dinit in Hinit.
  destruct (inv_ctx HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CI & _). destruct (CI Hinit) as (E0 & _).
  pose proof (mptr_key MM0) as KM. unfold keys in KM. rewrite E0 in KM. exact KM. }

  unfold top_high, V_DEPTH. cbn [ma_L rw rhoG]. rewrite !rwG_low by lia. exact Hsp_high.
Qed.
End ReabG.
End G.
End Mal_aslot_G.

Module Mal_aslot_VR1ns.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VR1ns.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S84Z0Vreq;A2S84S85Vreq;Sa8A2Sa4Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs;Vsc;A2S35S98Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S7eS7dVX;Vs;Vsc;A3S35S98Vm0;A2S2bS98Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§4§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§4§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§4§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§4§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§4§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§4§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§4§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls1 := (@U.Mal_aslot__G1.Mal_aslot_I.cls1 s X sc Hsc m0 rest Rg).
Local Notation "§5§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§5§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§5§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S199S15aVX;S36S2fS98S3eA2A1VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S20S1S1S84Z0M0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S9cS8Vs;Vm0;R1A3M2A1A3S2S0S3eSa5G2A1G0A3A1S0S3eS1cVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S9cS8Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§6§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§6§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§7§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§7§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§7§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§7§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§8§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§8§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§8§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_bits := (§8§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§7§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sc0Q40S49Vrho;PaA2A2M0A2S0S3eS89G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S174Z40Sc0Q40S49Vrho;PfA2A2A2M0S8aS186Z0A1A1A2S84S8aS8cZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S84S15eVL;A1S85Sc0Q40M0S49Vrho;PaA2A2S174Z40Sc0G0S49Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§9§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§9§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§10§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§8§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Local Abbreviation zf_tabidx := (§10§ U.Mal_aslot__G1.Mal_aslot_I.zf_tabidx).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;Vrd0;S13dSb8VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SbfQ40A1S2dF_;Vwok0;S13eSb8VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z60A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ecR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z20A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ccR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S20S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S22VL;S9bS8Vs;Vm0;R1A3A1A2Z8A2A2A3S35G1Sc1G0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S85Z5a3d0Z369A2Vsc;A2A2A3S35G1Sc1G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S15dS15bVrd0;SbfQ40A1S2eL_;A2S15cS15aA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S15bS13dSb8VmW;A2S13eSb8VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§11§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§11§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§4§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§12§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§12§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp).
Local Abbreviation od_ok_meta_entry := (§8§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§8§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§8§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S0S3eVbnc;SacS87Vsc;G0A2Sa2Vs;A1A2A3F_;").
Local Notation "§13§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§13§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§7§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S19aSb8VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cS114A1S115OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§14§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§14§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Notation "§15§ h__" := (h__ Kc RF GF TR RR) (at level 10, h__ global).
Local Abbreviation tr_seq := (§15§ U.Mal_aslot__G2.Mal_aslot_W.tr_seq).
Local Abbreviation tr_ex := (§15§ U.Mal_aslot__G2.Mal_aslot_W.tr_ex).
Local Abbreviation tr_pure := (§15§ U.Mal_aslot__G2.Mal_aslot_W.tr_pure).
Local Abbreviation tr_disj := (§15§ U.Mal_aslot__G2.Mal_aslot_W.tr_disj).
Local Notation "§16§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§16§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§17§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§17§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation setp := (@U.Mal_aslot__G2.Mal_aslot_W.setp).
Local Abbreviation keys_distinct := (@U.Mal_aslot__G2.Mal_aslot_W.keys_distinct).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§18§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§18§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§4§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§19§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§19§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd).
Local Notation "§20§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§20§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§21§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§21§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§22§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§22§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§22§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§19§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§16§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§23§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§23§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§23§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§23§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Notation "§24§ h__" := (h__ sc rho bnc gd Hsc Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation active_hd_set_hd := (§24§ U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§5§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§5§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§5§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§6§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation xraw_upd_meta_ptr := (§5§ U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta_ptr).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).
Local Abbreviation e_size := (@U.Mal_aslot__G9.Mal_aslot_L.e_size).
Local Abbreviation e_span0 := (@U.Mal_aslot__G9.Mal_aslot_L.e_span0).
Local Abbreviation e_a60 := (@U.Mal_aslot__G9.Mal_aslot_L.e_a60).
Local Abbreviation e_a40 := (@U.Mal_aslot__G9.Mal_aslot_L.e_a40).
Local Abbreviation e_byteS := (@U.Mal_aslot__G9.Mal_aslot_L.e_byteS).
Local Abbreviation e_byteL := (@U.Mal_aslot__G9.Mal_aslot_L.e_byteL).
Local Abbreviation e_maskG := (@U.Mal_aslot__G9.Mal_aslot_L.e_maskG).
Local Abbreviation e_freedG := (@U.Mal_aslot__G9.Mal_aslot_L.e_freedG).
Local Abbreviation size_range := (§24§ U.Mal_aslot__G9.Mal_aslot_L.size_range).
Local Abbreviation aidx_range := (@U.Mal_aslot__G9.Mal_aslot_L.aidx_range s sc rho byM0 byA byB byC byP bnc gd Hsc m0 Hbytes Hbnc Hgd).
Local Notation "§25§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hspanv Hsp) (at level 10, h__ global).
Local Abbreviation ze_byteS := (§25§ U.Mal_aslot__G9.Mal_aslot_L.ze_byteS).
Local Abbreviation ze_byteL := (§10§ U.Mal_aslot__G9.Mal_aslot_L.ze_byteL).
Local Abbreviation ze_maskG := (§8§ U.Mal_aslot__G9.Mal_aslot_L.ze_maskG).
Local Abbreviation ze_freedG := (§10§ U.Mal_aslot__G9.Mal_aslot_L.ze_freedG).
Local Abbreviation e_last1 := (@U.Mal_aslot__G9.Mal_aslot_L.e_last1).
Local Notation "§26§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hspanv Hsp mW K) (at level 10, h__ global).
Local Abbreviation cnt_lt_of := (§26§ U.Mal_aslot__G9.Mal_aslot_L.cnt_lt_of).
Local Abbreviation cnt_ge_of := (§26§ U.Mal_aslot__G9.Mal_aslot_L.cnt_ge_of).
Local Abbreviation eq0_of := (§16§ U.Mal_aslot__G9.Mal_aslot_L.eq0_of).
Local Abbreviation span_cnt_ge2 := (§24§ U.Mal_aslot__G9.Mal_aslot_L.span_cnt_ge2).
Local Abbreviation rename_chk := (@U.Mal_aslot__G9.Mal_aslot_L.rename_chk).
Local Abbreviation setsB := (@U.Mal_aslot__G9.Mal_aslot_L.setsB).
Local Abbreviation setsX := (@U.Mal_aslot__G9.Mal_aslot_L.setsX).
Local Abbreviation LINV := (@U.Mal_aslot__G9.Mal_aslot_L.LINV sc).
Local Notation "§27§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Hbnc_val Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation span_loop_sound := (§27§ U.Mal_aslot__G9.Mal_aslot_L.span_loop_sound).
Local Abbreviation setsA := (@U.Mal_aslot__G9.Mal_aslot_L.setsA).
Local Notation "§28§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp mW K) (at level 10, h__ global).
Local Abbreviation loop_entry := (§28§ U.Mal_aslot__G9.Mal_aslot_L.loop_entry).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;VmW;S59Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S116Vvm;S117Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cS114A1M0S115VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S115R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4fSb8Vrho;S188S187A1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 1%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S3eSadS8Vs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S2S0S3eSa3S8Vs;Vm0;S6A3A1Z0A3A1").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S3eSa3S8Vs;Vm0;S6A3M0A1SabS9fG0A1A1A3A1").
Hypothesis HVact : maskA MM0 = 0.

Hypothesis HVpart : ltac2:(tb__ "0|0|
S86S87Z1000SafA2S88Sa4Vsc;A1S85S9cS8Vs;Vm0;S6A3A1Z2A2A2A2").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Vs;S9Vm0;A1A2S35S9aS9dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls1 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls1 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.
Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition am1_M0 : ameta := (mam MM0).
Definition s1V : astate := ltac2:(tb__ "0|0|
S113Vsc;S35S98SaVs;Vm0;A2A2Vs;A3").
Definition s2V : astate := s1V.

Definition AM3 : ameta := ltac2:(tb__ "0|0|
Sb1S87S13fSf2A1Z1A2Sf2A2").
Definition s3V : astate := ltac2:(tb__ "0|0|
S1aaS9Vm0;A1S9dSf4A1S107A3").

Definition cnt1 : Z := ltac2:(tb__ "0|1|
Sb2U12cS85S9cS8Vs;Vm0;S6A3A1M0Z2A2S173Vsc;G0A2Sa4Vsc;A1A4").

Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S3eVmaskv;S140Sf4A1A3").
Hypothesis Hsv : spanv = cnt1.
Lemma K1 : ltac2:(tb__ "0|0|
S0S2cS98A1S78Sf8A1S78Vs;A1A3"). Proof using . unfold s1V. apply keys_set_hd. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sf8S21Vs;Vm0;S6A3A2S35S9aS9dSf2A1A2A3").
Proof using HI Hhd Hsc. drop_sp. unfold s1V, am1_M0. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma K3 : ltac2:(tb__ "0|0|
S0S2cS98A1S78Sf6A1S78Vs;A1A3"). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite keys_upd_In; [exact K1|]. rewrite K1. exact (mptr_key MM0). Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. rewrite K3. exact ND. Qed.
Lemma MT3_other q : ltac2:(tb__ "0|0|
S2S0S98Vq;S9Vm0;A1A3A1S0S31S9aA1S75Sf6Vq;A2S75Sf8Vq;A2A3F_;"). Proof using . intros Hq. unfold s3V, s2V. apply MT_upd_other. exact Hq. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S2cS3eA1Sa2Sf6A1Sa2Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HXr. unfold s1V. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. change pM0 with (mptr MM0). apply xraw_upd_meta_ptr. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd1 : ltac2:(tb__ "0|0|
S0S31S98A1S74Sf8Vsc;A2S35S98S9Vm0;A1A2A3").
Proof using HI Hbnc Hgd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. replace (Some pM0) with (Some pA) by (f_equal; solve_link). apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S31S98A1S74Sf6Vsc;A2S35S98S9Vm0;A1A2A3"). Proof using HI Hbnc Hgd Hr Hsc Hsp Rg. unfold s3V, s2V. rewrite active_hd_upd_meta. exact hd1. Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0Sa1S99S2fS31S98A1M0S99A2M1A2S146Vsc;S9Vm0;A1Vam0;Vs;A4Sa0S99G1S33G0S99S35S98SaVs;Vm0;A2A2Sf8A4A3A3").
Proof using HI HVf0 Hhd Hsc. drop_sp. unfold s1V. replace (Some pA) with (am_next am0) by (exact (am_next_mam MM0)). apply step1_rot. exact HVf0. Qed.
Lemma E_m1 : ltac2:(tb__ "0|0|
S0S98SaVs;Vm0;A2S21Vs;Vm0;S6A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sf8SaVs;Vm0;A2A2S35S9aS9dSf2A1A2A3"). Proof using HI Hhd Hr Hsc Rg. rewrite E_m1. exact MT1_M0. Qed.
Lemma S2 : ltac2:(tb__ "0|1|
S0Sa1S99S2fS98S99A2M0A2S147Vsc;SaVs;Vm0;A2Sf2Sf8A4Sa0S99G0S33S98S99S9Vm0;A1S107A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V. rewrite E_m1. apply step2_stay. unfold am1_M0. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S31S9aA1S75S107S9Vm0;A1A2S35S9aS9dSf2A1A2A3"). Proof using HI Hhd Hsc. unfold s2V. exact MT1_M0. Qed.
Lemma next2 : ltac2:(tb__ "0|0|
S0S31S98A1SaeSf2A1S35S98S9Vm0;A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold am1_M0. cbn [am_next am_set_links]. first [reflexivity | rewrite (am_next_mam MM0); f_equal; cbn [mptr]; solve_link]. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0Sa1S99S2fS98S99A2M0A2S148Vsc;S9Vm0;A1M1Sf2S107A4Sa0S99G0S33S98S99G1Sf6A4A3A3").
Proof using HI HVact Hhd Hr Hsc Rg. drop_sp. unfold s3V, AM3. apply (step3_span s2V sc pM0 am1_M0); [unfold am1_M0; cbn [am_freed am_aidx am_set_links]; exact HVact | exact next2]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sf6S9Vm0;A1A2S35S9aS9dSf4A1A2A3"). Proof using . unfold s3V. apply MT_upd_same. Qed.
Lemma Hav3 : am_avail AM3 = 0. Proof using HVa0. unfold AM3, am1_M0. cbn [am_avail am_set_aidx am_set_links]. exact HVa0. Qed.
Lemma sc_am2 : ltac2:(tb__ "0|0|
S0S3eSa9Sf2A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_M0. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MM0))). Qed.
Lemma aidx_am2 : ltac2:(tb__ "0|0|
S0S3eS9cSf2A1S9cS8Vs;Vm0;S6A3A1A3"). Proof using . reflexivity. Qed.
Lemma last_am2 : ltac2:(tb__ "0|0|
S0S3eS9fSf2A1S9fS8Vs;Vm0;S6A3A1A3"). Proof using . reflexivity. Qed.
Lemma freed_am2 : ltac2:(tb__ "0|0|
S0S3eSa3Sf2A1Sa3S8Vs;Vm0;S6A3A1A3"). Proof using . reflexivity. Qed.

Lemma span_cnt_eq : ltac2:(tb__ "0|1|
S0S3eS13fSf2A1S2dS3eL_;S8dS85S9fS8Vs;Vm0;S6A3A1Z1A2M0SfcA2G0SfcX2dx2A3").
Proof using HI Hhd Hsc. drop_sp. unfold span_cnt, cnt1, span0_of. rewrite sc_am2, aidx_am2, last_am2. reflexivity. Qed.
Lemma cnt1_ge : ltac2:(tb__ "0|0|
S84S85S9cS8Vs;Vm0;S6A3A1Z2A2SfcA2"). Proof using . unfold cnt1. apply span_loop_ge. Qed.
Lemma last_R : ltac2:(tb__ "0|2|
S1S84S9cS8Vs;Vm0;S6A3M0A1S9fG0A1M1A2S84G1Z1fA2A2"). Proof using HI HMI Hbnc Hgd Hhd Hr Hsc rho. pose proof (mem_R MM0) as (_ & _ & R3 & R4 & _). lia. Qed.
Lemma cnt_S : ltac2:(tb__ "0|0|
S86SfcS85S9fS8Vs;Vm0;S6A3A1Z1A2A2S0S3eS13fSf2A1SfcA3F_;").
Proof using HI Hbnc Hgd Hhd Hr Hsc rho. drop_sp. intros H. rewrite span_cnt_eq. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma cnt_L : ltac2:(tb__ "0|1|
S84S85S9fS8Vs;Vm0;S6A3A1Z1A2M0SfcA2S0S3eS13fSf2A1G0A3F_;").
Proof using HI Hbnc Hgd Hhd Hr Hsc rho. drop_sp. intros H. rewrite span_cnt_eq. destruct (Z.ltb_spec (am_last (mam MM0) + 1) cnt1); lia. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S3eS140Sf4A1S90Sa3S8Vs;Vm0;S6A3A1SabS87S13fSf2A1Z1A2A1A2A3"). Proof using . reflexivity. Qed.
Lemma HVmask3 : t_mask AM3 <> 0.
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_M0 pM0 s2V am1_M0 pM0 s3V AM3 S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.
Lemma maskS_range : ltac2:(tb__ "0|1|
S1S84Z0S140Sf4A1M0A2S86G0S8cZ2Z20A2A2A2").
Proof using HI HMI HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  rewrite Emask. pose proof (mem_R MM0) as (_ & R2 & R3 & R4 & _). pose proof (span_cnt_ge2 am1_M0) as [G _]; [rewrite aidx_am2; pose proof (aidx_range MM0); lia | rewrite last_am2; pose proof last_R; lia |].
  assert (HO : 0 < ones (span_cnt am1_M0 - 1) < 2 ^ 32).
  { apply ones_u32. rewrite span_cnt_eq. pose proof last_R. pose proof cnt1_ge. destruct (Z.ltb_spec (am_last (mam MM0) + 1) cnt1); lia. }
  split; [apply Z.land_nonneg; lia|]. pose proof (MallocWfSlot.land_le_l (am_freed (mam MM0)) (ones (span_cnt am1_M0 - 1)) ltac:(lia)). lia.
Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S145Sf6S9Vm0;A1Sf4A3").
Lemma taR : ltac2:(tb__ "0|1|
S0Sa1S99S2fS3eS99A2M0A2Sa7Vsc;Vs;A2Sa0S99G0S33S3eS99Sa6S140Sf4A1A1Sf3A4A3A3").
Proof using HI HVa0 HVact HVf0 HVskip Hhd Hr Hsc Rg. drop_sp.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_M0 pM0 s2V am1_M0 pM0 s3V AM3 S1 HM1 S2 HM2 S3 HM3 Hav3 HVmask3).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S3eSa6S140Sf4A1A1Z0A3A1").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. pose proof maskS_range. pose proof (lowbit_range (t_mask AM3) ltac:(pose proof HVmask3; lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S1aeVX;VU;Vs;Vsc;Sa6S140Sf4A1A1Sf3A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S31S98A1S74Sf3Vsc;A2S35S98S9Vm0;A1A2A3"). Proof using HI Hbnc Hgd Hr Hsc Hsp Rg. unfold sR'. rewrite (active_hd_s6 s3V pM0 AM3). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sf3S9Vm0;A1A2S35S9aS9dS141Sf4A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MM0)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S3eSa9Sf4A1Vsc;A3"). Proof using HI Hhd Hsc. unfold AM3. cbn [am_sc am_set_aidx]. exact sc_am2. Qed.

Lemma delta1 : ltac2:(tb__ "0|0|
S112Vs;Sf8S32S73A1A3").
Proof using Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. unfold s1V. replace (Some pA) with (Some pM0) by (f_equal; symmetry; solve_link). change pM0 with m0. rewrite <- Hhd. apply delta_sh_same; [lia|]. left. rewrite Hhd. discriminate. Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S112Sf8Sf6S30S73S2bS73S76S9eS9bSf2A1Z8A2A1S32S73A1A3S111S9Vm0;A1A1A3A3").
Proof using HI Hhd Hsc. drop_sp. unfold s3V, s2V, AM3. apply (delta_su s1V pM0 am1_M0); [exact ND1 | exact HM2 | apply same_shape_aidx]. Qed.
Lemma delta03 : ltac2:(tb__ "0|1|
S112Vs;Sf6S30S73S32S73A1M0S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G0A3S111S9Vm0;A1A1A3A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [exact delta1 | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|1|
S2bS5S11S2bS5S12S2bS5SdS97S1aS6A1A1M0A1S2bS5SbS6G0G0S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S2bS5SeS6S97S2aS6A1A1A2S2bS5S14S2bS5S13S2bS5S10S6S97PaaA1A2S32S5A1A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cS11eA1S2bS45S19SccS5S45SfSf7A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_R1ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

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
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  | |- zholds _ _ (SPUle (SAlu ALU_AND (SAlu ALU_SRL (v (vbits ?x)) (SLit 5)) (SLit 126)) (SLit 94)) => apply (zf_tabidx x)
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S11eA1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hsc Hsp Hsp_high.
  change (ss_facts SA_R1ns) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MM0)) (SLit 32)) (SLit 0)); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPNot (SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0)); SPBranch BC_NE (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MM0))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MM0)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MM0))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MM0))) (SLit 18446744073709551615))) (SLit 0); SPUle (SAlu ALU_AND (SAlu ALU_SRL (v (vbits MM0)) (SLit 5)) (SLit 126)) (SLit 94); SPUle (v (vavail MM0)) (SLit 0)]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S5dZ2126cSbaSb9S51S36S41A1S2bS45S19S32S45A1A3S47S11eA1S122S3aA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4fSb8VrhoW;S110S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4M0A4S4fSb8VrhoW;S11eG0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_R1ns with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S38S3cS5VdsF;A2S3cS5Sf7A2A3S5S92S5R1VdsF;A3S3S23Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S92S5R2S14cSf7VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS5A1M0G0S5S92S5R1S14cR3R2A2A3S92S5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Definition L0 : sstate := lfs LL_R1ns 0 SA_R1ns.
Definition L1 : sstate := lfs LL_R1ns 1 SA_R1ns.
Lemma LL_eq : ltac2:(tb__ "0|0|
S0S2cS183A1S12cS2bS183S185Sf5S184A2S2bS183S185SfbS184A2S32S183A1A3A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma SL_len : ss_lenient SL_R1ns = false. Proof using . reflexivity. Qed.
Lemma SL_next : ltac2:(tb__ "0|0|
S0S3fS5aS11fA1S122A3"). Proof using . reflexivity. Qed.
Lemma SL_regs : ltac2:(tb__ "0|0|
S1S0S41S4bS11fZ5A2S42Pd2A1A3S1S0S41S4bS11fZ10A2S42Pd3A1A3S0S41S4bS11fZeA2S42Pd4A1A3A2A2"). Proof using . repeat split; reflexivity. Qed.
Lemma ren_chk : ltac2:(tb__ "0|0|
S0S2dS171S3fS39S119S2bS3fPd2S2bS3fPd5S2bS3fPd4S2bS3fPd3S32S3fA1A3A3A3A3R1A2A1Lu;Sf5S11fS172Sf5A1A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L0_same : ltac2:(tb__ "0|0|
S1S0S2cS41A1S54S11fA1S54Sf5A1A3S1S0S57S53S11fA1S53Sf5A1A3S1S0S31S41A1S58S11fA1S58Sf5A1A3S0S2cS45A1S4cS11fA1S4cSf5A1A3A2A2A2"). Proof using . repeat split; vm_compute; reflexivity. Qed.
Lemma L0_5 : ltac2:(tb__ "0|0|
S0S41S4bSf5Z5A2S48Sc4S42Pd2A1S16dS6A1A3A3"). Proof using . reflexivity. Qed.
Lemma L0_14 : ltac2:(tb__ "0|0|
S0S41S4bSf5ZeA2S48Sc4S42Pd4A1S43Z1A1A3A3"). Proof using . reflexivity. Qed.
Lemma L0_16 : ltac2:(tb__ "0|0|
S0S41S4bSf5Z10A2S48Sc4S42Pd3A1S16dS6A1A3A3"). Proof using . reflexivity. Qed.
Lemma T0f : ltac2:(tb__ "0|0|
S92S44S4aScaS46Sc9S42Pd3A1S42Pd2A1A3S43Z1000A1A3S47Sf5A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma T1f : ltac2:(tb__ "0|0|
S92S44S4eS4aScaS46Sc9S42Pd3A1S42Pd2A1A3S43Z1000A1A3A1S47SfbA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma L1_14 : ltac2:(tb__ "0|0|
S0S41S4bSfbZeA2S48Sc4S42Pd4A1S43Z1A1A3A3"). Proof using . reflexivity. Qed.
Lemma swf_SX : swf SX_R1ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_X : ltac2:(tb__ "0|3|
S0S31S2fS2cS2fS41S41A2A1M0S2cS44A1M1A2M2A1S17fSfbS12bA2S35G2S33G0G1S34G0G1S123A3S2bS44S63S97PacA1S43Z12cA1A2S32S44A1A3A4A2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DX_R1ns)). Qed.
Lemma dX_ok : ltac2:(tb__ "0|1|
S0S2dS16cS169S34S2cS2fS41S41A2A1S2cS44A1S123A3M0A1PacS4bSfbZeA2G0A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma keysX : ltac2:(tb__ "0|0|
S0S2dS164SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S123A3A1A4A1S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsX_vars : ltac2:(tb__ "0|2|
S0S2dS93S2fS3fS41A2M0G0S150S3fS39S119SccG0S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S123A3A1M1A4R1A2A1Lu;S37S3fS41R1A3A2Lq;G1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsX_hi : ltac2:(tb__ "0|0|
S0S2dS93S3fS3fS39S118R1A1A1Lj;SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S123A3A1A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma varsX : ltac2:(tb__ "0|0|
S0S2dS152S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S123A3A1A4R1A2A1Lu;SfbA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma xeX : ltac2:(tb__ "0|1|
S1S0S2dS150S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S123A3A1A4M0R1A2A1Lu;S4bSfbZeA2A2S2eA3S0S2dS119G0PacA2S3aA3A2"). Proof using . split; reflexivity. Qed.

Lemma swf_SL : swf SL_R1ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_A : ltac2:(tb__ "0|3|
S0S31S2fS2cS2fS41S41A2A1M0S2cS44A1M1A2M2A1S17fS12aS11fA2S35G2S33G0G1S34G0G1S120A3S32S44A1A4A2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DL_R1ns)). Qed.
Lemma dA_ok : ltac2:(tb__ "0|2|
S0S2dS16cS167S34S2cS2fS41S41A2A1S2cS44A1S120A3M0A1P1M1S42G1A1G0A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma keysA : ltac2:(tb__ "0|0|
S0S2dS164SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1A4A1S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsA_vars : ltac2:(tb__ "0|2|
S0S2dS93S2fS3fS41A2M0G0S150S3fS39S119SccG0S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1M1A4R1A2A1Lu;S37S3fS41R1A3A2Lq;G1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsA_hi : ltac2:(tb__ "0|0|
S0S2dS93S3fS3fS39S118R1A1A1Lj;SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma varsA : ltac2:(tb__ "0|0|
S0S2dS152S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1A4R1A2A1Lu;S12aA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma inA : ltac2:(tb__ "0|2|
S1S92S2fS3fS41A2M0S33S3fS41Pd2S170S6A1A4S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1M1A3S1S92G0S33S3fS41Pd3S16fS6A1A4G1A3S92G0S33S3fS41Pd4S16eS6A1A4G1A3A2A2").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high. vm_compute. repeat split; tauto. Qed.
Lemma no1A : ltac2:(tb__ "0|0|
S0S2dS119SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S120A3A1A4P1A2S3aA3"). Proof using . reflexivity. Qed.

Definition EB0 (x : member) : sv := e_byteS x.
Definition EB2 (x : member) : sv := e_byteL x.
Lemma SX_len : ss_lenient SX_R1ns = false. Proof using . reflexivity. Qed.
Lemma SX_next : ltac2:(tb__ "0|0|
S0S3fS5aS12bA1S122A3"). Proof using . reflexivity. Qed.
Lemma fX0 : ltac2:(tb__ "0|0|
S92S44S4aSc5S97PacA1S16bS6A1A3S47S11bS121U0S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX1 : ltac2:(tb__ "0|0|
S92S44S4eS4aScbS168S6Sf9S6A1A2S43Z0A1A3A1S47S11bS121U1S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX2 : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S97PacA1S16bS6A1A3A1S47S11bS121U2S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX3 : ltac2:(tb__ "0|0|
S92S44S4eS4aScbS168S6SfaS6A1A2S43Z0A1A3A1S47S11bS121U3S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX3b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S97PacA1S16bS6A1A3A1S47S11bS121U3S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX1b : ltac2:(tb__ "0|0|
S92S44S4aSc5S97PacA1S16bS6A1A3S47S11bS121U1S11eA3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S0S99S144Sf6S9Vm0;A1M1Sf4A3S143Sf6G1Sf4A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pM0 AM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|3|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S112Vs;Sf3S30S73S30S73S32S73A1M1S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G1A3S111S9Vm0;A1A1M2A3A3S30S73S30S73G2G1A3G2A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pM0 AM3 ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|3|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S112Vs;Sf3S30S73S30S73S32S73A1M1S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G1A3S111S9Vm0;A1A1M2A3A3S30S73S30S73G2S2bS73S77S85S7cS87Vsc;G0A2A2A1G1A3A3G2A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pM0 AM3 ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S0S2cS3eA1Sa2Sf3A1Sb4S87Vsc;G0A2S87Vbnc;Z1A2Sa2Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pM0 AM3 (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3S10S6S14eA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma loc_mem8 : ltac2:(tb__ "0|2|
S0S3eS79VL;S76S9eS9bS8Vs;Vm0;S6A3A1M0Z8M1A2A1A2S85S22VL;G0A2G1A2A3").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp. unfold zA, addr_of, loc_addr. destruct (am_mem (mam MM0)); cbn [padd]. lia. Qed.

Lemma sd_0 : ltac2:(tb__ "0|4|
S0S31S2fS2cS2fS41S41A2M0A1M1S2cS44A1M2A2M3A1S17fS11bS121U0S11eA3S11cA2S35G3S33G1G2S2bG0S33S41S41S168S6Sf9S6A1A2S42PabA1A4S32G0A1A3S37G1G2S128A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT0_R1ns)). Qed.
Lemma swf_ST0 : swf ST0_R1ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl0 : ltac2:(tb__ "0|0|
S0S2dS93S44S44S95S44S62R1A1S47S11cA1A3Lp;S37S2cS2fS41S41A2A1S2cS44A1S128A3A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST0_vars : ltac2:(tb__ "0|0|
S0S2dS93S44S151S118A1S47S11cA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST0_sup : ltac2:(tb__ "0|0|
S0S2dS93S44S177S47S11cA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST0 : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S11cA1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST0_R1ns) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MM0)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST0_len : ss_lenient ST0_R1ns = false. Proof using . reflexivity. Qed.
Lemma ST0_next : ltac2:(tb__ "0|0|
S0S3fS5aS11cA1S122A3"). Proof using . reflexivity. Qed.

Definition LT00 : sstate := lfs LT0_R1ns 0 ST0_R1ns.
Definition LT01 : sstate := lfs LT0_R1ns 1 ST0_R1ns.
Definition LT02 : sstate := lfs LT0_R1ns 2 ST0_R1ns.
Definition dsF00 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT00))) in exact x).
Definition dsF01 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT01))) in exact x).
Definition dsF02 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT02))) in exact x).
Definition dsC00 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF00) in exact x).
Definition dsC01 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF01) in exact x).
Definition dsC02 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF02) in exact x).
Lemma match00 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS10cA1A2SffA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match01 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS108A1A2S100A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match02 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS109A1A2S101A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars00 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSffA4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars01 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS100A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars02 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS101A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem00 : ltac2:(tb__ "0|0|
S0S2dS93S5S161SffA3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem01 : ltac2:(tb__ "0|0|
S0S2dS93S5S161S100A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem02 : ltac2:(tb__ "0|0|
S0S2dS93S5S161S101A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg00 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7SffA2SfdA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg01 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7S100A2S10eA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg02 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7S101A2S105A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma dsC00_eq : ltac2:(tb__ "0|2|
S0S2cS5A1SfdS2bS5SbS6S97S1aS6A1A1M0G0S97S16S6A1A1S14dS16aS6Sf9S6A1M1A2S97S15S6A1A1A7S2bS5SeS6G1A2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC01_eq : dsC01 = dsC00. Proof using . reflexivity. Qed.
Lemma dsC02_eq : ltac2:(tb__ "0|0|
S0S2cS5A1S105S30S5SfdS2bS5S10S6S14eA2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma LT0_objs k : ltac2:(tb__ "0|1|
ScfVk;U3A2S0S2cS45A1S4cS11bS124Vk;S11cA3A1M0S2bS45S162S5bS96S45S19G0A3A1A1S94S45G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_pc k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S3eS5eS11bS124Vk;S11cA3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_fregs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S2cS41A1S54S11bS124Vk;S11cA3A1Sb9A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_fcsr k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S57S53S11bS124Vk;S11cA3A1S51A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_resv k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S31S41A1S58S11bS124Vk;S11cA3A1S36S41A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_a0 k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S41S4bS11bS124Vk;S11cA3ZaA2S24S97PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_cs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S3eS1S84Z1R1A2S84R1Z1fA2A2S0S2dSbbS8bR2A1A1S2eA3S0S41S4bS11bS124Vk;S11cA3R3A2SbcS8bR3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT0_R1ns k ST0_R1ns) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f00 : ltac2:(tb__ "0|0|
S92S44S4aSc5S43Z1fA1S1bS6A1A3S47S10cA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f01a : ltac2:(tb__ "0|0|
S92S44S4aSc8S97PaaA1S43Z0A1A3S47S108A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f01b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS6A1A3A1S47S108A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f02a : ltac2:(tb__ "0|0|
S92S44S4eS4aSc8S97PaaA1S43Z0A1A3A1S47S109A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f02b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS6A1A3A1S47S109A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Section T0.
Hypothesis CS : ltac2:(tb__ "0|0|
S0S3eS13fSf2A1Vspanv;A3").

Lemma EBv0 : ltac2:(tb__ "0|3|
S1S1S84Z0M0S175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfSf9S6A1A3M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S87S13fSf2A1Z1A2M2A3S2S0S3eSa5S8Vs;Vm0;S6A3A1G0A3A1S0S3eG1G2A3F_;A2A2").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  unfold EB0.
  pose proof (ze_byteS MM0 ltac:(pose proof last_R; pose proof cnt1_ge; pose proof (aidx_range MM0); rewrite <- CS; rewrite span_cnt_eq; destruct (Z.ltb_spec (am_last (mam MM0) + 1) cnt1); lia)) as (E & R & M).
  rewrite CS. split; [exact R|]. split; [rewrite M; lia|].
  intros Hml. rewrite E. pose proof (Hbytes MM0) as (B1 & B2 & B3). rewrite (B3 Hml). pose proof (aidx_range MM0).
  rewrite (Z.mod_small (am_aidx (mam MM0))) by lia. lia.
Qed.

Lemma ME0 : ltac2:(tb__ "0|0|
S0S3eS175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS168S6Sf9S6A1A2A3S178Vmaskv;A1A3").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmv Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  destruct EBv0 as (R & M & _). rewrite (ze_maskG MM0 (EB0 MM0) _ eq_refl) by lia. rewrite M, Hmv, Emask. reflexivity.
Qed.

Lemma ok_meta'0 : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3SbS6S97S1aS6A1A1M0G0S97S16S6A1A1S14dS16aS6Sf9S6A1A2S97S15S6A1A1A7A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Hspanv Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final AM3). split; [exact MT_R'|].
  pose proof (am_final_fields AM3) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold AM3, am1_M0, am0; cbn [am_prev am_set_links am_set_aidx]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold AM3, am1_M0, am0; cbn [am_next am_set_links am_set_aidx]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold AM3, am1_M0; cbn [am_mem am_set_links am_set_aidx]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; reflexivity|].
  split; [destruct EBv0 as (R & M & _); rewrite (ze_freedG MM0 (EB0 MM0) _ eq_refl R), M; unfold AM3, am1_M0; cbn [am_freed am_aidx am_set_links am_set_aidx]; reflexivity|].
  rewrite ze_bits. unfold AM3, am1_M0, meta_bits. cbn [am_last am_sc am_maplen am_set_links am_set_aidx]. reflexivity.
Qed.
Lemma ok_mem'0 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3SeS6Sf9S6A1A2A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. split; [reflexivity|]. exists (am_final AM3). split; [exact MT_R'|].
  destruct EBv0 as (R & M & X3). pose proof (am_final_fields AM3) as (_ & _ & Fm & _ & _ & _ & Fa & _ & _ & Fml). rewrite Fm, Fa, Fml.
  unfold AM3, am1_M0. cbn [am_mem am_aidx am_maplen am_set_links am_set_aidx].
  split; [exact R|]. split; [exact M|]. split; [reflexivity|]. split; [reflexivity|]. exact X3.
Qed.

Ltac ok_changed0 := first [exact ok_meta'0 | exact ok_mem'0 | exact I].
Lemma okC_00 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1SfdA3S1S92S5R2SffA3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg00 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC00_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed0 | exact I]|]). destruct Hd. Qed.
Lemma okC_01 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1S10eA3S1S92S5R2S100A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg01 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC01_eq, dsC00_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed0 | exact I]|]). destruct Hd. Qed.
Lemma okC_02 : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S5S92S5R1S105A3S1S92S5R2S101A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg02 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC02_eq, dsC00_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed0 | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs0_01 : ltac2:(tb__ "0|4|
S73S92S73R1S30S73S30S73S32S73A1M0S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G0A3S111S9Vm0;A1A1M1A3A3S30S73S30S73G1G0A3G1A3A3A3S4S5S5S1S92S5R1SfdA3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M2A3S79VL;R3A2M3A2S86G3S37S3eS3eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC00_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedG MM0 (EB0 MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MM0 (EB0 MM0)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_M0; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
              ].
Qed.
Lemma locs0_2 : ltac2:(tb__ "0|4|
S73S92S73R1S30S73S30S73S32S73A1M0S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G0A3S111S9Vm0;A1A1M1A3A3S30S73S30S73G1S2bS73S77S85S7cS87Vsc;Z7A2A2A1G0A3A3G1A3A3A3S4S5S5S1S92S5R1S105A3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M2A3S79VL;R3A2M3A2S86G3S37S3eS3eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC02_eq, dsC00_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedG MM0 (EB0 MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MM0 (EB0 MM0)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_M0; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MM0 e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
              ].
Qed.

Lemma T0_ok : ltac2:(tb__ "0|0|
S55S11aVrhoW;R1A2VTR;Z0S181Sb8VK;S11cR2A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3F_;FrhoA;").
Proof using CS EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  intros rhoA HagA.
  apply (seg_run 300 ST0_R1ns LT0_R1ns _ rhoA ST0_len ST0_next runT0_R1ns HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (t_mask AM3)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT0_R1ns _ _ _ ST0_R1ns Lf LT0_R1ns_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MM0 rhoF _ _ HagF (conj HsmF HK') f00).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_R1ns 0 ST0_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_R1ns 0 ST0_R1ns) _ _ dsF00 dsC00 (LT0_objs 0%nat ltac:(repeat constructor)) match00 HsmF vars00 sem00
              ltac:(rewrite <- chg00; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_00 (or_introl OUT)) locs0_01
              (LT0_pc 0%nat ltac:(repeat constructor)) (LT0_cs 0%nat ltac:(repeat constructor)) (LT0_fregs 0%nat ltac:(repeat constructor)) (LT0_fcsr 0%nat ltac:(repeat constructor)) (LT0_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f01b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f01a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_R1ns 1 ST0_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_R1ns 1 ST0_R1ns) _ _ dsF01 dsC01 (LT0_objs 1%nat ltac:(repeat constructor)) match01 HsmF vars01 sem01
              ltac:(rewrite <- chg01; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_01 (or_intror (conj IN B0))) locs0_01
              (LT0_pc 1%nat ltac:(repeat constructor)) (LT0_cs 1%nat ltac:(repeat constructor)) (LT0_fregs 1%nat ltac:(repeat constructor)) (LT0_fcsr 1%nat ltac:(repeat constructor)) (LT0_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f02b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f02a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_R1ns 2 ST0_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_R1ns 2 ST0_R1ns) _ _ dsF02 dsC02 (LT0_objs 2%nat ltac:(repeat constructor)) match02 HsmF vars02 sem02
              ltac:(rewrite <- chg02; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_02 IN BN) locs0_2
              (LT0_pc 2%nat ltac:(repeat constructor)) (LT0_cs 2%nat ltac:(repeat constructor)) (LT0_fregs 2%nat ltac:(repeat constructor)) (LT0_fcsr 2%nat ltac:(repeat constructor)) (LT0_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.
End T0.

Lemma sd_2 : ltac2:(tb__ "0|4|
S0S31S2fS2cS2fS41S41A2M0A1M1S2cS44A1M2A2M3A1S17fS11bS121U2S11eA3S11dA2S35G3S33G1G2S2bG0S33S41S41S168S6SfaS6A1A2S42PabA1A4S32G0A1A3S37G1G2S129A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT2_R1ns)). Qed.
Lemma swf_ST2 : swf ST2_R1ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl2 : ltac2:(tb__ "0|0|
S0S2dS93S44S44S95S44S62R1A1S47S11dA1A3Lp;S37S2cS2fS41S41A2A1S2cS44A1S129A3A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST2_vars : ltac2:(tb__ "0|0|
S0S2dS93S44S151S118A1S47S11dA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST2_sup : ltac2:(tb__ "0|0|
S0S2dS93S44S177S47S11dA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST2 : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S11dA1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hsc Hsp Hsp_high.
  change (ss_facts ST2_R1ns) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPUle (v (vbyte MM0)) (SLit 255); SPAlign (vptr MM0) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MM0)) (SLit 32)) (SLit 0))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST2_len : ss_lenient ST2_R1ns = false. Proof using . reflexivity. Qed.
Lemma ST2_next : ltac2:(tb__ "0|0|
S0S3fS5aS11dA1S122A3"). Proof using . reflexivity. Qed.

Definition LT20 : sstate := lfs LT2_R1ns 0 ST2_R1ns.
Definition LT21 : sstate := lfs LT2_R1ns 1 ST2_R1ns.
Definition LT22 : sstate := lfs LT2_R1ns 2 ST2_R1ns.
Definition dsF20 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT20))) in exact x).
Definition dsF21 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT21))) in exact x).
Definition dsF22 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT22))) in exact x).
Definition dsC20 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF20) in exact x).
Definition dsC21 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF21) in exact x).
Definition dsC22 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF22) in exact x).
Lemma match20 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS10dA1A2S102A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match21 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS10aA1A2S103A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match22 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS10bA1A2S104A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars20 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS102A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars21 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS103A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars22 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS104A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem20 : ltac2:(tb__ "0|0|
S0S2dS93S5S161S102A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem21 : ltac2:(tb__ "0|0|
S0S2dS93S5S161S103A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem22 : ltac2:(tb__ "0|0|
S0S2dS93S5S161S104A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg20 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7S102A2SfeA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg21 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7S103A2S10fA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg22 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSf7S104A2S106A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma dsC20_eq : ltac2:(tb__ "0|2|
S0S2cS5A1SfeS2bS5SbS6S97S1aS6A1A1M0G0S97S16S6A1A1S14dS16aS6SfaS6A1M1A2S97S15S6A1A1A7S2bS5SeS6G1A2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC21_eq : dsC21 = dsC20. Proof using . reflexivity. Qed.
Lemma dsC22_eq : ltac2:(tb__ "0|0|
S0S2cS5A1S106S30S5SfeS2bS5S10S6S14eA2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma LT2_objs k : ltac2:(tb__ "0|1|
ScfVk;U3A2S0S2cS45A1S4cS11bS125Vk;S11dA3A1M0S2bS45S162S5bS96S45S19G0A3A1A1S94S45G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_pc k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S3eS5eS11bS125Vk;S11dA3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_fregs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S2cS41A1S54S11bS125Vk;S11dA3A1Sb9A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_fcsr k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S57S53S11bS125Vk;S11dA3A1S51A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_resv k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S31S41A1S58S11bS125Vk;S11dA3A1S36S41A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_a0 k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S41S4bS11bS125Vk;S11dA3ZaA2S24S97PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_cs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S3eS1S84Z1R1A2S84R1Z1fA2A2S0S2dSbbS8bR2A1A1S2eA3S0S41S4bS11bS125Vk;S11dA3R3A2SbcS8bR3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT2_R1ns k ST2_R1ns) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f20 : ltac2:(tb__ "0|0|
S92S44S4aSc5S43Z1fA1S1bS6A1A3S47S10dA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f21a : ltac2:(tb__ "0|0|
S92S44S4aSc8S97PaaA1S43Z0A1A3S47S10aA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f21b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS6A1A3A1S47S10aA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f22a : ltac2:(tb__ "0|0|
S92S44S4eS4aSc8S97PaaA1S43Z0A1A3A1S47S10bA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f22b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS6A1A3A1S47S10bA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Section T2.
Hypothesis CS : ltac2:(tb__ "0|0|
S0S3eS13fSf2A1S85S9fS8Vs;Vm0;S6A3A1Z1A2A3").

Lemma EBv2 : ltac2:(tb__ "0|3|
S1S1S84Z0M0S175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfSfaS6A1A3M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S87S13fSf2A1Z1A2M2A3S2S0S3eSa5S8Vs;Vm0;S6A3A1G0A3A1S0S3eG1G2A3F_;A2A2").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold EB2.
  pose proof (ze_byteL MM0) as (E & R & M).
  rewrite CS. split; [exact R|]. split; [rewrite M; lia|].
  intros Hml. rewrite E. pose proof (Hbytes MM0) as (B1 & B2 & B3). rewrite (B3 Hml). pose proof (aidx_range MM0).
  rewrite (Z.mod_small (am_aidx (mam MM0))) by lia. lia.
Qed.

Lemma ME2 : ltac2:(tb__ "0|0|
S0S3eS175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS168S6SfaS6A1A2A3S178Vmaskv;A1A3").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  destruct EBv2 as (R & M & _). rewrite (ze_maskG MM0 (EB2 MM0) _ eq_refl) by lia. rewrite M, Hmv, Emask. reflexivity.
Qed.

Lemma ok_meta'2 : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3SbS6S97S1aS6A1A1M0G0S97S16S6A1A1S14dS16aS6SfaS6A1A2S97S15S6A1A1A7A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final AM3). split; [exact MT_R'|].
  pose proof (am_final_fields AM3) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MM0); unfold AM3, am1_M0, am0; cbn [am_prev am_set_links am_set_aidx]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MM0); unfold AM3, am1_M0, am0; cbn [am_next am_set_links am_set_aidx]; rewrite ?(am_prev_mam MM0), ?(am_next_mam MM0); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold AM3, am1_M0; cbn [am_mem am_set_links am_set_aidx]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; reflexivity|].
  split; [destruct EBv2 as (R & M & _); rewrite (ze_freedG MM0 (EB2 MM0) _ eq_refl R), M; unfold AM3, am1_M0; cbn [am_freed am_aidx am_set_links am_set_aidx]; reflexivity|].
  rewrite ze_bits. unfold AM3, am1_M0, meta_bits. cbn [am_last am_sc am_maplen am_set_links am_set_aidx]. reflexivity.
Qed.
Lemma ok_mem'2 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3SeS6SfaS6A1A2A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. split; [reflexivity|]. exists (am_final AM3). split; [exact MT_R'|].
  destruct EBv2 as (R & M & X3). pose proof (am_final_fields AM3) as (_ & _ & Fm & _ & _ & _ & Fa & _ & _ & Fml). rewrite Fm, Fa, Fml.
  unfold AM3, am1_M0. cbn [am_mem am_aidx am_maplen am_set_links am_set_aidx].
  split; [exact R|]. split; [exact M|]. split; [reflexivity|]. split; [reflexivity|]. exact X3.
Qed.

Ltac ok_changed2 := first [exact ok_meta'2 | exact ok_mem'2 | exact I].
Lemma okC_20 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1SfeA3S1S92S5R2S102A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg20 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC20_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed2 | exact I]|]). destruct Hd. Qed.
Lemma okC_21 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1S10fA3S1S92S5R2S103A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg21 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC21_eq, dsC20_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed2 | exact I]|]). destruct Hd. Qed.
Lemma okC_22 : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S5S92S5R1S106A3S1S92S5R2S104A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sf3R2A11S160Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using CS HI HMI Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg22 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC22_eq, dsC20_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed2 | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs2_01 : ltac2:(tb__ "0|4|
S73S92S73R1S30S73S30S73S32S73A1M0S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G0A3S111S9Vm0;A1A1M1A3A3S30S73S30S73G1G0A3G1A3A3A3S4S5S5S1S92S5R1SfeA3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M2A3S79VL;R3A2M3A2S86G3S37S3eS3eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC20_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedG MM0 (EB2 MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MM0 (EB2 MM0)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_M0; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
              ].
Qed.
Lemma locs2_2 : ltac2:(tb__ "0|4|
S73S92S73R1S30S73S30S73S32S73A1M0S30S73S2bS73S76S9eS9bSf2A1Z8A2A1G0A3S111S9Vm0;A1A1M1A3A3S30S73S30S73G1S2bS73S77S85S7cS87Vsc;Z7A2A2A1G0A3A3G1A3A3A3S4S5S5S1S92S5R1S106A3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M2A3S79VL;R3A2M3A2S86G3S37S3eS3eG2A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC22_eq, dsC20_eq. change pM0 with (mptr MM0) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (v (vptr MM0)) (v (vptr MM0)) (v (vmem MM0)) e_avT (e_freedG MM0 (EB2 MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MM0 (EB2 MM0)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_M0; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MM0 e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
              ].
Qed.

Lemma T2_ok : ltac2:(tb__ "0|0|
S55S11aVrhoW;R1A2VTR;Z0S181Sb8VK;S11dR2A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3F_;FrhoA;").
Proof using CS EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  intros rhoA HagA.
  apply (seg_run 300 ST2_R1ns LT2_R1ns _ rhoA ST2_len ST2_next runT2_R1ns HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (t_mask AM3)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT2_R1ns _ _ _ ST2_R1ns Lf LT2_R1ns_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MM0 rhoF _ _ HagF (conj HsmF HK') f20).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_R1ns 0 ST2_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_R1ns 0 ST2_R1ns) _ _ dsF20 dsC20 (LT2_objs 0%nat ltac:(repeat constructor)) match20 HsmF vars20 sem20
              ltac:(rewrite <- chg20; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_20 (or_introl OUT)) locs2_01
              (LT2_pc 0%nat ltac:(repeat constructor)) (LT2_cs 0%nat ltac:(repeat constructor)) (LT2_fregs 0%nat ltac:(repeat constructor)) (LT2_fcsr 0%nat ltac:(repeat constructor)) (LT2_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f21b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f21a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_R1ns 1 ST2_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_R1ns 1 ST2_R1ns) _ _ dsF21 dsC21 (LT2_objs 1%nat ltac:(repeat constructor)) match21 HsmF vars21 sem21
              ltac:(rewrite <- chg21; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_21 (or_intror (conj IN B0))) locs2_01
              (LT2_pc 1%nat ltac:(repeat constructor)) (LT2_cs 1%nat ltac:(repeat constructor)) (LT2_fregs 1%nat ltac:(repeat constructor)) (LT2_fcsr 1%nat ltac:(repeat constructor)) (LT2_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MM0 rhoF _ _ HagF (conj HsmF HK') f22b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f22a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_R1ns 2 ST2_R1ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_R1ns 2 ST2_R1ns) _ _ dsF22 dsC22 (LT2_objs 2%nat ltac:(repeat constructor)) match22 HsmF vars22 sem22
              ltac:(rewrite <- chg22; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_22 IN BN) locs2_2
              (LT2_pc 2%nat ltac:(repeat constructor)) (LT2_cs 2%nat ltac:(repeat constructor)) (LT2_fregs 2%nat ltac:(repeat constructor)) (LT2_fcsr 2%nat ltac:(repeat constructor)) (LT2_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pM0 (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.
End T2.

Theorem variant_R1ns : ltac2:(tb__ "0|0|
VTR;Z0S181Sb8VK;S11eVrhoW;A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVpart HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv Hsv RR Rg am0.
  pose proof (aidx_range MM0) as AR. pose proof last_R as LR. pose proof cnt1_ge as CG. pose proof size_range as [SR _].
  destruct (span_facts sc (am_aidx (mam MM0)) Hsc ltac:(lia) HVpart) as [EX LE]. fold cnt1 in LE.

  apply (tr_seq _ (fun w => exists rho0, (agrees rhoW rho0 /\ LINV (span0_of sc (am_aidx (mam MM0))) (am_aidx (mam MM0) + 2) rho0) /\ SymSoundR.SP segsU K SL_R1ns rho0 w)).
  { apply (seg_run 300 SA_R1ns LA_R1ns _ rhoW eq_refl eq_refl runA_R1ns (agrees_refl rhoW)).
    intros LfA rhoA w HinA HagA HSPA.
    rewrite (single_leaf LA_R1ns _ SA_R1ns LfA LA_R1ns_shape HinA) in HSPA. change (lfs LA_R1ns 0 SA_R1ns) with LA_R1nss in HSPA.
    destruct (loop_entry MM0 LA_R1nss SL_R1ns (fst DL_R1ns) swf_SL sd_A dA_ok keysA setsA_vars setsA_hi varsA inA no1A rhoA w HagA HSPA) as (Hag0 & HINV0 & HSP0).
    exists (setp rhoA (setsA (fst DL_R1ns))). split; [split; assumption | exact HSP0]. }

  apply tr_ex. intros rho0. apply tr_pure. intros [Hag0 HINV0].
  apply (tr_seq _ (POST SX_R1ns)).
  { apply (span_loop_sound MM0 SL_R1ns L0 L1 SX_R1ns LL_R1ns (fst DX_R1ns) runL_R1ns LL_eq SL_len SL_next SL_regs ren_chk L0_same L0_5 L0_14 L0_16 T0f T1f L1_14
             swf_SX sd_X dX_ok keysX setsX_vars setsX_hi varsX xeX 300%nat _ _ rho0 Hag0 HINV0).
    - unfold span0_of, UNIT. nia.
    - lia.
    - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - unfold span0_of, UNIT. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. nia.
    - exact EX.
    - rewrite Hsv. reflexivity. }

  apply from_POST. intros rhoX HagX.
  apply (tr_seq _ (fun w => (span_cnt am1_M0 = spanv /\ POST ST0_R1ns w) \/ (span_cnt am1_M0 = am_last (mam MM0) + 1 /\ POST ST2_R1ns w))).
  { apply (seg_run 300 SX_R1ns LX_R1ns _ rhoX SX_len SX_next runX_R1ns HagX).
    intros Lf rhoY w Hin HagY HSPY.
    destruct (leaf4 LX_R1ns _ _ _ _ SA_R1ns Lf LX_R1ns_shape Hin) as [EL|[EL|[EL|EL]]]; rewrite EL in HSPY.
    - assert (CS : span_cnt am1_M0 = spanv) by (rewrite Hsv; apply cnt_S; rewrite <- Hsv; exact (cnt_lt_of MM0 rhoY _ w HagY HSPY fX0)).
      left. split; [exact CS|]. exists rhoY. split; [exact HagY|].
      apply (linkT (lfs LX_R1ns 0 SA_R1ns) ST0_R1ns (e_maskG MM0 (EB0 MM0)) (snd DT0_R1ns) rhoY _ swf_ST0 sd_0 HagY); try assumption.
      + reflexivity.
      + reflexivity. + exact (ME0 CS). + exact nf_incl0. + exact ST0_vars. + exact ST0_sup. + exact ZF_ST0.
    - exfalso. assert (CS : span_cnt am1_M0 = spanv) by (rewrite Hsv; apply cnt_S; rewrite <- Hsv; exact (cnt_lt_of MM0 rhoY _ w HagY HSPY fX1b)).
      pose proof (eq0_of (e_maskG MM0 (EB0 MM0)) rhoY _ w HagY HSPY fX1 eq_refl eq_refl) as Z0.
      rewrite (ME0 CS) in Z0. apply HVmask3. rewrite <- Hmv. apply (proj1 (sx32_zero_iff maskv ltac:(pose proof Hmaskv; lia))). exact Z0.
    - assert (CS : span_cnt am1_M0 = am_last (mam MM0) + 1) by (apply cnt_L; rewrite <- Hsv; exact (cnt_ge_of MM0 rhoY _ w HagY HSPY fX2)).
      right. split; [exact CS|]. exists rhoY. split; [exact HagY|].
      apply (linkT (lfs LX_R1ns 2 SA_R1ns) ST2_R1ns (e_maskG MM0 (EB2 MM0)) (snd DT2_R1ns) rhoY _ swf_ST2 sd_2 HagY); try assumption.
      + reflexivity.
      + reflexivity. + exact (ME2 CS). + exact nf_incl2. + exact ST2_vars. + exact ST2_sup. + exact ZF_ST2.
    - exfalso. assert (CS : span_cnt am1_M0 = am_last (mam MM0) + 1) by (apply cnt_L; rewrite <- Hsv; exact (cnt_ge_of MM0 rhoY _ w HagY HSPY fX3b)).
      pose proof (eq0_of (e_maskG MM0 (EB2 MM0)) rhoY _ w HagY HSPY fX3 eq_refl eq_refl) as Z0.
      rewrite (ME2 CS) in Z0. apply HVmask3. rewrite <- Hmv. apply (proj1 (sx32_zero_iff maskv ltac:(pose proof Hmaskv; lia))). exact Z0. }
  apply tr_disj.
  - apply tr_pure. intros CS. apply from_POST. intros rhoA HagA. exact (T0_ok CS rhoA HagA).
  - apply tr_pure. intros CS. apply from_POST. intros rhoA HagA. exact (T2_ok CS rhoA HagA).
Qed.

End VR1ns.
End Mal_aslot_VR1ns.

Module Mal_aslot_VD2ns.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_runsD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section VD2ns.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S84Z0Vreq;A2S84S85Vreq;Sa8A2Sa4Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs;Vsc;A2S35S98Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S7eS7dVX;Vs;Vsc;A3S35S98Vm0;A2S2bS98Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§29§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§29§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§29§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§29§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§29§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§29§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§29§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls2 := (@U.Mal_aslot__G1.Mal_aslot_I.cls2 s X sc Hsc m0 rest Rg).
Local Notation "§30§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§30§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Local Abbreviation mptr_key := (§30§ U.Mal_aslot__G1.Mal_aslot_I.mptr_key).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S199S15aVX;S36S2fS98S3eA2A1VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S20S1S1S84Z0M0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S9cS8Vs;Vm0;R1A3M2A1A3S2S0S3eSa5G2A1G0A3A1S0S3eS1cVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S9cS8Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Notation "§31§ h__" := (h__ s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation mem_R := (§31§ U.Mal_aslot__G1.Mal_aslot_I.mem_R).
Local Notation "§32§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§32§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§32§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§32§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Abbreviation vbyte := (@U.Mal_aslot__G1.Mal_aslot_I.vbyte).
Local Notation "§33§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§33§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§33§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§33§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§33§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§33§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Local Abbreviation ze171 := (§32§ U.Mal_aslot__G1.Mal_aslot_I.ze171).
Local Abbreviation e_lowbit := (@U.Mal_aslot__G1.Mal_aslot_I.e_lowbit).
Local Abbreviation e_dbidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_dbidx).
Local Abbreviation e_bncidx := (@U.Mal_aslot__G1.Mal_aslot_I.e_bncidx).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sc0Q40S49Vrho;PaA2A2M0A2S0S3eS89G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S174Z40Sc0Q40S49Vrho;PfA2A2A2M0S8aS186Z0A1A1A2S84S8aS8cZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S84S15eVL;A1S85Sc0Q40M0S49Vrho;PaA2A2S174Z40Sc0G0S49Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Notation "§34§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high) (at level 10, h__ global).
Local Abbreviation ZF_base5 := (§34§ U.Mal_aslot__G1.Mal_aslot_I.ZF_base5).
Local Abbreviation zf_ptr_ne0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_byte := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_byte).
Local Abbreviation zf_align := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_align).
Local Abbreviation zf_freeable := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_freeable).
Local Notation "§35§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation zf_neq := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_neq).
Local Abbreviation zf_avail_eq0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_avail_ne0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_ne0).
Local Abbreviation zf_freed_eq0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Local Abbreviation zf_freed_ne0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_ne0).
Local Abbreviation zf_avail_le0 := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_le0).
Local Abbreviation zf_all_eq := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_eq).
Local Abbreviation zf_all_ne := (§33§ U.Mal_aslot__G1.Mal_aslot_I.zf_all_ne).
Local Abbreviation zf_act_ne0_a := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_a).
Local Abbreviation zf_act_ne0_b := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_ne0_b).
Local Abbreviation zf_act_eq0_a := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_a).
Local Abbreviation zf_act_eq0_b := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_act_eq0_b).
Local Abbreviation zf_tabidx := (§35§ U.Mal_aslot__G1.Mal_aslot_I.zf_tabidx).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;Vrd0;S13dSb8VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SbfQ40A1S2dF_;Vwok0;S13eSb8VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z60A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ecR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z20A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ccR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S20S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S22VL;S9bS8Vs;Vm0;R1A3A1A2Z8A2A2A3S35G1Sc1G0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S85Z5a3d0Z369A2Vsc;A2A2A3S35G1Sc1G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S15dS15bVrd0;SbfQ40A1S2eL_;A2S15cS15aA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S15bS13dSb8VmW;A2S13eSb8VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§36§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§36§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§29§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§37§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§37§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation e_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.e_ctz).
Local Notation "§38§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_ctz := (§38§ U.Mal_aslot__G1.Mal_aslot_I.ze_ctz).
Local Abbreviation od_ok_meta_entry := (§33§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§33§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Local Abbreviation od_ok_mem_entry := (§33§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_mem_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S0S3eVbnc;SacS87Vsc;G0A2Sa2Vs;A1A2A3F_;").
Local Notation "§39§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hbnc_val) (at level 10, h__ global).
Local Abbreviation od_ok_bnc_entry := (§39§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_bnc_entry).
Local Abbreviation od_ok_got := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§32§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S19aSb8VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cS114A1S115OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW).
Local Notation "§40§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation seg_run := (§40§ U.Mal_aslot__G2.Mal_aslot_W.seg_run).
Local Notation "§41§ h__" := (h__ Kc RF GF TR RR) (at level 10, h__ global).
Local Abbreviation tr_seq := (§41§ U.Mal_aslot__G2.Mal_aslot_W.tr_seq).
Local Abbreviation tr_ex := (§41§ U.Mal_aslot__G2.Mal_aslot_W.tr_ex).
Local Abbreviation tr_pure := (§41§ U.Mal_aslot__G2.Mal_aslot_W.tr_pure).
Local Abbreviation tr_disj := (§41§ U.Mal_aslot__G2.Mal_aslot_W.tr_disj).
Local Notation "§42§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW K) (at level 10, h__ global).
Local Abbreviation POST := (§42§ U.Mal_aslot__G2.Mal_aslot_W.POST).
Local Notation "§43§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0 mW Kc RF GF TR RR K) (at level 10, h__ global).
Local Abbreviation from_POST := (§43§ U.Mal_aslot__G2.Mal_aslot_W.from_POST).
Local Abbreviation setp := (@U.Mal_aslot__G2.Mal_aslot_W.setp).
Local Abbreviation keys_distinct := (@U.Mal_aslot__G2.Mal_aslot_W.keys_distinct).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§44§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_okH := (§44§ U.Mal_aslot__G2.Mal_aslot_W.post_okH).
Local Abbreviation e_avT := (@U.Mal_aslot__G3.Mal_aslot_T.e_avT).
Local Abbreviation e_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.e_bncdec).
Local Abbreviation maskA := (§29§ U.Mal_aslot__G3.Mal_aslot_T.maskA).
Local Notation "§45§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hmaskv Hsp) (at level 10, h__ global).
Local Abbreviation ze_avT := (§45§ U.Mal_aslot__G3.Mal_aslot_T.ze_avT).
Local Notation "§46§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_bncdec := (§46§ U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec).
Local Notation "§47§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW Hbnc_val K) (at level 10, h__ global).
Local Abbreviation bnc_out_of := (§47§ U.Mal_aslot__G3.Mal_aslot_T.bnc_out_of).
Local Notation "§48§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_in_of := (§48§ U.Mal_aslot__G3.Mal_aslot_T.bnc_in_of).
Local Notation "§49§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW K) (at level 10, h__ global).
Local Abbreviation bnc_zero_of := (§49§ U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of).
Local Abbreviation bnc_nz_of := (§49§ U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of).
Local Abbreviation zf_T171 := (§45§ U.Mal_aslot__G3.Mal_aslot_T.zf_T171).
Local Abbreviation linkT := (§42§ U.Mal_aslot__G3.Mal_aslot_T.linkT).
Local Notation "§50§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§50§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§50§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation bounces_len := (§50§ U.Mal_aslot__G3.Mal_aslot_T.bounces_len).
Local Notation "§51§ h__" := (h__ sc rho bnc gd Hsc Hbnc Hgd Hsp) (at level 10, h__ global).
Local Abbreviation active_hd_set_hd := (§51§ U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd).
Local Abbreviation xraw_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta X).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation xraw_s6 := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_s6 X).
Local Abbreviation memb_used := (§30§ U.Mal_aslot__G3.Mal_aslot_T.memb_used).
Local Abbreviation set_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.set_hd_set_hd).
Local Abbreviation len_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.len_set_hd).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation st_active_upd_meta := (@U.Mal_aslot__G3.Mal_aslot_T.st_active_upd_meta).
Local Abbreviation am_next_mam := (§30§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation am_prev_mam := (§30§ U.Mal_aslot__G3.Mal_aslot_T.am_prev_mam).
Local Abbreviation nonhead_avail0 := (§31§ U.Mal_aslot__G3.Mal_aslot_T.nonhead_avail0).
Local Abbreviation xraw_upd_meta_ptr := (§30§ U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta_ptr).
Local Abbreviation ta_post_of := (@U.Mal_aslot__G3.Mal_aslot_T.ta_post_of s X U sc HI Hsc).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).
Local Abbreviation e_size := (@U.Mal_aslot__G9.Mal_aslot_L.e_size).
Local Abbreviation e_span0 := (@U.Mal_aslot__G9.Mal_aslot_L.e_span0).
Local Abbreviation e_a60 := (@U.Mal_aslot__G9.Mal_aslot_L.e_a60).
Local Abbreviation e_a40 := (@U.Mal_aslot__G9.Mal_aslot_L.e_a40).
Local Abbreviation e_byteS := (@U.Mal_aslot__G9.Mal_aslot_L.e_byteS).
Local Abbreviation e_byteL := (@U.Mal_aslot__G9.Mal_aslot_L.e_byteL).
Local Abbreviation e_maskG := (@U.Mal_aslot__G9.Mal_aslot_L.e_maskG).
Local Abbreviation e_freedG := (@U.Mal_aslot__G9.Mal_aslot_L.e_freedG).
Local Abbreviation size_range := (§51§ U.Mal_aslot__G9.Mal_aslot_L.size_range).
Local Abbreviation aidx_range := (@U.Mal_aslot__G9.Mal_aslot_L.aidx_range s sc rho byM0 byA byB byC byP bnc gd Hsc m0 Hbytes Hbnc Hgd).
Local Notation "§52§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hspanv Hsp) (at level 10, h__ global).
Local Abbreviation ze_byteS := (§52§ U.Mal_aslot__G9.Mal_aslot_L.ze_byteS).
Local Abbreviation ze_byteL := (§35§ U.Mal_aslot__G9.Mal_aslot_L.ze_byteL).
Local Abbreviation ze_maskG := (§33§ U.Mal_aslot__G9.Mal_aslot_L.ze_maskG).
Local Abbreviation ze_freedG := (§35§ U.Mal_aslot__G9.Mal_aslot_L.ze_freedG).
Local Abbreviation e_last1 := (@U.Mal_aslot__G9.Mal_aslot_L.e_last1).
Local Notation "§53§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hspanv Hsp mW K) (at level 10, h__ global).
Local Abbreviation cnt_lt_of := (§53§ U.Mal_aslot__G9.Mal_aslot_L.cnt_lt_of).
Local Abbreviation cnt_ge_of := (§53§ U.Mal_aslot__G9.Mal_aslot_L.cnt_ge_of).
Local Abbreviation eq0_of := (§42§ U.Mal_aslot__G9.Mal_aslot_L.eq0_of).
Local Abbreviation span_cnt_ge2 := (§51§ U.Mal_aslot__G9.Mal_aslot_L.span_cnt_ge2).
Local Abbreviation rename_chk := (@U.Mal_aslot__G9.Mal_aslot_L.rename_chk).
Local Abbreviation setsB := (@U.Mal_aslot__G9.Mal_aslot_L.setsB).
Local Abbreviation setsX := (@U.Mal_aslot__G9.Mal_aslot_L.setsX).
Local Abbreviation LINV := (@U.Mal_aslot__G9.Mal_aslot_L.LINV sc).
Local Notation "§54§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Hbnc_val Kc RF GF TR RR K HK) (at level 10, h__ global).
Local Abbreviation span_loop_sound := (§54§ U.Mal_aslot__G9.Mal_aslot_L.span_loop_sound).
Local Abbreviation setsA := (@U.Mal_aslot__G9.Mal_aslot_L.setsA).
Local Notation "§55§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hsp mW K) (at level 10, h__ global).
Local Abbreviation loop_entry := (§55§ U.Mal_aslot__G9.Mal_aslot_L.loop_entry).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;VmW;S59Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S116Vvm;S117Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cS114A1M0S115VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S115R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4fSb8Vrho;S188S187A1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PdA2A2Vreq;A3").

Hypothesis Hr : rcls = 2%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S3eSadS8Vs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S3eSa3S8Vs;Vm0;S6A3A1Z0A3").
Hypothesis HVskip : ltac2:(tb__ "0|1|
S2S0S3eSa3S8Vs;Vm0;S7A3M0A1SabS9fG0A1A1A3A1").
Hypothesis HVact : maskA MA_ = 0.

Hypothesis HVpart : ltac2:(tb__ "0|0|
S86S87Z1000SafA2S88Sa4Vsc;A1S85S9cS8Vs;Vm0;S7A3A1Z2A2A2A2").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Vs;S9Vm0;A1A2S35S9aS9dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls2 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls2 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.
Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition xp : mslot := MUsed (mam MA_).
Definition xn : mslot := ltac2:(tb__ "0|1|
S9dSaaSb0S8Vs;Vm0;S7A3M0A1S35S98SaVs;Vm0;A2A2G0A3A1").
Definition am1_M0 : ameta := (am_set_links None None am0).
Definition am1_A : ameta := ltac2:(tb__ "0|2|
SaaS35S98SaVs;Vm0;A2A2M0G0SaaSb0S8Vs;Vm0;S7A3M1A1G0G1A3A3").
Definition s1V : astate := ltac2:(tb__ "0|1|
S149Vs;Vsc;S9Vm0;A1Vam0;SaVs;Vm0;A2M0G0Se3SebA8").
Definition s2V : astate := s1V.

Definition AM3 : ameta := ltac2:(tb__ "0|0|
Sb1S87S13fSd0A1Z1A2Sd0A2").
Definition s3V : astate := ltac2:(tb__ "0|0|
S1aaSaVs;Vm0;A2S9dSd2A1Se6A3").

Definition cnt1 : Z := ltac2:(tb__ "0|1|
Sb2U12cS85S9cS8Vs;Vm0;S7A3A1M0Z2A2S173Vsc;G0A2Sa4Vsc;A1A4").

Hypothesis Hmv : ltac2:(tb__ "0|0|
S0S3eVmaskv;S140Sd2A1A3").
Hypothesis Hsv : spanv = cnt1.
Lemma HXp : ltac2:(tb__ "0|0|
S0S31S9aA1S75Vs;SaVs;Vm0;A2A2S35S9aSe3A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MA_))). Qed.
Lemma HXn : ltac2:(tb__ "0|1|
S0S31S9aA1S75S142Vs;SaVs;Vm0;A2M0G0Se3A4G0A2S35S9aSebA2A3").
Proof using . drop_sp. unfold s1a, xn, xp. cbn [with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K1a : ltac2:(tb__ "0|1|
S0S2cS98A1S78S142Vs;SaVs;Vm0;A2M0G0Se3A4A1S78Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1a. apply keys_upd_In. exact (mptr_key MA_). Qed.
Lemma K1b : ltac2:(tb__ "0|1|
S0S2cS98A1S78S14bVs;SaVs;Vm0;A2M0G0Se3SebA5A1S78Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1b. rewrite keys_upd_In; [exact K1a|]. rewrite K1a. exact (mptr_key MA_). Qed.
Lemma K1 : ltac2:(tb__ "0|0|
S0S2cS98A1S78Sd5A1S78Vs;A1A3"). Proof using HI Hhd Hsc. unfold s1V, s1_deq. rewrite keys_upd_In; rewrite keys_set_hd, K1b; [reflexivity | exact (mptr_key MM0)]. Qed.
Lemma MT1_M0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd5S21Vs;Vm0;S6A3A2S35S9aS9dSeeA1A2A3").
Proof using . drop_sp. unfold s1V, am1_M0, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MM0)))]. Qed.
Lemma MT1_A : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd5S21Vs;Vm0;S7A3A2S35S9aS9dSd0A1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold s1V, am1_A, s1_deq, s1b, s1a, xn, xp. cbn [mptr with_links links_of fst snd]. repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]. first [reflexivity | exact (proj2 (proj2 (mam_used MA_)))]. Qed.
Lemma K3 : ltac2:(tb__ "0|0|
S0S2cS98A1S78Sd4A1S78Vs;A1A3"). Proof using HI Hhd Hsc. unfold s3V, s2V. rewrite keys_upd_In; [exact K1|]. rewrite K1. exact (mptr_key MA_). Qed.
Lemma ND1 : List.NoDup (keys s1V). Proof using HI Hhd Hsc. rewrite K1. exact ND. Qed.
Lemma ND3 : List.NoDup (keys s3V). Proof using HI Hhd Hsc. rewrite K3. exact ND. Qed.
Lemma MT3_other q : ltac2:(tb__ "0|0|
S2S0S98Vq;SaVs;Vm0;A2A3A1S0S31S9aA1S75Sd4Vq;A2S75Sd5Vq;A2A3F_;"). Proof using . intros Hq. unfold s3V, s2V. apply MT_upd_other. exact Hq. Qed.
Lemma bounces3 : ltac2:(tb__ "0|0|
S0S2cS3eA1Sa2Sd4A1Sa2Vs;A1A3"). Proof using . reflexivity. Qed.
Lemma xraw1 : xraw X s1V. Proof using HI HXr Hhd Hsc. unfold s1V, s1_deq, s1b, s1a. repeat first [apply xraw_set_hd | apply xraw_upd_meta].
  all: first [exact HXr | exact (memb_used MM0) | exact (memb_used MA_) | exact (memb_used MB) | exact (memb_used MC) | exact (memb_used MP)]. Qed.
Lemma xraw3 : xraw X s3V. Proof using HI HXr Hhd Hsc. unfold s3V, s2V. change pA with (mptr MA_). apply xraw_upd_meta_ptr. exact xraw1. Qed.
Lemma len1 : length (st_active s1V) = 48%nat. Proof using HI. unfold s1V, s1_deq. unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len. Qed.
Lemma hd1 : ltac2:(tb__ "0|0|
S0S31S98A1S74Sd5Vsc;A2S35S98SaVs;Vm0;A2A2A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq. rewrite ?active_hd_upd_meta, ?set_hd_set_hd. apply active_hd_set_hd; [| exact Hsc].
  unfold s1b, s1a; repeat (first [rewrite len_set_hd | rewrite st_active_upd_meta]); exact active_len.
Qed.
Lemma hd3 : ltac2:(tb__ "0|0|
S0S31S98A1S74Sd4Vsc;A2S35S98SaVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold s3V, s2V. rewrite active_hd_upd_meta. exact hd1. Qed.

Lemma S1 : ltac2:(tb__ "0|2|
S0Sa1S99S2fS31S98A1M0S99A2M1A2S146Vsc;S9Vm0;A1Vam0;Vs;A4Sa0S99G1S33G0S99S35S98SaVs;Vm0;A2A2Sd5A4A3A3").
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
S0S98SaVs;Vm0;A2S21Vs;Vm0;S7A3A3"). Proof using Hr Hsc Rg. cbn [mptr]. solve_link. Qed.
Lemma HM1 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd5SaVs;Vm0;A2A2S35S9aS9dSd0A1A2A3"). Proof using Hr Hsc Rg. rewrite E_m1. exact MT1_A. Qed.
Lemma S2 : ltac2:(tb__ "0|2|
S0Sa1S99S2fS98S99A2M0A2S147Vsc;SaVs;Vm0;A2M1Sd0Sd5A4Sa0S99G0S33S98S99G1Se6A4A3A3").
Proof using HVskip Hr Hsc Rg. drop_sp. unfold s2V. rewrite E_m1. apply step2_stay. unfold am1_A. cbn [am_freed am_last am_set_links]. exact HVskip. Qed.
Lemma HM2 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Se6SaVs;Vm0;A2A2S35S9aS9dSd0A1A2A3"). Proof using Hr Hsc Rg. unfold s2V. exact MT1_A. Qed.
Lemma next2 : ltac2:(tb__ "0|0|
S0S31S98A1SaeSd0A1S35S98SaVs;Vm0;A2A2A3").
Proof using . drop_sp. unfold am1_A. cbn [am_next am_set_links]. first [reflexivity | rewrite (am_next_mam MA_); f_equal; cbn [mptr]; solve_link]. Qed.
Lemma S3 : ltac2:(tb__ "0|2|
S0Sa1S99S2fS98S99A2M0A2S148Vsc;SaVs;Vm0;A2M1Sd0Se6A4Sa0S99G0S33S98S99G1Sd4A4A3A3").
Proof using HVact. drop_sp. unfold s3V, AM3. apply (step3_span s2V sc pA am1_A); [unfold am1_A; cbn [am_freed am_aidx am_set_links]; exact HVact | exact next2]. Qed.
Lemma HM3 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd4SaVs;Vm0;A2A2S35S9aS9dSd2A1A2A3"). Proof using . unfold s3V. apply MT_upd_same. Qed.
Lemma Hav3 : am_avail AM3 = 0. Proof using HI HMI Hbnc Hgd Hhd Hr Hsc Rg. unfold AM3, am1_A. cbn [am_avail am_set_aidx am_set_links]. apply nonhead_avail0; cbn [mptr]; solve_neq. Qed.
Lemma sc_am2 : ltac2:(tb__ "0|0|
S0S3eSa9Sd0A1Vsc;A3"). Proof using HI Hhd Hsc. unfold am1_A. cbn [am_sc am_set_links]. exact (proj1 (proj2 (mam_used MA_))). Qed.
Lemma aidx_am2 : ltac2:(tb__ "0|0|
S0S3eS9cSd0A1S9cS8Vs;Vm0;S7A3A1A3"). Proof using . reflexivity. Qed.
Lemma last_am2 : ltac2:(tb__ "0|0|
S0S3eS9fSd0A1S9fS8Vs;Vm0;S7A3A1A3"). Proof using . reflexivity. Qed.
Lemma freed_am2 : ltac2:(tb__ "0|0|
S0S3eSa3Sd0A1Sa3S8Vs;Vm0;S7A3A1A3"). Proof using . reflexivity. Qed.

Lemma span_cnt_eq : ltac2:(tb__ "0|1|
S0S3eS13fSd0A1S2dS3eL_;S8dS85S9fS8Vs;Vm0;S7A3A1Z1A2M0SdaA2G0SdaX2dx2A3").
Proof using HI Hhd Hsc. drop_sp. unfold span_cnt, cnt1, span0_of. rewrite sc_am2, aidx_am2, last_am2. reflexivity. Qed.
Lemma cnt1_ge : ltac2:(tb__ "0|0|
S84S85S9cS8Vs;Vm0;S7A3A1Z2A2SdaA2"). Proof using . unfold cnt1. apply span_loop_ge. Qed.
Lemma last_R : ltac2:(tb__ "0|2|
S1S84S9cS8Vs;Vm0;S7A3M0A1S9fG0A1M1A2S84G1Z1fA2A2"). Proof using HI HMI Hbnc Hgd Hhd Hr Hsc rho. pose proof (mem_R MA_) as (_ & _ & R3 & R4 & _). lia. Qed.
Lemma cnt_S : ltac2:(tb__ "0|0|
S86SdaS85S9fS8Vs;Vm0;S7A3A1Z1A2A2S0S3eS13fSd0A1SdaA3F_;").
Proof using HI Hbnc Hgd Hhd Hr Hsc rho. drop_sp. intros H. rewrite span_cnt_eq. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma cnt_L : ltac2:(tb__ "0|1|
S84S85S9fS8Vs;Vm0;S7A3A1Z1A2M0SdaA2S0S3eS13fSd0A1G0A3F_;").
Proof using HI Hbnc Hgd Hhd Hr Hsc rho. drop_sp. intros H. rewrite span_cnt_eq. destruct (Z.ltb_spec (am_last (mam MA_) + 1) cnt1); lia. Qed.
Lemma Emask : ltac2:(tb__ "0|0|
S0S3eS140Sd2A1S90Sa3S8Vs;Vm0;S7A3A1SabS87S13fSd0A1Z1A2A1A2A3"). Proof using . reflexivity. Qed.
Lemma HVmask3 : t_mask AM3 <> 0.
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. exact (ta_mask_nz X U s sc pM0 am0 HI Hsc Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V AM3 S1 HM1 S2 HM2 S3 HM3 Hav3). Qed.
Lemma maskS_range : ltac2:(tb__ "0|1|
S1S84Z0S140Sd2A1M0A2S86G0S8cZ2Z20A2A2A2").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  rewrite Emask. pose proof (mem_R MA_) as (_ & R2 & R3 & R4 & _). pose proof (span_cnt_ge2 am1_A) as [G _]; [rewrite aidx_am2; pose proof (aidx_range MA_); lia | rewrite last_am2; pose proof last_R; lia |].
  assert (HO : 0 < ones (span_cnt am1_A - 1) < 2 ^ 32).
  { apply ones_u32. rewrite span_cnt_eq. pose proof last_R. pose proof cnt1_ge. destruct (Z.ltb_spec (am_last (mam MA_) + 1) cnt1); lia. }
  split; [apply Z.land_nonneg; lia|]. pose proof (MallocWfSlot.land_le_l (am_freed (mam MA_)) (ones (span_cnt am1_A - 1)) ltac:(lia)). lia.
Qed.

Definition sR' : astate := ltac2:(tb__ "0|0|
S145Sd4SaVs;Vm0;A2Sd2A3").
Lemma taR : ltac2:(tb__ "0|1|
S0Sa1S99S2fS3eS99A2M0A2Sa7Vsc;Vs;A2Sa0S99G0S33S3eS99Sa6S140Sd2A1A1Sd1A4A3A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  exact (ta_miss s sc pM0 am0 Hhd HM0 HVa0 pA s1V am1_A pA s2V am1_A pA s3V AM3 S1 HM1 S2 HM2 S3 HM3 Hav3 HVmask3).
Qed.
Lemma lowbit_nz : ltac2:(tb__ "0|0|
S2S0S3eSa6S140Sd2A1A1Z0A3A1").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. pose proof maskS_range. pose proof (lowbit_range (t_mask AM3) ltac:(pose proof HVmask3; lia)). lia. Qed.
Lemma postR : ltac2:(tb__ "0|0|
S1aeVX;VU;Vs;Vsc;Sa6S140Sd2A1A1Sd1A6"). Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Rg. exact (ta_post_of _ _ taR lowbit_nz). Qed.

Lemma hdR' : ltac2:(tb__ "0|0|
S0S31S98A1S74Sd1Vsc;A2S35S98SaVs;Vm0;A2A2A3"). Proof using HI Hbnc Hgd Hsc Hsp. unfold sR'. rewrite (active_hd_s6 s3V pA AM3). exact hd3. Qed.
Lemma MT_R' : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd1SaVs;Vm0;A2A2S35S9aS9dS141Sd2A1A1A2A3"). Proof using . unfold sR'. apply MT_s6_same. Qed.
Lemma xraw_R' : xraw X sR'. Proof using HI HXr Hhd Hsc. unfold sR'. apply xraw_s6; [exact xraw3 | exact (memb_used MA_)]. Qed.
Lemma sc_am3 : ltac2:(tb__ "0|0|
S0S3eSa9Sd2A1Vsc;A3"). Proof using HI Hhd Hsc. unfold AM3. cbn [am_sc am_set_aidx]. exact sc_am2. Qed.

Lemma MTF_M0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Sd1S21Vs;Vm0;S6A3A2S35S9aS9dSeeA1A2A3").
Proof using Hr Hsc Rg. drop_sp. unfold sR'. rewrite (MT_s6_other s3V pA AM3); [rewrite MT3_other; [exact MT1_M0 | cbn [mptr]; solve_neq] | cbn [mptr]; solve_neq]. Qed.
Lemma delta1 : ltac2:(tb__ "0|1|
S112Vs;Sd5S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8Vsc;A2A2A1S32S73A1A3A3S111S9Vm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  unfold s1V, s1_deq.
  apply (delta_trans _ (set_hd sc (Some pA) (s1b s pA pA xp xn))); [apply (delta_trans _ (s1b s pA pA xp xn)); [apply (delta_trans _ (s1a s pA pA xp))|]|].
  - unfold s1a, xp. cbn [with_links links_of fst snd]. apply (delta_su_keep s pA (mam MA_)); [exact ND | exact HXp | apply same_shape_links | reflexivity].
  - unfold s1b. pose proof HXn as Hn. unfold xn in Hn |- *. cbn [with_links links_of fst snd] in Hn |- *.
    eapply (delta_su_keep _ pA _ _); [rewrite K1a; exact ND | exact Hn | apply same_shape_links | reflexivity].
  - apply delta_sh. lia.
  - apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd, K1b; exact ND | rewrite MT_set_hd; unfold s1b, s1a, xn, xp; cbn [with_links links_of fst snd]; repeat first [rewrite MT_upd_same | rewrite MT_set_hd | rewrite MT_upd_other by (cbn [mptr]; solve_neq)]; exact HM0 | apply same_shape_links | reflexivity].
Qed.
Lemma delta3 : ltac2:(tb__ "0|0|
S112Sd5Sd4S30S73S2bS73S76S9eS9bSd0A1Z8A2A1S32S73A1A3S111SaVs;Vm0;A2A1A3A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold s3V, s2V, AM3. apply (delta_su s1V pA am1_A); [exact ND1 | exact HM2 | apply same_shape_aidx]. Qed.
Lemma delta03 : ltac2:(tb__ "0|3|
S112Vs;Sd4S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8M1Vsc;A2A2A1S32S73A1M2A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G1A2A1G2A3G0A3A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. eapply delta_trans; [exact delta1 | exact delta3]. Qed.

Definition dsR : list od := ltac2:(tb__ "0|2|
S2bS5S11S2bS5S12S2bS5SdS97S1aS6A1A1M0A1S2bS5SbS6S97S1aS7A1A1M1G1S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S2bS5SbS7G0G0S97S16S7A1A1S97S1eS7A1A1S97S1fS7A1A1S97S15S7A1A1A7S2bS5SeS7S97S2aS7A1A1A2S2bS5S14S2bS5S13S2bS5S10S7S97PaaA1A2S32S5A1A3A3A3A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cS130A1S2bS45S19SccS5S45SfSd6A4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_D2ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

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
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0))) => apply (zf_act_ne0_a x); assumption
  | |- zholds _ _ (SPNot (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0))) => apply (zf_act_ne0_b x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD _ _) (SExt true _ (v (vfreed ?x)))) (SLit 0)) => apply (zf_act_eq0_a x); assumption
  | |- zholds _ _ (SPBranch BC_EQ (SAlu ALU_AND (SExt true _ (v (vfreed ?x))) (SAluW ALU_ADD _ _)) (SLit 0)) => apply (zf_act_eq0_b x); assumption
  | |- zholds _ _ (SPUle (v (vavail ?x)) (SLit 0)) => apply (zf_avail_le0 x); first [assumption | apply nonhead_avail0; cbn [mptr]; solve_neq]
  | |- zholds _ _ (SPUle (SAlu ALU_AND (SAlu ALU_SRL (v (vbits ?x)) (SLit 5)) (SLit 126)) (SLit 94)) => apply (zf_tabidx x)
  end.

Lemma ZF_R : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S130A1A3").
Proof using HI HMI HVa0 HVact HVf0 HVskip Hbnc Hbytes Hdepth Hgd Hhd Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts SA_D2ns) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_))); SPBranch BC_EQ (SExt true 32%N (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32%N (v (vfreed MM0))) (SLit 0); SPBranch BC_NE (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbits MA_))) (SLit 18446744073709551615)); SPBranch BC_EQ (SAlu ALU_AND (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615)) (SExt true 32%N (v (vfreed MA_)))) (SLit 0); SPBranch BC_EQ (SAlu ALU_AND (SExt true 32%N (v (vfreed MA_))) (SAluW ALU_ADD (SAluW ALU_SLL (SLit 2) (v (vbyte MA_))) (SLit 18446744073709551615))) (SLit 0); SPUle (SAlu ALU_AND (SAlu ALU_SRL (v (vbits MA_)) (SLit 5)) (SLit 126)) (SLit 94); SPUle (v (vavail MA_)) (SLit 0)]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S5dZ2126cSbaSb9S51S36S41A1S2bS45S19S32S45A1A3S47S130A1S137S3aA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4fSb8VrhoW;Sf1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4M0A4S4fSb8VrhoW;S130G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_D2ns with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S38S3cS5VdsF;A2S3cS5Sd6A2A3S5S92S5R1VdsF;A3S3S23Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S92S5R2S14cSd6VdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbnc_val Hbytes Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.
Lemma changed_sub : ltac2:(tb__ "0|1|
S2cS5A1M0G0S5S92S5R1S14cR3R2A2A3S92S5R2R3A3F_;Fd;Fds';Fds;").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  induction ds as [|x t IH]; intros [|y t'] d Hd; cbn in Hd; try tauto.
  destruct (od_eqb x y); [right; exact (IH _ _ Hd) | destruct Hd as [<-|Hd]; [left; reflexivity | right; exact (IH _ _ Hd)]].
Qed.

Definition L0 : sstate := lfs LL_D2ns 0 SA_D2ns.
Definition L1 : sstate := lfs LL_D2ns 1 SA_D2ns.
Lemma LL_eq : ltac2:(tb__ "0|0|
S0S2cS183A1S13cS2bS183S185Sd3S184A2S2bS183S185Sd9S184A2S32S183A1A3A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma SL_len : ss_lenient SL_D2ns = false. Proof using . reflexivity. Qed.
Lemma SL_next : ltac2:(tb__ "0|0|
S0S3fS5aS131A1S137A3"). Proof using . reflexivity. Qed.
Lemma SL_regs : ltac2:(tb__ "0|0|
S1S0S41S4bS131Z5A2S42Pd2A1A3S1S0S41S4bS131Z10A2S42Pd3A1A3S0S41S4bS131ZeA2S42Pd4A1A3A2A2"). Proof using . repeat split; reflexivity. Qed.
Lemma ren_chk : ltac2:(tb__ "0|0|
S0S2dS171S3fS39S119S2bS3fPd2S2bS3fPd5S2bS3fPd4S2bS3fPd3S32S3fA1A3A3A3A3R1A2A1Lu;Sd3S131S172Sd3A1A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma L0_same : ltac2:(tb__ "0|0|
S1S0S2cS41A1S54S131A1S54Sd3A1A3S1S0S57S53S131A1S53Sd3A1A3S1S0S31S41A1S58S131A1S58Sd3A1A3S0S2cS45A1S4cS131A1S4cSd3A1A3A2A2A2"). Proof using . repeat split; vm_compute; reflexivity. Qed.
Lemma L0_5 : ltac2:(tb__ "0|0|
S0S41S4bSd3Z5A2S48Sc4S42Pd2A1S16dS7A1A3A3"). Proof using . reflexivity. Qed.
Lemma L0_14 : ltac2:(tb__ "0|0|
S0S41S4bSd3ZeA2S48Sc4S42Pd4A1S43Z1A1A3A3"). Proof using . reflexivity. Qed.
Lemma L0_16 : ltac2:(tb__ "0|0|
S0S41S4bSd3Z10A2S48Sc4S42Pd3A1S16dS7A1A3A3"). Proof using . reflexivity. Qed.
Lemma T0f : ltac2:(tb__ "0|0|
S92S44S4aScaS46Sc9S42Pd3A1S42Pd2A1A3S43Z1000A1A3S47Sd3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma T1f : ltac2:(tb__ "0|0|
S92S44S4eS4aScaS46Sc9S42Pd3A1S42Pd2A1A3S43Z1000A1A3A1S47Sd9A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma L1_14 : ltac2:(tb__ "0|0|
S0S41S4bSd9ZeA2S48Sc4S42Pd4A1S43Z1A1A3A3"). Proof using . reflexivity. Qed.
Lemma swf_SX : swf SX_D2ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_X : ltac2:(tb__ "0|3|
S0S31S2fS2cS2fS41S41A2A1M0S2cS44A1M1A2M2A1S17fSd9S13bA2S35G2S33G0G1S34G0G1S134A3S2bS44S63S97PacA1S43Z12cA1A2S32S44A1A3A4A2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DX_D2ns)). Qed.
Lemma dX_ok : ltac2:(tb__ "0|1|
S0S2dS16cS169S34S2cS2fS41S41A2A1S2cS44A1S134A3M0A1PacS4bSd9ZeA2G0A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma keysX : ltac2:(tb__ "0|0|
S0S2dS164SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S134A3A1A4A1S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsX_vars : ltac2:(tb__ "0|2|
S0S2dS93S2fS3fS41A2M0G0S150S3fS39S119SccG0S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S134A3A1M1A4R1A2A1Lu;S37S3fS41R1A3A2Lq;G1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsX_hi : ltac2:(tb__ "0|0|
S0S2dS93S3fS3fS39S118R1A1A1Lj;SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S134A3A1A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma varsX : ltac2:(tb__ "0|0|
S0S2dS152S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S134A3A1A4R1A2A1Lu;Sd9A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma xeX : ltac2:(tb__ "0|1|
S1S0S2dS150S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S169S34S2cS2fS41S41A2A1S2cS44A1S134A3A1A4M0R1A2A1Lu;S4bSd9ZeA2A2S2eA3S0S2dS119G0PacA2S3aA3A2"). Proof using . split; reflexivity. Qed.

Lemma swf_SL : swf SL_D2ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_A : ltac2:(tb__ "0|3|
S0S31S2fS2cS2fS41S41A2A1M0S2cS44A1M1A2M2A1S17fS13aS131A2S35G2S33G0G1S34G0G1S132A3S32S44A1A4A2A3"). Proof using . vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DL_D2ns)). Qed.
Lemma dA_ok : ltac2:(tb__ "0|2|
S0S2dS16cS167S34S2cS2fS41S41A2A1S2cS44A1S132A3M0A1P1M1S42G1A1G0A4S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma keysA : ltac2:(tb__ "0|0|
S0S2dS164SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1A4A1S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsA_vars : ltac2:(tb__ "0|2|
S0S2dS93S2fS3fS41A2M0G0S150S3fS39S119SccG0S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1M1A4R1A2A1Lu;S37S3fS41R1A3A2Lq;G1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma setsA_hi : ltac2:(tb__ "0|0|
S0S2dS93S3fS3fS39S118R1A1A1Lj;SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma varsA : ltac2:(tb__ "0|0|
S0S2dS152S3fS39S119SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1A4R1A2A1Lu;S13aA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma inA : ltac2:(tb__ "0|2|
S1S92S2fS3fS41A2M0S33S3fS41Pd2S170S7A1A4S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1M1A3S1S92G0S33S3fS41Pd3S16fS7A1A4G1A3S92G0S33S3fS41Pd4S16eS7A1A4G1A3A2A2").
Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. try clear Hsp_high. vm_compute. repeat split; tauto. Qed.
Lemma no1A : ltac2:(tb__ "0|0|
S0S2dS119SccS2fS3fS41A2S3fS34S3fS41A2S167S34S2cS2fS41S41A2A1S2cS44A1S132A3A1A4P1A2S3aA3"). Proof using . reflexivity. Qed.

Definition EB0 (x : member) : sv := e_byteS x.
Definition EB2 (x : member) : sv := e_byteL x.
Lemma SX_len : ss_lenient SX_D2ns = false. Proof using . reflexivity. Qed.
Lemma SX_next : ltac2:(tb__ "0|0|
S0S3fS5aS13bA1S137A3"). Proof using . reflexivity. Qed.
Lemma fX0 : ltac2:(tb__ "0|0|
S92S44S4aSc5S97PacA1S16bS7A1A3S47S12dS133U0S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX1 : ltac2:(tb__ "0|0|
S92S44S4eS4aScbS168S7Sd7S7A1A2S43Z0A1A3A1S47S12dS133U1S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX2 : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S97PacA1S16bS7A1A3A1S47S12dS133U2S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX3 : ltac2:(tb__ "0|0|
S92S44S4eS4aScbS168S7Sd8S7A1A2S43Z0A1A3A1S47S12dS133U3S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX3b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S97PacA1S16bS7A1A3A1S47S12dS133U3S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma fX1b : ltac2:(tb__ "0|0|
S92S44S4aSc5S97PacA1S16bS7A1A3S47S12dS133U1S130A3A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Lemma s5_01 : ltac2:(tb__ "0|2|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S0S99S144Sd4SaVs;Vm0;A2M1Sd2A3S143Sd4G1Sd2A3A3F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros [H|[H Hb]].
  - apply s5_out. rewrite sc_am3. apply bounce_idx_none. exact H.
  - apply (s5_zero s3V pA AM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H|].
    rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma delta_01 : ltac2:(tb__ "0|4|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S112Vs;Sd1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M1G1A3S2bS73S77S85S7aS88Z8M2Vsc;A2A2A1S32S73A1M3A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G2A2A1G3A3G1A3A3S30S73S30S73G1G3A3G1A3A3A3F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. intros H. eapply delta_trans; [apply delta03|]. unfold sR'. apply (delta_s6_same s3V pA AM3 ND3 HM3). apply s5_01. exact H. Qed.
Lemma delta_2 : ltac2:(tb__ "0|4|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S112Vs;Sd1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M1G1A3S2bS73S77S85S7aS88Z8M2Vsc;A2A2A1S32S73A1M3A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G2A2A1G3A3G1A3A3S30S73S30S73G1S2bS73S77S85S7cS87Vsc;G0A2A2A1G3A3A3G1A3A3A3F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth.
  intros H Hb. eapply delta_trans; [apply delta03|]. unfold sR'.
  apply (delta_s6_dec s3V pA AM3 ND3 HM3 (sc - 7)); [rewrite sc_am3; apply bounce_idx_some; exact H | lia |].
  rewrite bounces3, <- (Hbnc_val H). exact Hb.
Qed.
Lemma bounces_R'_dec : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S0S2cS3eA1Sa2Sd1A1Sb4S87Vsc;G0A2S87Vbnc;Z1A2Sa2Vs;A1A3A3F_;F_;").
Proof using HI Hbnc_val Hhd Hsc. drop_sp.
  intros H Hb. unfold sR'. rewrite (st_bounces_s6_dec s3V pA AM3 (sc - 7)); [| rewrite sc_am3; apply bounce_idx_some; exact H | rewrite bounces3, <- (Hbnc_val H); exact Hb].
  rewrite bounces3, <- (Hbnc_val H). reflexivity.
Qed.
Lemma ok_bnc' : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1S10S7S14eA2A11F_;F_;").
Proof using HI Hbnc Hbnc_val Hgd Hhd Hr Hsc. drop_sp.
  intros H Hb. cbn [od_ok_at]. split; [reflexivity|]. rewrite (ze_bncdec Hb). pose proof Hbnc. split; [lia|].
  intros _. rewrite (bounces_R'_dec H Hb). rewrite znth_zset by (first [clear - H; solve [lia] | lia]). rewrite Z.eqb_refl, bounces_len.
  replace (sc - 7 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma loc_mem8 : ltac2:(tb__ "0|2|
S0S3eS79VL;S76S9eS9bS8Vs;Vm0;S7A3A1M0Z8M1A2A1A2S85S22VL;G0A2G1A2A3").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp. unfold zA, addr_of, loc_addr. destruct (am_mem (mam MA_)); cbn [padd]. lia. Qed.
Lemma ok_M0' : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SbS6S43Z0A1M0G0S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists am1_M0. split; [exact MTF_M0|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_prev am_set_links am_set_aidx optrZ]; reflexivity|].
  split; [rewrite ze_lit; unfold am1_M0, am0; cbn [am_next am_set_links am_set_aidx optrZ]; reflexivity|].
  unfold am1_M0, am0. cbn [am_mem am_avail am_freed am_set_links].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.

Lemma sd_0 : ltac2:(tb__ "0|4|
S0S31S2fS2cS2fS41S41A2M0A1M1S2cS44A1M2A2M3A1S17fS12dS133U0S130A3S12eA2S35G3S33G1G2S2bG0S33S41S41S168S7Sd7S7A1A2S42PabA1A4S32G0A1A3S37G1G2S138A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT0_D2ns)). Qed.
Lemma swf_ST0 : swf ST0_D2ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl0 : ltac2:(tb__ "0|0|
S0S2dS93S44S44S95S44S62R1A1S47S12eA1A3Lp;S37S2cS2fS41S41A2A1S2cS44A1S138A3A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST0_vars : ltac2:(tb__ "0|0|
S0S2dS93S44S151S118A1S47S12eA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST0_sup : ltac2:(tb__ "0|0|
S0S2dS93S44S177S47S12eA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST0 : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S12eA1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST0_D2ns) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST0_len : ss_lenient ST0_D2ns = false. Proof using . reflexivity. Qed.
Lemma ST0_next : ltac2:(tb__ "0|0|
S0S3fS5aS12eA1S137A3"). Proof using . reflexivity. Qed.

Definition LT00 : sstate := lfs LT0_D2ns 0 ST0_D2ns.
Definition LT01 : sstate := lfs LT0_D2ns 1 ST0_D2ns.
Definition LT02 : sstate := lfs LT0_D2ns 2 ST0_D2ns.
Definition dsF00 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT00))) in exact x).
Definition dsF01 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT01))) in exact x).
Definition dsF02 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT02))) in exact x).
Definition dsC00 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF00) in exact x).
Definition dsC01 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF01) in exact x).
Definition dsC02 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF02) in exact x).
Lemma match00 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSecA1A2SddA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match01 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSe7A1A2SdeA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match02 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSe8A1A2SdfA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars00 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSddA4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars01 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSdeA4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars02 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSdfA4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem00 : ltac2:(tb__ "0|0|
S0S2dS93S5S161SddA3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem01 : ltac2:(tb__ "0|0|
S0S2dS93S5S161SdeA3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem02 : ltac2:(tb__ "0|0|
S0S2dS93S5S161SdfA3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg00 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6SddA2SdbA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg01 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6SdeA2SefA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg02 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6SdfA2Se4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma dsC00_eq : ltac2:(tb__ "0|3|
S0S2cS5A1SdbS2bS5SdS97S1aS7A1A1M0A1S2bS5SbS6S43Z0A1M1G1S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S2bS5SbS7G0G0S97S16S7A1A1S14dS16aS7Sd7S7A1M2A2S97S15S7A1A1A7S2bS5SeS7G2A2S32S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC01_eq : dsC01 = dsC00. Proof using . reflexivity. Qed.
Lemma dsC02_eq : ltac2:(tb__ "0|0|
S0S2cS5A1Se4S30S5SdbS2bS5S10S7S14eA2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma LT0_objs k : ltac2:(tb__ "0|1|
ScfVk;U3A2S0S2cS45A1S4cS12dS135Vk;S12eA3A1M0S2bS45S162S5bS96S45S19G0A3A1A1S94S45G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_pc k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S3eS5eS12dS135Vk;S12eA3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_fregs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S2cS41A1S54S12dS135Vk;S12eA3A1Sb9A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_fcsr k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S57S53S12dS135Vk;S12eA3A1S51A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_resv k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S31S41A1S58S12dS135Vk;S12eA3A1S36S41A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_a0 k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S41S4bS12dS135Vk;S12eA3ZaA2S24S97PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT0_cs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S3eS1S84Z1R1A2S84R1Z1fA2A2S0S2dSbbS8bR2A1A1S2eA3S0S41S4bS12dS135Vk;S12eA3R3A2SbcS8bR3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT0_D2ns k ST0_D2ns) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f00 : ltac2:(tb__ "0|0|
S92S44S4aSc5S43Z1fA1S1bS7A1A3S47SecA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f01a : ltac2:(tb__ "0|0|
S92S44S4aSc8S97PaaA1S43Z0A1A3S47Se7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f01b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS7A1A3A1S47Se7A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f02a : ltac2:(tb__ "0|0|
S92S44S4eS4aSc8S97PaaA1S43Z0A1A3A1S47Se8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f02b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS7A1A3A1S47Se8A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Section T0.
Hypothesis CS : ltac2:(tb__ "0|0|
S0S3eS13fSd0A1Vspanv;A3").

Lemma EBv0 : ltac2:(tb__ "0|3|
S1S1S84Z0M0S175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfSd7S7A1A3M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S87S13fSd0A1Z1A2M2A3S2S0S3eSa5S8Vs;Vm0;S7A3A1G0A3A1S0S3eG1G2A3F_;A2A2").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  unfold EB0.
  pose proof (ze_byteS MA_ ltac:(pose proof last_R; pose proof cnt1_ge; pose proof (aidx_range MA_); rewrite <- CS; rewrite span_cnt_eq; destruct (Z.ltb_spec (am_last (mam MA_) + 1) cnt1); lia)) as (E & R & M).
  rewrite CS. split; [exact R|]. split; [rewrite M; lia|].
  intros Hml. rewrite E. pose proof (Hbytes MA_) as (B1 & B2 & B3). rewrite (B3 Hml). pose proof (aidx_range MA_).
  rewrite (Z.mod_small (am_aidx (mam MA_))) by lia. lia.
Qed.

Lemma ME0 : ltac2:(tb__ "0|0|
S0S3eS175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS168S7Sd7S7A1A2A3S178Vmaskv;A1A3").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmv Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  destruct EBv0 as (R & M & _). rewrite (ze_maskG MA_ (EB0 MA_) _ eq_refl) by lia. rewrite M, Hmv, Emask. reflexivity.
Qed.

Lemma ok_meta'0 : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SbS7S97S1aS7A1A1M0G0S97S16S7A1A1S14dS16aS7Sd7S7A1A2S97S15S7A1A1A7A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final AM3). split; [exact MT_R'|].
  pose proof (am_final_fields AM3) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold AM3, am1_A, am0; cbn [am_prev am_set_links am_set_aidx]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold AM3, am1_A, am0; cbn [am_next am_set_links am_set_aidx]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold AM3, am1_A; cbn [am_mem am_set_links am_set_aidx]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; reflexivity|].
  split; [destruct EBv0 as (R & M & _); rewrite (ze_freedG MA_ (EB0 MA_) _ eq_refl R), M; unfold AM3, am1_A; cbn [am_freed am_aidx am_set_links am_set_aidx]; reflexivity|].
  rewrite ze_bits. unfold AM3, am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links am_set_aidx]. reflexivity.
Qed.
Lemma ok_mem'0 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SeS7Sd7S7A1A2A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp Hspanv. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. split; [reflexivity|]. exists (am_final AM3). split; [exact MT_R'|].
  destruct EBv0 as (R & M & X3). pose proof (am_final_fields AM3) as (_ & _ & Fm & _ & _ & _ & Fa & _ & _ & Fml). rewrite Fm, Fa, Fml.
  unfold AM3, am1_A. cbn [am_mem am_aidx am_maplen am_set_links am_set_aidx].
  split; [exact R|]. split; [exact M|]. split; [reflexivity|]. split; [reflexivity|]. exact X3.
Qed.
Lemma ok_act'0 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SdS97S1aS7A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.

Ltac ok_changed0 := first [exact ok_meta'0 | exact ok_mem'0 | exact ok_act'0 | exact ok_M0' | exact I].
Lemma okC_00 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1SdbA3S1S92S5R2SddA3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg00 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC00_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed0 | exact I]|]). destruct Hd. Qed.
Lemma okC_01 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1SefA3S1S92S5R2SdeA3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg01 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC01_eq, dsC00_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed0 | exact I]|]). destruct Hd. Qed.
Lemma okC_02 : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S5S92S5R1Se4A3S1S92S5R2SdfA3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg02 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC02_eq, dsC00_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed0 | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs0_01 : ltac2:(tb__ "0|5|
S73S92S73R1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8M1Vsc;A2A2A1S32S73A1M2A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G1A2A1G2A3G0A3A3S30S73S30S73G0G2A3G0A3A3A3S4S5S5S1S92S5R1SdbA3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M3A3S79VL;R3A2M4A2S86G4S37S3eS3eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC00_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedG MA_ (EB0 MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MA_ (EB0 MA_)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_A; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs0_2 : ltac2:(tb__ "0|5|
S73S92S73R1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8M1Vsc;A2A2A1S32S73A1M2A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G1A2A1G2A3G0A3A3S30S73S30S73G0S2bS73S77S85S7cS87Vsc;Z7A2A2A1G2A3A3G0A3A3A3S4S5S5S1S92S5R1Se4A3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M3A3S79VL;R3A2M4A2S86G4S37S3eS3eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC02_eq, dsC00_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedG MA_ (EB0 MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MA_ (EB0 MA_)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_A; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Lemma T0_ok : ltac2:(tb__ "0|0|
S55S11aVrhoW;R1A2VTR;Z0S181Sb8VK;S12eR2A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3F_;FrhoA;").
Proof using CS EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  intros rhoA HagA.
  apply (seg_run 300 ST0_D2ns LT0_D2ns _ rhoA ST0_len ST0_next runT0_D2ns HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (t_mask AM3)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT0_D2ns _ _ _ ST0_D2ns Lf LT0_D2ns_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f00).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_D2ns 0 ST0_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_D2ns 0 ST0_D2ns) _ _ dsF00 dsC00 (LT0_objs 0%nat ltac:(repeat constructor)) match00 HsmF vars00 sem00
              ltac:(rewrite <- chg00; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_00 (or_introl OUT)) locs0_01
              (LT0_pc 0%nat ltac:(repeat constructor)) (LT0_cs 0%nat ltac:(repeat constructor)) (LT0_fregs 0%nat ltac:(repeat constructor)) (LT0_fcsr 0%nat ltac:(repeat constructor)) (LT0_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f01b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f01a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_D2ns 1 ST0_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_D2ns 1 ST0_D2ns) _ _ dsF01 dsC01 (LT0_objs 1%nat ltac:(repeat constructor)) match01 HsmF vars01 sem01
              ltac:(rewrite <- chg01; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_01 (or_intror (conj IN B0))) locs0_01
              (LT0_pc 1%nat ltac:(repeat constructor)) (LT0_cs 1%nat ltac:(repeat constructor)) (LT0_fregs 1%nat ltac:(repeat constructor)) (LT0_fcsr 1%nat ltac:(repeat constructor)) (LT0_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f02b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f02a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT0_D2ns 2 ST0_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT0_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT0_D2ns 2 ST0_D2ns) _ _ dsF02 dsC02 (LT0_objs 2%nat ltac:(repeat constructor)) match02 HsmF vars02 sem02
              ltac:(rewrite <- chg02; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_02 IN BN) locs0_2
              (LT0_pc 2%nat ltac:(repeat constructor)) (LT0_cs 2%nat ltac:(repeat constructor)) (LT0_fregs 2%nat ltac:(repeat constructor)) (LT0_fcsr 2%nat ltac:(repeat constructor)) (LT0_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.
End T0.

Lemma sd_2 : ltac2:(tb__ "0|4|
S0S31S2fS2cS2fS41S41A2M0A1M1S2cS44A1M2A2M3A1S17fS12dS133U2S130A3S12fA2S35G3S33G1G2S2bG0S33S41S41S168S7Sd8S7A1A2S42PabA1A4S32G0A1A3S37G1G2S139A3A4A2A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some DT2_D2ns)). Qed.
Lemma swf_ST2 : swf ST2_D2ns = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma nf_incl2 : ltac2:(tb__ "0|0|
S0S2dS93S44S44S95S44S62R1A1S47S12fA1A3Lp;S37S2cS2fS41S41A2A1S2cS44A1S139A3A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST2_vars : ltac2:(tb__ "0|0|
S0S2dS93S44S151S118A1S47S12fA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ST2_sup : ltac2:(tb__ "0|0|
S0S2dS93S44S177S47S12fA1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_ST2 : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S12fA1A3").
Proof using HI HMI Hbnc Hbytes Hdepth Hgd Hhd Hmaskv Hr Hsc Hsp Hsp_high Rg.
  change (ss_facts ST2_D2ns) with ((F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (SLit 0)); SPUle (v (vbyte MA_)) (SLit 255); SPAlign (vptr MA_) 3; SPNot (SPBranch BC_EQ (SAlu ALU_AND (v (vbits MA_)) (SLit 32)) (SLit 0)); SPNot (SPBranch BC_EQ (v (vptr MA_)) (v (vptr MM0))); SPNot (SPBranch BC_EQ (v (vptr MM0)) (v (vptr MA_)))]) ++
    [SPNot (SPBranch BC_EQ (v 171) (SLit 0)); SPNot (SPBranch BC_EQ (e_lowbit (v 171)) (SLit 0)); SPUle (e_dbidx (v 171)) (SLit 31); SPUle (v 170) (SLit 255)]).
  apply Forall_app. split; [|exact zf_T171]. apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [solve_zf|]). apply Forall_nil.
Qed.
Lemma ST2_len : ss_lenient ST2_D2ns = false. Proof using . reflexivity. Qed.
Lemma ST2_next : ltac2:(tb__ "0|0|
S0S3fS5aS12fA1S137A3"). Proof using . reflexivity. Qed.

Definition LT20 : sstate := lfs LT2_D2ns 0 ST2_D2ns.
Definition LT21 : sstate := lfs LT2_D2ns 1 ST2_D2ns.
Definition LT22 : sstate := lfs LT2_D2ns 2 ST2_D2ns.
Definition dsF20 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT20))) in exact x).
Definition dsF21 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT21))) in exact x).
Definition dsF22 : list od := ltac:(let x := eval vm_compute in (fill dsR (tl (ss_objs LT22))) in exact x).
Definition dsC20 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF20) in exact x).
Definition dsC21 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF21) in exact x).
Definition dsC22 : list od := ltac:(let x := eval vm_compute in (changed dsR dsF22) in exact x).
Lemma match20 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSedA1A2Se0A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match21 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSe9A1A2Se1A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma match22 : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cSeaA1A2Se2A2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars20 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSe0A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars21 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSe1A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma vars22 : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfSe2A4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem20 : ltac2:(tb__ "0|0|
S0S2dS93S5S161Se0A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem21 : ltac2:(tb__ "0|0|
S0S2dS93S5S161Se1A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sem22 : ltac2:(tb__ "0|0|
S0S2dS93S5S161Se2A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chg20 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6Se0A2SdcA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg21 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6Se1A2Sf0A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma chg22 : ltac2:(tb__ "0|0|
S0S2cS5A1S14cSd6Se2A2Se5A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma dsC20_eq : ltac2:(tb__ "0|3|
S0S2cS5A1SdcS2bS5SdS97S1aS7A1A1M0A1S2bS5SbS6S43Z0A1M1G1S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S2bS5SbS7G0G0S97S16S7A1A1S14dS16aS7Sd8S7A1M2A2S97S15S7A1A1A7S2bS5SeS7G2A2S32S5A1A3A3A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsC21_eq : dsC21 = dsC20. Proof using . reflexivity. Qed.
Lemma dsC22_eq : ltac2:(tb__ "0|0|
S0S2cS5A1Se5S30S5SdcS2bS5S10S7S14eA2S32S5A1A3A3A3"). Proof using . reflexivity. Qed.

Lemma LT2_objs k : ltac2:(tb__ "0|1|
ScfVk;U3A2S0S2cS45A1S4cS12dS136Vk;S12fA3A1M0S2bS45S162S5bS96S45S19G0A3A1A1S94S45G0A2A3A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_pc k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S3eS5eS12dS136Vk;S12fA3A1Z21b08A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_fregs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S2cS41A1S54S12dS136Vk;S12fA3A1Sb9A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_fcsr k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S57S53S12dS136Vk;S12fA3A1S51A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_resv k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S31S41A1S58S12dS136Vk;S12fA3A1S36S41A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_a0 k : ltac2:(tb__ "0|0|
ScfVk;U3A2S0S41S4bS12dS136Vk;S12fA3ZaA2S24S97PabA1A1A3F_;").
Proof using . drop_sp. intros Hk. destruct k as [|[|[|k]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hk; lia]. Qed.
Lemma LT2_cs k : ltac2:(tb__ "0|0|
ScfVk;U3A2S3eS1S84Z1R1A2S84R1Z1fA2A2S0S2dSbbS8bR2A1A1S2eA3S0S41S4bS12dS136Vk;S12fA3R3A2SbcS8bR3A1A1A3F_;F_;Fz;F_;").
Proof using Hbnc Hgd Hr Hsc rho. drop_sp.
  intros Hk z Hz Hcs.
  pose proof (forall_range_dec (fun z => forallb (fun k => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (lfs LT2_D2ns k ST2_D2ns) z) (pre_reg (Z.to_nat z))) [0;1;2]%nat)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb forallb] in XX.
  repeat (apply andb_prop in XX as [?X1 XX]).
  destruct k as [|[|[|k]]]; [apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | apply sv_eqb_sound; assumption | exfalso; clear - Hk; lia].
Qed.

Lemma f20 : ltac2:(tb__ "0|0|
S92S44S4aSc5S43Z1fA1S1bS7A1A3S47SedA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f21a : ltac2:(tb__ "0|0|
S92S44S4aSc8S97PaaA1S43Z0A1A3S47Se9A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f21b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS7A1A3A1S47Se9A1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f22a : ltac2:(tb__ "0|0|
S92S44S4eS4aSc8S97PaaA1S43Z0A1A3A1S47SeaA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.
Lemma f22b : ltac2:(tb__ "0|0|
S92S44S4eS4aSc5S43Z1fA1S1bS7A1A3A1S47SeaA1A3"). Proof using Hbnc Hbnc_val Hdepth Hgd Hmaskv Hreq Hsc Hsp Hspanv. vm_compute. tauto. Qed.

Section T2.
Hypothesis CS : ltac2:(tb__ "0|0|
S0S3eS13fSd0A1S85S9fS8Vs;Vm0;S7A3A1Z1A2A3").

Lemma EBv2 : ltac2:(tb__ "0|3|
S1S1S84Z0M0S175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfSd8S7A1A3M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S87S13fSd0A1Z1A2M2A3S2S0S3eSa5S8Vs;Vm0;S7A3A1G0A3A1S0S3eG1G2A3F_;A2A2").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold EB2.
  pose proof (ze_byteL MA_) as (E & R & M).
  rewrite CS. split; [exact R|]. split; [rewrite M; lia|].
  intros Hml. rewrite E. pose proof (Hbytes MA_) as (B1 & B2 & B3). rewrite (B3 Hml). pose proof (aidx_range MA_).
  rewrite (Z.mod_small (am_aidx (mam MA_))) by lia. lia.
Qed.

Lemma ME2 : ltac2:(tb__ "0|0|
S0S3eS175S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS168S7Sd8S7A1A2A3S178Vmaskv;A1A3").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  destruct EBv2 as (R & M & _). rewrite (ze_maskG MA_ (EB2 MA_) _ eq_refl) by lia. rewrite M, Hmv, Emask. reflexivity.
Qed.

Lemma ok_meta'2 : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SbS7S97S1aS7A1A1M0G0S97S16S7A1A1S14dS16aS7Sd8S7A1A2S97S15S7A1A1A7A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hmaskv Hmv Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_final AM3). split; [exact MT_R'|].
  pose proof (am_final_fields AM3) as (Fp & Fn & Fm & Fa & Ff & Fb & _).
  rewrite Fp, Fn, Fm, Fa, Ff, Fb.
  split; [rewrite (ze_ptr MA_); unfold AM3, am1_A, am0; cbn [am_prev am_set_links am_set_aidx]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [rewrite (ze_ptr MA_); unfold AM3, am1_A, am0; cbn [am_next am_set_links am_set_aidx]; rewrite ?(am_prev_mam MA_), ?(am_next_mam MA_); cbn [optrZ]; f_equal; cbn [mptr]; solve_link|].
  split; [unfold AM3, am1_A; cbn [am_mem am_set_links am_set_aidx]; apply ze_mem|].
  split; [rewrite ze_avT, Hmv; unfold t_first; reflexivity|].
  split; [destruct EBv2 as (R & M & _); rewrite (ze_freedG MA_ (EB2 MA_) _ eq_refl R), M; unfold AM3, am1_A; cbn [am_freed am_aidx am_set_links am_set_aidx]; reflexivity|].
  rewrite ze_bits. unfold AM3, am1_A, meta_bits. cbn [am_last am_sc am_maplen am_set_links am_set_aidx]. reflexivity.
Qed.
Lemma ok_mem'2 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SeS7Sd8S7A1A2A11").
Proof using CS HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  cbn [od_ok_at]. split; [reflexivity|]. exists (am_final AM3). split; [exact MT_R'|].
  destruct EBv2 as (R & M & X3). pose proof (am_final_fields AM3) as (_ & _ & Fm & _ & _ & _ & Fa & _ & _ & Fml). rewrite Fm, Fa, Fml.
  unfold AM3, am1_A. cbn [am_mem am_aidx am_maplen am_set_links am_set_aidx].
  split; [exact R|]. split; [exact M|]. split; [reflexivity|]. split; [reflexivity|]. exact X3.
Qed.
Lemma ok_act'2 : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1SdS97S1aS7A1A1A1A11").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hsc Hsp. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite hdR'. cbn [optrZ]. exact (ze_ptr MA_). Qed.

Ltac ok_changed2 := first [exact ok_meta'2 | exact ok_mem'2 | exact ok_act'2 | exact ok_M0' | exact I].
Lemma okC_20 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1SdcA3S1S92S5R2Se0A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg20 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC20_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed2 | exact I]|]). destruct Hd. Qed.
Lemma okC_21 : ltac2:(tb__ "0|1|
S3S2S1S84Z7Vsc;A2S86Vsc;Z27A2A2M0A1S1G0S0S3eVbnc;Z0A3A2A2S5S92S5R1Sf0A3S1S92S5R2Se1A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros H d Hd. split; [rewrite <- chg21 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC21_eq, dsC20_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [ok_changed2 | exact I]|]). destruct Hd. Qed.
Lemma okC_22 : ltac2:(tb__ "0|0|
S1S84Z7Vsc;A2S86Vsc;Z27A2A2S2S0S3eVbnc;Z0A3A1S5S92S5R1Se5A3S1S92S5R2Se2A3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;Sd1R2A11S160Vsc;R2A2A2A2F_;Fd;F_;F_;").
Proof using CS HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hmv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high.
  intros H Hb d Hd. split; [rewrite <- chg22 in Hd; exact (changed_sub _ _ _ Hd)|]. rewrite dsC22_eq, dsC20_eq in Hd. cbn [app] in Hd.
  repeat (destruct Hd as [<-|Hd]; [split; [first [ok_changed2 | exact (ok_bnc' H Hb)] | first [exact I | exact H]]|]). destruct Hd.
Qed.

Lemma locs2_01 : ltac2:(tb__ "0|5|
S73S92S73R1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8M1Vsc;A2A2A1S32S73A1M2A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G1A2A1G2A3G0A3A3S30S73S30S73G0G2A3G0A3A3A3S4S5S5S1S92S5R1SdcA3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M3A3S79VL;R3A2M4A2S86G4S37S3eS3eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC20_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedG MA_ (EB2 MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MA_ (EB2 MA_)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_A; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.
Lemma locs2_2 : ltac2:(tb__ "0|5|
S73S92S73R1S30S73S30S73S30S73S30S73S30S73S111SaVs;Vm0;A2A1M0G0A3S2bS73S77S85S7aS88Z8M1Vsc;A2A2A1S32S73A1M2A3A3S111S9Vm0;A1A1A3S30S73S2bS73S76S9eS9bSd0A1G1A2A1G2A3G0A3A3S30S73S30S73G0S2bS73S77S85S7cS87Vsc;Z7A2A2A1G2A3A3G0A3A3A3S4S5S5S1S92S5R1Se5A3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M3A3S79VL;R3A2M4A2S86G4S37S3eS3eG3A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC22_eq, dsC20_eq. change pM0 with (mptr MM0) in Hl. change pA with (mptr MA_) in Hl.
  repeat (apply in_app_iff in Hl as [Hl|Hl]).
  all: first [ (exfalso; exact Hl)
             | (pose proof (in_meta_locs_range MM0 l Hl) as R_; exists (OD_meta MM0 (SLit 0) (SLit 0) (v (vmem MM0)) (v (vavail MM0)) (v (vfreed MM0)) (v (vbits MM0))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (pose proof (in_meta_locs_range MA_ l Hl) as R_; exists (OD_meta MA_ (v (vptr MA_)) (v (vptr MA_)) (v (vmem MA_)) e_avT (e_freedG MA_ (EB2 MA_)) (v (vbits MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; clear - R_; lia)
             | (destruct Hl as [<-|[]]; exists (OD_mem MA_ (EB2 MA_)); split; [cbn; tauto|]; cbn [od_range fst snd]; unfold am1_A; cbn [am_mem am_set_links]; rewrite loc_mem8; lia)
             | (destruct Hl as [<-|[]]; exists (OD_bnc MA_ e_bncdec); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_bounces; clear - Hsc; lia)
             | (destruct Hl as [<-|[]]; exists (OD_act (v (vptr MA_))); split; [cbn; tauto|]; cbn [od_range fst snd]; rewrite loc_ctx; unfold CTX_active; clear - Hsc; lia) ].
Qed.

Lemma T2_ok : ltac2:(tb__ "0|0|
S55S11aVrhoW;R1A2VTR;Z0S181Sb8VK;S12fR2A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3F_;FrhoA;").
Proof using CS EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv RR Rg am0.
  intros rhoA HagA.
  apply (seg_run 300 ST2_D2ns LT2_D2ns _ rhoA ST2_len ST2_next runT2_D2ns HagA).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  pose proof postR as (Hf0 & g & am' & HI' & Hg' & Hu' & Hsc' & Hcs' & Hidx' & Hheads' & Hub').
  rewrite hdR' in Hg'. injection Hg' as <-.
  pose proof (usedX_MT _ _ _ _ Hu') as [MU _]. rewrite MT_R' in MU. injection MU as <-.
  pose proof Hmaskv as MR.
  destruct (ze_ctz (v 171) maskv ze171 MR) as [EC RC].
  rewrite (ctz32_lowbit (t_mask AM3)) in HI', Hidx' by (clear - Hmv Hmaskv; lia).
  rewrite <- Hmv in HI', Hidx'.
  destruct (leaf3 LT2_D2ns _ _ _ ST2_D2ns Lf LT2_D2ns_shape Hin) as [EL|[EL|EL]]; rewrite EL in HsmF.
  - assert (OUT : ~ (7 <= sc < 39)) by exact (bnc_out_of MA_ rhoF _ _ HagF (conj HsmF HK') f20).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_D2ns 0 ST2_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 0%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_D2ns 0 ST2_D2ns) _ _ dsF20 dsC20 (LT2_objs 0%nat ltac:(repeat constructor)) match20 HsmF vars20 sem20
              ltac:(rewrite <- chg20; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_introl OUT)) (okC_20 (or_introl OUT)) locs2_01
              (LT2_pc 0%nat ltac:(repeat constructor)) (LT2_cs 0%nat ltac:(repeat constructor)) (LT2_fregs 0%nat ltac:(repeat constructor)) (LT2_fcsr 0%nat ltac:(repeat constructor)) (LT2_resv 0%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f21b).
    assert (B0 : bnc = 0) by exact (bnc_zero_of rhoF _ _ HagF (conj HsmF HK') f21a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_D2ns 1 ST2_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 1%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_D2ns 1 ST2_D2ns) _ _ dsF21 dsC21 (LT2_objs 1%nat ltac:(repeat constructor)) match21 HsmF vars21 sem21
              ltac:(rewrite <- chg21; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_01 (or_intror (conj IN B0))) (okC_21 (or_intror (conj IN B0))) locs2_01
              (LT2_pc 1%nat ltac:(repeat constructor)) (LT2_cs 1%nat ltac:(repeat constructor)) (LT2_fregs 1%nat ltac:(repeat constructor)) (LT2_fcsr 1%nat ltac:(repeat constructor)) (LT2_resv 1%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
  - assert (IN : 7 <= sc < 39) by exact (bnc_in_of MA_ rhoF _ _ HagF (conj HsmF HK') f22b).
    assert (BN : bnc <> 0) by exact (bnc_nz_of rhoF _ _ HagF (conj HsmF HK') f22a).
    assert (EI : bv_unsigned (eval rhoF (reg_sv (lfs LT2_D2ns 2 ST2_D2ns) 10)) = ctz32 maskv).
    { rewrite (LT2_a0 2%nat ltac:(repeat constructor)). rewrite (EVu rhoF _ HagF) by reflexivity. exact EC. }
    eapply (post_okH tr md msF rhoF EmW Evm HagF (lfs LT2_D2ns 2 ST2_D2ns) _ _ dsF22 dsC22 (LT2_objs 2%nat ltac:(repeat constructor)) match22 HsmF vars22 sem22
              ltac:(rewrite <- chg22; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok) sR' _ _ HI' xraw_R' (delta_2 IN BN) (okC_22 IN BN) locs2_2
              (LT2_pc 2%nat ltac:(repeat constructor)) (LT2_cs 2%nat ltac:(repeat constructor)) (LT2_fregs 2%nat ltac:(repeat constructor)) (LT2_fcsr 2%nat ltac:(repeat constructor)) (LT2_resv 2%nat ltac:(repeat constructor)) Hsm_pre ltac:(rewrite EI; clear - RC; lia) HKc' Hsc_rho Hreq_rho pA (am_final AM3)).
    + rewrite EI. reflexivity. + exact hdR'. + exact Hu'. + exact Hsc'. + clear - Hreq Hcs'; lia. + rewrite EI. exact Hidx'. + intros c Hc. apply Hheads'; clear - Hc; lia. + exact Hub'.
    + exact taR. + rewrite <- Hmv; exact Hmaskv. + rewrite <- Hmv. exact EI.
Qed.
End T2.

Theorem variant_D2ns : ltac2:(tb__ "0|0|
VTR;Z0S181Sb8VK;S130VrhoW;A4S163VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVact HVf0 HVpart HVskip HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hmv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv Hsv RR Rg am0.
  pose proof (aidx_range MA_) as AR. pose proof last_R as LR. pose proof cnt1_ge as CG. pose proof size_range as [SR _].
  destruct (span_facts sc (am_aidx (mam MA_)) Hsc ltac:(lia) HVpart) as [EX LE]. fold cnt1 in LE.

  apply (tr_seq _ (fun w => exists rho0, (agrees rhoW rho0 /\ LINV (span0_of sc (am_aidx (mam MA_))) (am_aidx (mam MA_) + 2) rho0) /\ SymSoundR.SP segsU K SL_D2ns rho0 w)).
  { apply (seg_run 300 SA_D2ns LA_D2ns _ rhoW eq_refl eq_refl runA_D2ns (agrees_refl rhoW)).
    intros LfA rhoA w HinA HagA HSPA.
    rewrite (single_leaf LA_D2ns _ SA_D2ns LfA LA_D2ns_shape HinA) in HSPA. change (lfs LA_D2ns 0 SA_D2ns) with LA_D2nss in HSPA.
    destruct (loop_entry MA_ LA_D2nss SL_D2ns (fst DL_D2ns) swf_SL sd_A dA_ok keysA setsA_vars setsA_hi varsA inA no1A rhoA w HagA HSPA) as (Hag0 & HINV0 & HSP0).
    exists (setp rhoA (setsA (fst DL_D2ns))). split; [split; assumption | exact HSP0]. }

  apply tr_ex. intros rho0. apply tr_pure. intros [Hag0 HINV0].
  apply (tr_seq _ (POST SX_D2ns)).
  { apply (span_loop_sound MA_ SL_D2ns L0 L1 SX_D2ns LL_D2ns (fst DX_D2ns) runL_D2ns LL_eq SL_len SL_next SL_regs ren_chk L0_same L0_5 L0_14 L0_16 T0f T1f L1_14
             swf_SX sd_X dX_ok keysX setsX_vars setsX_hi varsX xeX 300%nat _ _ rho0 Hag0 HINV0).
    - unfold span0_of, UNIT. nia.
    - lia.
    - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - unfold span0_of, UNIT. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. nia.
    - exact EX.
    - rewrite Hsv. reflexivity. }

  apply from_POST. intros rhoX HagX.
  apply (tr_seq _ (fun w => (span_cnt am1_A = spanv /\ POST ST0_D2ns w) \/ (span_cnt am1_A = am_last (mam MA_) + 1 /\ POST ST2_D2ns w))).
  { apply (seg_run 300 SX_D2ns LX_D2ns _ rhoX SX_len SX_next runX_D2ns HagX).
    intros Lf rhoY w Hin HagY HSPY.
    destruct (leaf4 LX_D2ns _ _ _ _ SA_D2ns Lf LX_D2ns_shape Hin) as [EL|[EL|[EL|EL]]]; rewrite EL in HSPY.
    - assert (CS : span_cnt am1_A = spanv) by (rewrite Hsv; apply cnt_S; rewrite <- Hsv; exact (cnt_lt_of MA_ rhoY _ w HagY HSPY fX0)).
      left. split; [exact CS|]. exists rhoY. split; [exact HagY|].
      apply (linkT (lfs LX_D2ns 0 SA_D2ns) ST0_D2ns (e_maskG MA_ (EB0 MA_)) (snd DT0_D2ns) rhoY _ swf_ST0 sd_0 HagY); try assumption.
      + reflexivity.
      + reflexivity. + exact (ME0 CS). + exact nf_incl0. + exact ST0_vars. + exact ST0_sup. + exact ZF_ST0.
    - exfalso. assert (CS : span_cnt am1_A = spanv) by (rewrite Hsv; apply cnt_S; rewrite <- Hsv; exact (cnt_lt_of MA_ rhoY _ w HagY HSPY fX1b)).
      pose proof (eq0_of (e_maskG MA_ (EB0 MA_)) rhoY _ w HagY HSPY fX1 eq_refl eq_refl) as Z0.
      rewrite (ME0 CS) in Z0. apply HVmask3. rewrite <- Hmv. apply (proj1 (sx32_zero_iff maskv ltac:(pose proof Hmaskv; lia))). exact Z0.
    - assert (CS : span_cnt am1_A = am_last (mam MA_) + 1) by (apply cnt_L; rewrite <- Hsv; exact (cnt_ge_of MA_ rhoY _ w HagY HSPY fX2)).
      right. split; [exact CS|]. exists rhoY. split; [exact HagY|].
      apply (linkT (lfs LX_D2ns 2 SA_D2ns) ST2_D2ns (e_maskG MA_ (EB2 MA_)) (snd DT2_D2ns) rhoY _ swf_ST2 sd_2 HagY); try assumption.
      + reflexivity.
      + reflexivity. + exact (ME2 CS). + exact nf_incl2. + exact ST2_vars. + exact ST2_sup. + exact ZF_ST2.
    - exfalso. assert (CS : span_cnt am1_A = am_last (mam MA_) + 1) by (apply cnt_L; rewrite <- Hsv; exact (cnt_ge_of MA_ rhoY _ w HagY HSPY fX3b)).
      pose proof (eq0_of (e_maskG MA_ (EB2 MA_)) rhoY _ w HagY HSPY fX3 eq_refl eq_refl) as Z0.
      rewrite (ME2 CS) in Z0. apply HVmask3. rewrite <- Hmv. apply (proj1 (sx32_zero_iff maskv ltac:(pose proof Hmaskv; lia))). exact Z0. }
  apply tr_disj.
  - apply tr_pure. intros CS. apply from_POST. intros rhoA HagA. exact (T0_ok CS rhoA HagA).
  - apply tr_pure. intros CS. apply from_POST. intros rhoA HagA. exact (T2_ok CS rhoA HagA).
Qed.

End VD2ns.
End Mal_aslot_VD2ns.

Module Mal_aslot_VE.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ta_post0_of X U s sc s' : ltac2:(tb__ "0|4|
S7bVX;S36S2fS98S3eA2A1M0VU;Vs;A4S1S84Z0M1Vsc;A2S86Vsc;Z30A2A2S0Sa1S99S2fS3eS99A2M2A2Sa7Vsc;Vs;A2Sa0S99G2S33S3eS99G1Vs';A4A3A3S1S7bVX;G0VU;Vs';A4S1S0S31S98A1M3S74Vs';Vsc;A2S36S98A1A3S1S3eS84G1R1A2S2S0S3eR2Vsc;A3A1S0G3S74Vs';R3A2S74Vs;R3A2A3F_;F_;Fc;S1a9Vs;Vs';A2A2A2A2F_;F_;F_;").
Proof.
  intros HI Hsc E.
  pose proof (try_avail_spec X U s sc (fun r => fst r = 0 -> Inv X None U (snd r) /\ active_hd (snd r) sc = None /\ (forall c, 0 <= c -> c <> sc -> active_hd (snd r) c = active_hd s c) /\ ub_same s (snd r)) HI Hsc
                ltac:(intros s1 H1 H2 H3 H4 _; cbn [fst snd]; auto) ltac:(intros f1 s1 [Hf _] H0; cbn [fst] in H0; exfalso; exact (Hf H0))) as T0.
  rewrite E in T0. cbn [itok fst snd] in T0. exact (T0 eq_refl).
Qed.

Section VE.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (byM0 byA byB byC byP bnc gd maskv spanv : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S84Z0Vreq;A2S84S85Vreq;Sa8A2Sa4Vsc;A1A2A2").
Variable m0 : sptr.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs;Vsc;A2S35S98Vm0;A2A3").
Variable rest : list sptr.
Hypothesis Rg : ltac2:(tb__ "0|0|
S7eS7dVX;Vs;Vsc;A3S35S98Vm0;A2S2bS98Vm0;Vrest;A3A3").
Local Abbreviation pM0 := (@U.Mal_aslot__G1.Mal_aslot_I.pM0 m0).
Local Notation "§56§ h__" := (h__ s m0) (at level 10, h__ global).
Local Abbreviation pA := (§56§ U.Mal_aslot__G1.Mal_aslot_I.pA).
Local Abbreviation pB := (§56§ U.Mal_aslot__G1.Mal_aslot_I.pB).
Local Abbreviation pC := (§56§ U.Mal_aslot__G1.Mal_aslot_I.pC).
Local Abbreviation pP := (§56§ U.Mal_aslot__G1.Mal_aslot_I.pP).
Local Abbreviation mptr := (§56§ U.Mal_aslot__G1.Mal_aslot_I.mptr).
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte byM0 byA byB byC byP).
Local Abbreviation mam := (§56§ U.Mal_aslot__G1.Mal_aslot_I.mam).
Local Abbreviation rcls := (@U.Mal_aslot__G1.Mal_aslot_I.rcls rest).
Local Abbreviation cls1 := (@U.Mal_aslot__G1.Mal_aslot_I.cls1 s X sc Hsc m0 rest Rg).
Local Notation "§57§ h__" := (h__ s X U sc HI Hsc m0 Hhd) (at level 10, h__ global).
Local Abbreviation mam_used := (§57§ U.Mal_aslot__G1.Mal_aslot_I.mam_used).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S199S15aVX;S36S2fS98S3eA2A1VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis Hbytes : ltac2:(tb__ "0|3|
S20S1S1S84Z0M0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6M1A2S86G1Z100A2A2S1S0S3eS89G1Z20A2S9cS8Vs;Vm0;R1A3M2A1A3S2S0S3eSa5G2A1G0A3A1S0S3eS1cVbyM0;VbyA;VbyB;VbyC;VbyP;R2A6S9cS8Vs;Vm0;R2A3A1A3F_;A2A2Fx;").
Hypothesis Hbnc : 0 <= bnc < 256.
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hmaskv : 0 < maskv < 2 ^ 32.
Hypothesis Hspanv : 0 <= spanv <= 300.
Local Abbreviation zA := (@U.Mal_aslot__G1.Mal_aslot_I.zA L).
Local Abbreviation mem_R := (@U.Mal_aslot__G1.Mal_aslot_I.mem_R s L X U sc bnc gd HI Hsc m0 Hhd rd0 wok0 vm HMI Hbnc Hgd).
Local Notation "§58§ h__" := (h__ s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv m0) (at level 10, h__ global).
Local Abbreviation rho1 := (§58§ U.Mal_aslot__G1.Mal_aslot_I.rho1).
Local Abbreviation zr1 := (§58§ U.Mal_aslot__G1.Mal_aslot_I.zr1).
Local Abbreviation zl1 := (§58§ U.Mal_aslot__G1.Mal_aslot_I.zl1).
Local Abbreviation ze_lit := (§58§ U.Mal_aslot__G1.Mal_aslot_I.ze_lit).
Local Abbreviation vptr := (@U.Mal_aslot__G1.Mal_aslot_I.vptr).
Local Abbreviation vmem := (@U.Mal_aslot__G1.Mal_aslot_I.vmem).
Local Abbreviation vavail := (@U.Mal_aslot__G1.Mal_aslot_I.vavail).
Local Abbreviation vfreed := (@U.Mal_aslot__G1.Mal_aslot_I.vfreed).
Local Abbreviation vbits := (@U.Mal_aslot__G1.Mal_aslot_I.vbits).
Local Notation "§59§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI Hsc m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd) (at level 10, h__ global).
Local Abbreviation ze_ptr := (§59§ U.Mal_aslot__G1.Mal_aslot_I.ze_ptr).
Local Abbreviation ze_mem := (§59§ U.Mal_aslot__G1.Mal_aslot_I.ze_mem).
Local Abbreviation ze_avail := (§59§ U.Mal_aslot__G1.Mal_aslot_I.ze_avail).
Local Abbreviation ze_freed := (§59§ U.Mal_aslot__G1.Mal_aslot_I.ze_freed).
Local Abbreviation ze_bits := (§59§ U.Mal_aslot__G1.Mal_aslot_I.ze_bits).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sc0Q40S49Vrho;PaA2A2M0A2S0S3eS89G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S174Z40Sc0Q40S49Vrho;PfA2A2A2M0S8aS186Z0A1A1A2S84S8aS8cZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S84S15eVL;A1S85Sc0Q40M0S49Vrho;PaA2A2S174Z40Sc0G0S49Vrho;PfA2A2A2A2A2").
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Abbreviation ZF_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.ZF_base5 s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd Hsp Hdepth Hsp_high).
Local Abbreviation zf_ptr_ne0 := (§59§ U.Mal_aslot__G1.Mal_aslot_I.zf_ptr_ne0).
Local Abbreviation zf_avail_eq0 := (§59§ U.Mal_aslot__G1.Mal_aslot_I.zf_avail_eq0).
Local Abbreviation zf_freed_eq0 := (§59§ U.Mal_aslot__G1.Mal_aslot_I.zf_freed_eq0).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;Vrd0;S13dSb8VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SbfQ40A1S2dF_;Vwok0;S13eSb8VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z60A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ecR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z20A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ccR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hbytes_rd : ltac2:(tb__ "0|2|
S20S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S22VL;S9bS8Vs;Vm0;R1A3A1A2Z8A2A2A3S35G1Sc1G0S1cVbyM0;VbyA;VbyB;VbyC;VbyP;R1A6A2A2A3Fx;").
Hypothesis Hbnc_rd : ltac2:(tb__ "0|2|
S0S31SbfQ8M0A1M1A1S13dSb8VmW;Sc1Q40S85S85Z5a3d0Z369A2Vsc;A2A2A3S35G1Sc1G0Vbnc;A2A2A3").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S15dS15bVrd0;SbfQ40A1S2eL_;A2S15cS15aA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S15bS13dSb8VmW;A2S13eSb8VmW;A2A2").
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation optrZ := (@U.Mal_aslot__G1.Mal_aslot_I.optrZ L).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_at).
Local Abbreviation od_ok := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok).
Local Notation "§60§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation od_hold := (§60§ U.Mal_aslot__G1.Mal_aslot_I.od_hold).
Local Abbreviation od_range := (@U.Mal_aslot__G1.Mal_aslot_I.od_range s L sc m0).
Local Abbreviation od_pairwise := (§56§ U.Mal_aslot__G1.Mal_aslot_I.od_pairwise).
Local Notation "§61§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds) (at level 10, h__ global).
Local Abbreviation carve := (§61§ U.Mal_aslot__G1.Mal_aslot_I.carve).
Local Abbreviation od_ok_meta_entry := (§59§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_meta_entry).
Local Abbreviation od_ok_act_entry := (§59§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_act_entry).
Hypothesis Hbnc_val : ltac2:(tb__ "0|1|
S1S84Z7M0Vsc;A2S86Vsc;Z27A2A2S0S3eVbnc;SacS87Vsc;G0A2Sa2Vs;A1A2A3F_;").
Local Abbreviation od_ok_got := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_got).
Local Abbreviation od_ok_guard := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard).
Local Abbreviation od_ok_sct := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct).
Local Abbreviation od_ok_ctz := (§58§ U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S19aSb8VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cS114A1S115OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation seg_run := (@U.Mal_aslot__G2.Mal_aslot_W.seg_run s L sc req rho byM0 byA byB byC byP bnc gd maskv spanv Hsc m0 Hbnc Hgd mW Kc RF GF TR RR K HK).
Local Abbreviation od_chg_ok := (@U.Mal_aslot__G2.Mal_aslot_W.od_chg_ok sc).
Local Abbreviation od_sem := (@U.Mal_aslot__G2.Mal_aslot_W.od_sem).
Local Abbreviation objs_matchb := (@U.Mal_aslot__G2.Mal_aslot_W.objs_matchb).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Notation "§62§ h__" := (h__ s X U HI) (at level 10, h__ global).
Local Abbreviation ND := (§62§ U.Mal_aslot__G3.Mal_aslot_T.ND).
Local Abbreviation active_len := (§62§ U.Mal_aslot__G3.Mal_aslot_T.active_len).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho bnc gd Hsc Hbnc Hgd Hsp).
Local Abbreviation xraw_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.xraw_set_hd X).
Local Abbreviation keys_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.keys_set_hd).
Local Abbreviation am_next_mam := (§57§ U.Mal_aslot__G3.Mal_aslot_T.am_next_mam).
Local Abbreviation xraw_upd_meta_ptr := (§57§ U.Mal_aslot__G3.Mal_aslot_T.xraw_upd_meta_ptr).
Local Abbreviation loc_ctx := (@U.Mal_aslot__G3.Mal_aslot_T.loc_ctx s L X U rd0 wok0 vm HMI).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho bnc gd Hsc m0 Hbnc Hgd).
Local Notation "§63§ h__" := (h__ s L X U sc req rho byM0 byA byB byC byP bnc gd maskv spanv HI HXr Hsc Hreq m0 Hhd rest Rg rd0 wok0 vm HMI Hbytes Hbnc Hgd Hmaskv Hspanv Hsp Hdepth Hsp_high mW Erd Ewok ms Hrom Hm_sct Hm_ctz Hbytes_rd Hbnc_rd Hgd_holds Hbnc_val Kc) (at level 10, h__ global).
Local Abbreviation post_G := (§63§ U.Mal_aslot__G10.Mal_aslot_G.post_G).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Local Notation mnext := (RingFacts.mnext s).
Local Notation mprev := (RingFacts.mprev s).

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;VmW;S59Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S116Vvm;S117Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cS114A1M0S115VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S115R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4fSb8Vrho;S188S187A1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PdA2A2Vreq;A3").
Hypothesis Htier : ltac2:(tb__ "0|0|
S84S174Z40Sc0Q40S49Vrho;S1a3A2A2A2S8aS186S8eS189Vsc;A1A1A1A1A2").
Hypothesis Htp : tp_ok C_U rho.

Hypothesis Hr : rcls = 1%nat.
Hypothesis HVa0 : ltac2:(tb__ "0|0|
S0S3eSadS8Vs;Vm0;S6A3A1Z0A3").
Hypothesis HVf0 : ltac2:(tb__ "0|0|
S0S3eSa3S8Vs;Vm0;S6A3A1Z0A3").

Let am0 : ameta := mam MM0.
Lemma HM0 : ltac2:(tb__ "0|0|
S0S31S9aA1S75Vs;S9Vm0;A1A2S35S9aS9dVam0;A1A2A3"). Proof using HI Hhd Hsc. exact (proj2 (proj2 (mam_used MM0))). Qed.
Definition CLS : Prop := ltac:(let t := type of (cls1 Hr) in exact t).
Lemma HCLS : CLS. Proof using Hr Hsc Rg. exact (cls1 Hr). Qed.
Ltac use_cls := pose proof HCLS as HH; unfold CLS in HH; decompose [and] HH; clear HH.
Ltac ring_norm := use_cls; cbn [mptr] in *; unfold U.Mal_aslot__G1.Mal_aslot_I.pP, U.Mal_aslot__G1.Mal_aslot_I.pC, U.Mal_aslot__G1.Mal_aslot_I.pB, U.Mal_aslot__G1.Mal_aslot_I.pA in *.
Ltac solve_link := ring_norm; first [reflexivity | assumption | symmetry; assumption | congruence].
Ltac solve_neq := ring_norm; first [assumption | apply not_eq_sym; assumption | congruence].

Definition dsR : list od := ltac2:(tb__ "0|1|
S2bS5S11S2bS5S12S2bS5SdS97S1aS6A1A1M0A1S2bS5SbS6G0G0S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S2bS5S14S2bS5S13S32S5A1A3A3A3A3A3A3").

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cS126A1S2bS45S19SccS5S45SfS17dA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_E = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma okR : Forall od_ok dsR.
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp.
  unfold dsR. repeat apply Forall_cons; try apply Forall_nil.
  - apply od_ok_got.
  - apply od_ok_guard.
  - apply od_ok_act_entry.
  - apply od_ok_meta_entry; [rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link | rewrite (ze_ptr MM0); cbn [mptr]; f_equal; solve_link].
  - apply od_ok_sct.
  - apply od_ok_ctz.
Qed.
Lemma pwR : od_pairwise dsR.
Proof using . drop_sp. cbn. repeat split; try exact I; try apply Forall_nil; repeat (apply Forall_cons; [cbn; try exact I; solve_neq|]); apply Forall_nil. Qed.

Lemma ZF_R : ltac2:(tb__ "0|0|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfS17Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;AfA2S47S126A1A3").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hdepth Hgd Hhd Hsc Hsp Hsp_high.
  change (ss_facts SA_E) with (F_base5 ++ [SPNot (SPBranch BC_EQ (v (vptr MM0)) (SLit 0)); SPBranch BC_EQ (SExt true 32 (v (vavail MM0))) (SLit 0); SPBranch BC_EQ (SExt true 32 (v (vfreed MM0))) (SLit 0)]).
  apply Forall_app. split; [apply ZF_base5|].
  repeat (apply Forall_cons; [first [apply (zf_ptr_ne0 MM0) | apply (zf_avail_eq0 MM0); assumption | apply (zf_freed_eq0 MM0); assumption]|]). apply Forall_nil.
Qed.

Definition S0R : sstate := ltac2:(tb__ "0|0|
S5dZ2126cSbaSb9S51S36S41A1S2bS45S19S32S45A1A3S47S126A1S122S3aA9").

Lemma carve_R : ltac2:(tb__ "0|1|
S4fSb8VrhoW;S17eS33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4M0A4S4fSb8VrhoW;S126G0A4F_;").
Proof using Erd Ewok HI HMI HXr Hbnc Hbnc_rd Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hrom Hsc Hsp Hsp_high Hspanv Rg.
  intros Hsm. change SA_E with (mkSS (ss_pc S0R) (ss_regs S0R) (ss_fregs S0R) (ss_fcsr S0R) (ss_resv S0R) (ss_objs S0R ++ map obj_of dsR) (ss_facts S0R) NXA (ss_lenient S0R)).
  apply (carve S0R dsR NXA tr md eq_refl okR pwR swf_SA Hsm).
Qed.

Lemma ent_k dsF : ltac2:(tb__ "0|0|
S0S38S3cS5VdsF;A2S3cS5S17dA2A3S5S92S5R1VdsF;A3S3S23Vs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;R2A10S92S5R2S14cS17dVdsF;A2A3A2F_;Fd;F_;").
Proof using HI HMI Hbnc Hbytes Hgd Hhd Hr Hsc Rg. drop_sp. intros Hl. apply (ent_changed od_ok dsR dsF Hl okR). Qed.

Definition sE : astate := ltac2:(tb__ "0|0|
S14aVs;Vsc;S9Vm0;A1Vam0;A4").

Lemma next0 : ltac2:(tb__ "0|0|
S0S31S98A1SaeVam0;A1S35S98S9Vm0;A1A2A3").
Proof using HI Hhd Hr Hsc Rg. drop_sp. unfold am0. rewrite (am_next_mam MM0). f_equal. cbn [mptr]. solve_link. Qed.
Lemma hd_none : ltac2:(tb__ "0|1|
S0S31S98A1S74S113Vsc;S36S98A1M0Vs;A3Vsc;A2G0A3").
Proof using HI Hbnc Hgd Hsc Hsp. try clear Hsp_high. try clear Hdepth. apply active_hd_set_hd; [exact active_len | exact Hsc]. Qed.
Lemma taE : ltac2:(tb__ "0|1|
S0Sa1S99S2fS3eS99A2M0A2Sa7Vsc;Vs;A2Sa0S99G0S33S3eS99Z0S179A4A3A3").
Proof using HI HVa0 HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. exact (ta_empty s sc pM0 am0 Hhd HM0 HVa0 HVf0 next0 hd_none). Qed.
Lemma postE : ltac2:(tb__ "0|1|
S1S7bVX;S36S2fS98S3eA2A1VU;S179A4S1S0S31S98A1M0S74S179Vsc;A2S36S98A1A3S1S3eS84Z0R1A2S2S0S3eR2Vsc;A3A1S0G0S74S179R3A2S74Vs;R3A2A3F_;F_;Fc;S1a9Vs;S179A2A2A2A2").
Proof using HI HVa0 HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. exact (ta_post0_of X U s sc sE HI Hsc taE). Qed.
Lemma xrawE : xraw X sE.
Proof using HI HXr Hhd Hsc. drop_sp. unfold sE, s1_empty. change pM0 with (mptr MM0). apply xraw_upd_meta_ptr. apply xraw_set_hd. exact HXr. Qed.
Lemma MT_E : ltac2:(tb__ "0|1|
S0S31S9aA1S75S179S9Vm0;A1A2S35S9aS9dSaaS36S98A1M0G0Vam0;A3A1A2A3").
Proof using . drop_sp. unfold sE, s1_empty. apply MT_upd_same. Qed.
Lemma deltaE : ltac2:(tb__ "0|0|
S112Vs;S179S30S73S2bS73S77S85S7aS88Z8Vsc;A2A2A1S32S73A1A3S111S9Vm0;A1A1A3A3").
Proof using HI Hbnc Hgd Hhd Hr Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold sE, s1_empty. eapply delta_trans; [apply delta_sh; lia|].
  apply (delta_su_keep _ pM0 am0); [rewrite keys_set_hd; exact ND | rewrite MT_set_hd; exact HM0 | apply same_shape_links | reflexivity].
Qed.

Definition LE : sstate := lfs LA_E 0 SA_E.
Definition dsF : list od := ltac2:(tb__ "0|1|
S2bS5S11S2bS5S12S2bS5SdS43Z0A1M0A1S2bS5SbS6G0G0S42P7bA1S42P7cA1S42P7dA1S42P7eA1A7S2bS5S14S2bS5S13S32S5A1A3A3A3A3A3A3").
Definition dsC : list od := ltac:(let x := eval vm_compute in (changed dsR dsF) in exact x).
Lemma matchF : ltac2:(tb__ "0|0|
S0S2dS15fS94S45S4cS17bA1A2S17aA2S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma varsF : ltac2:(tb__ "0|0|
S0S2dS93S45S14fS118A1SccS5S45SfS17aA4A3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma semF : ltac2:(tb__ "0|0|
S0S2dS93S5S161S17aA3S2eA3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chgF : ltac2:(tb__ "0|0|
S0S2cS5A1S14cS17dS17aA2S17cA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma dsC_eq : ltac2:(tb__ "0|1|
S0S2cS5A1S17cS2bS5SdS43Z0A1M0A1S2bS5SbS6G0G0S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7S32S5A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma dsF_head : ltac2:(tb__ "0|1|
S4S2cS5A1M0G0S0G0S17aS2bS5S11S2bS5S12S2bS5SdS43Z0A1A1R1A3A3A3A3Lt;A2"). Proof using . eexists. reflexivity. Qed.
Lemma LE_objs : ltac2:(tb__ "0|1|
S0S2cS45A1S4cS17bA1M0S2bS45S162S5bS96S45S19G0A3A1A1S94S45G0A2A3A3"). Proof using . reflexivity. Qed.
Lemma LE_stk : ltac2:(tb__ "0|0|
S0S2cS4dA1S5bS96S45S19S4cS17bA1A3A1S18fA3"). Proof using . vm_compute. reflexivity. Qed.
Lemma LE_pc : ss_pc LE = 0x2144c. Proof using . reflexivity. Qed.
Lemma LE_regs : regsG_okb LE = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LE_fregs : ltac2:(tb__ "0|0|
S0S2cS41A1S54S17bA1Sb9A3"). Proof using . reflexivity. Qed.
Lemma LE_fcsr : ltac2:(tb__ "0|0|
S0S57S53S17bA1S51A3"). Proof using . reflexivity. Qed.
Lemma LE_resv : ss_resv LE = None. Proof using . reflexivity. Qed.

Lemma ok_act' : ltac2:(tb__ "0|0|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S179SdS43Z0A1A1A11").
Proof using HI HVa0 HVf0 Hbnc Hgd Hhd Hr Hsc Hsp Rg. try clear Hsp_high. try clear Hdepth. cbn [od_ok_at]. split; [reflexivity|]. rewrite (proj1 (proj2 postE)). rewrite ze_lit. reflexivity. Qed.
Lemma ok_meta' : ltac2:(tb__ "0|1|
ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S179SbS6S43Z0A1M0G0S97S16S6A1A1S97S1eS6A1A1S97S1fS6A1A1S97S15S6A1A1A7A11").
Proof using HI HMI HVa0 HVf0 Hbnc Hbytes Hgd Hhd Hr Hsc. drop_sp.
  cbn [od_ok_at]. repeat (split; [reflexivity|]).
  exists (am_set_links None None am0). split; [exact MT_E|].
  unfold am0. cbn [am_prev am_next am_mem am_avail am_freed am_set_links optrZ].
  split; [rewrite ze_lit; reflexivity|]. split; [rewrite ze_lit; reflexivity|].
  split; [apply ze_mem|]. split; [rewrite ze_avail; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  split; [rewrite ze_freed; apply Z.mod_small; pose proof (mem_R MM0); lia|].
  rewrite ze_bits. unfold meta_bits. cbn [am_last am_sc am_maplen am_set_links]. reflexivity.
Qed.
Lemma okC : ltac2:(tb__ "0|0|
S5S92S5R1S17cA3S1S92S5R2S17aA3S1ScVs;VL;Vsc;Vreq;Vrho;VbyM0;VbyA;VbyB;VbyC;VbyP;Vbnc;Vgd;Vmaskv;Vspanv;Vm0;S179R2A11S160Vsc;R2A2A2A2F_;Fd;").
Proof using HI HMI HVa0 HVf0 Hbnc Hbnc_val Hbytes Hdepth Hgd Hhd Hmaskv Hr Hreq Hsc Hsp Hspanv Rg. try clear Hsp_high. intros d Hd. rewrite dsC_eq in Hd. repeat (destruct Hd as [<-|Hd]; [split; [cbn; tauto|]; split; [first [exact ok_act' | exact ok_meta'] | exact I]|]). destruct Hd. Qed.
Lemma locsE : ltac2:(tb__ "0|2|
S73S92S73R1S30S73S2bS73S77S85S7aS88Z8Vsc;A2A2A1S32S73A1A3S111S9Vm0;A1A1A3A3S4S5S5S1S92S5R1S17cA3S1S84S34S3eS3eS1dVs;VL;Vsc;Vm0;R1A5M0A3S79VL;R3A2M1A2S86G1S37S3eS3eG0A3A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hbnc Hbnc_val Hdepth Hgd Hmaskv Hr Hreq Hsc Hsp Hspanv. try clear Hsp_high.
  intros l Hl. rewrite dsC_eq. change pM0 with (mptr MM0) in Hl.
  apply in_app_iff in Hl as [Hl|Hl].
  - destruct Hl as [<-|[]]. exists (OD_act (SLit 0)). split; [cbn; tauto|]. cbn [od_range fst snd]. rewrite loc_ctx. unfold CTX_active. lia.
  - eexists. split; [right; left; reflexivity|]. cbn [od_range fst snd]. pose proof (in_meta_locs_range MM0 l Hl). lia.
Qed.

Theorem variant_E : ltac2:(tb__ "0|0|
VTR;Z0S181Sb8VK;S126VrhoW;A4S191VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HI HK HKc HMI HVa0 HVf0 HXr Hbnc Hbnc_rd Hbnc_val Hbytes Hbytes_rd Hdepth Hgd Hgd_holds Hhd Hm_ctz Hm_sct Hmaskv Hr Hreq Hreq_rho Hrom Hsc Hsc_rho Hsm_pre Hsp Hsp_high Hspanv Htier Htp RR Rg am0.
  apply (seg_run 300 SA_E LA_E _ rhoW eq_refl eq_refl runA_E (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  rewrite (single_leaf LA_E _ SA_E Lf LA_E_shape Hin) in HsmF. change (lfs LA_E 0 SA_E) with LE in HsmF.
  pose proof postE as (HI' & Hhd' & Hheads' & Hub').
  pose proof LE_objs as EO. rewrite LE_stk in EO.
  exact (post_G tr md msF rhoF EmW Evm HagF LE _ dsF dsC EO matchF HsmF varsF semF
           ltac:(rewrite <- chgF; apply ent_k; reflexivity) (fun d Hd Hok => od_hold d Hok)
           sE _ HI' xrawE deltaE okC locsE LE_pc LE_regs LE_fregs LE_fcsr LE_resv dsF_head Hsm_pre Hsc_rho Hreq_rho Htier Htp HKc' Hhd' Hheads' Hub' taE).
Qed.
End VE.
End Mal_aslot_VE.

Module Mal_aslot_VN.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G2.Mal_aslot_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G3.Mal_aslot_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G9.Mal_aslot_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition m0d : sptr := SP 0 0.
Lemma bnc0_ok : 0 <= 0 < 256. Proof. lia. Qed.
Lemma maskv1_ok : 0 < 1 < 2 ^ 32. Proof. lia. Qed.
Lemma spanv0_ok : 0 <= 0 <= 300. Proof. lia. Qed.

Section N.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (sc req : Z).
Variable rho : valuation.
Variables (gd : Z).
Hypothesis HI : ltac2:(tb__ "0|0|
S7bVX;S36S2fS98S3eA2A1VU;Vs;A4").
Hypothesis HXr : xraw X s.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : ltac2:(tb__ "0|0|
S1S84Z0Vreq;A2S84S85Vreq;Sa8A2Sa4Vsc;A1A2A2").
Local Abbreviation mbyte := (@U.Mal_aslot__G1.Mal_aslot_I.mbyte 0 0 0 0 0).
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S199S15aVX;S36S2fS98S3eA2A1VU;S156Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Abbreviation Hctx := (@U.Mal_aslot__G1.Mal_aslot_I.Hctx s L X U rd0 wok0 vm HMI).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Abbreviation member_val := (@U.Mal_aslot__G1.Mal_aslot_I.member_val s L 0 0 0 0 0 m0d).
Local Abbreviation rw1v := (@U.Mal_aslot__G1.Mal_aslot_I.rw1v s L sc req 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation rw1 := (@U.Mal_aslot__G1.Mal_aslot_I.rw1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation rho1 := (@U.Mal_aslot__G1.Mal_aslot_I.rho1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation rw1_low := (@U.Mal_aslot__G1.Mal_aslot_I.rw1_low s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zr1 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zl1 := (@U.Mal_aslot__G1.Mal_aslot_I.zl1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_zl1_any := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_zl1_any s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zl1_1 := (@U.Mal_aslot__G1.Mal_aslot_I.zl1_1 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zl1_4 := (@U.Mal_aslot__G1.Mal_aslot_I.zl1_4 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_v := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_v s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_12 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_12 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zr1_13 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_13 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc Hreq m0d bnc0_ok Hgd).
Local Abbreviation zr1_170 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_170 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zr1_171 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_171 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_173 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_173 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zr1_174 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_174 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation rw1v_member := (@U.Mal_aslot__G1.Mal_aslot_I.rw1v_member s L sc req 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ze_var := (@U.Mal_aslot__G1.Mal_aslot_I.ze_var s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_v := (@U.Mal_aslot__G1.Mal_aslot_I.ze_v s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_lit := (@U.Mal_aslot__G1.Mal_aslot_I.ze_lit s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_alu := (@U.Mal_aslot__G1.Mal_aslot_I.ze_alu s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_aluw := (@U.Mal_aslot__G1.Mal_aslot_I.ze_aluw s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_mul := (@U.Mal_aslot__G1.Mal_aslot_I.ze_mul s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_ext := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ext s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze_lbytes := (@U.Mal_aslot__G1.Mal_aslot_I.ze_lbytes s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ze12 := (@U.Mal_aslot__G1.Mal_aslot_I.ze12 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ze13 := (@U.Mal_aslot__G1.Mal_aslot_I.ze13 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc Hreq m0d bnc0_ok Hgd).
Local Abbreviation ze170 := (@U.Mal_aslot__G1.Mal_aslot_I.ze170 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ze171 := (@U.Mal_aslot__G1.Mal_aslot_I.ze171 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_172 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_172 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd spanv0_ok).
Local Abbreviation ze172 := (@U.Mal_aslot__G1.Mal_aslot_I.ze172 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd spanv0_ok).
Local Abbreviation ze173 := (@U.Mal_aslot__G1.Mal_aslot_I.ze173 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ze174 := (@U.Mal_aslot__G1.Mal_aslot_I.ze174 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation e_actoff := (@U.Mal_aslot__G1.Mal_aslot_I.e_actoff).
Local Abbreviation e_acthi := (@U.Mal_aslot__G1.Mal_aslot_I.e_acthi).
Local Abbreviation ze_actoff := (@U.Mal_aslot__G1.Mal_aslot_I.ze_actoff s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ze_acthi := (@U.Mal_aslot__G1.Mal_aslot_I.ze_acthi s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation mod_mod_le := (@U.Mal_aslot__G1.Mal_aslot_I.mod_mod_le sc 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation ze_lowbit_sx := (@U.Mal_aslot__G1.Mal_aslot_I.ze_lowbit_sx s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation sx32_lowbit_nz := (@U.Mal_aslot__G1.Mal_aslot_I.sx32_lowbit_nz sc 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation ze_dbidx_sx := (@U.Mal_aslot__G1.Mal_aslot_I.ze_dbidx_sx s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S84Z1000Sc0Q40S49Vrho;PaA2A2M0A2S0S3eS89G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S84S174Z40Sc0Q40S49Vrho;PfA2A2A2M0S8aS186Z0A1A1A2S84S8aS8cZ2Z28A2A1G0A2A2").
Hypothesis Hsp_high : ltac2:(tb__ "0|1|
S84S15eVL;A1S85Sc0Q40M0S49Vrho;PaA2A2S174Z40Sc0G0S49Vrho;PfA2A2A2A2A2").
Local Abbreviation zr1_10 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_10 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation zr1_15 := (@U.Mal_aslot__G1.Mal_aslot_I.zr1_15 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation sp_sum := (@U.Mal_aslot__G1.Mal_aslot_I.sp_sum sc rho 0 gd Hsc bnc0_ok Hgd Hsp Hdepth Hsp_high).
Local Abbreviation F_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.F_base5).
Local Abbreviation ZF_base5 := (@U.Mal_aslot__G1.Mal_aslot_I.ZF_base5 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd Hsp Hdepth Hsp_high).
Local Abbreviation ZF_T := (@U.Mal_aslot__G1.Mal_aslot_I.ZF_T s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd maskv1_ok Hsp).
Local Abbreviation facts_hold := (@U.Mal_aslot__G1.Mal_aslot_I.facts_hold s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;Vrd0;S13dSb8VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0SbfQ40A1S2dF_;Vwok0;S13eSb8VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z60A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ecR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hm_ctz : ltac2:(tb__ "0|1|
S3eS1S84Z0R1A2S86R1Z20A2A2S0S31SbfQ8A1M0A1VmW;Sc1Q40S85Z108ccR2A2A2A1S36G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S15dS15bVrd0;SbfQ40A1S2eL_;A2S15cS15aA1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S15bS13dSb8VmW;A2S13eSb8VmW;A2A2").
Local Abbreviation cell_rw0 := (@U.Mal_aslot__G1.Mal_aslot_I.cell_rw0 s L X U sc rho 0 gd Hsc rd0 wok0 vm HMI bnc0_ok Hgd Hsp mW Erd Ewok).
Local Abbreviation ev1 := (@U.Mal_aslot__G1.Mal_aslot_I.ev1 s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation ev1u := (@U.Mal_aslot__G1.Mal_aslot_I.ev1u s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation cell_view0 := (@U.Mal_aslot__G1.Mal_aslot_I.cell_view0 s L X U sc req rho 0 0 0 0 0 0 gd 1 0 m0d rd0 wok0 vm HMI mW Erd Ewok).
Local Abbreviation soff_of_ev := (@U.Mal_aslot__G1.Mal_aslot_I.soff_of_ev s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation O_stk := (@U.Mal_aslot__G1.Mal_aslot_I.O_stk).
Local Abbreviation O_got := (@U.Mal_aslot__G1.Mal_aslot_I.O_got).
Local Abbreviation O_guard := (@U.Mal_aslot__G1.Mal_aslot_I.O_guard).
Local Abbreviation O_act := (@U.Mal_aslot__G1.Mal_aslot_I.O_act).
Local Abbreviation O_sct := (@U.Mal_aslot__G1.Mal_aslot_I.O_sct).
Local Abbreviation O_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.O_ctz).
Local Abbreviation hold_got := (@U.Mal_aslot__G1.Mal_aslot_I.hold_got s L X U sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d rd0 wok0 vm HMI bnc0_ok Hgd Hsp mW Erd Ewok ms Hrom).
Local Abbreviation hold_guard := (@U.Mal_aslot__G1.Mal_aslot_I.hold_guard s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d rd0 bnc0_ok Hgd Hsp mW Erd ms Hrom Hgd_holds).
Local Abbreviation sctab_image := (@U.Mal_aslot__G1.Mal_aslot_I.sctab_image s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation ctztab_image := (@U.Mal_aslot__G1.Mal_aslot_I.ctztab_image s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation hold_sct := (@U.Mal_aslot__G1.Mal_aslot_I.hold_sct s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW ms Hrom Hm_sct).
Local Abbreviation hold_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.hold_ctz s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW ms Hrom Hm_ctz).
Local Abbreviation ctx_owned := (@U.Mal_aslot__G1.Mal_aslot_I.ctx_owned s L X U sc rho 0 gd HI HXr Hsc rd0 wok0 vm HMI bnc0_ok Hgd Hsp).
Local Abbreviation obj_of := (@U.Mal_aslot__G1.Mal_aslot_I.obj_of).
Local Abbreviation od_ok_at := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok_at s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation od_ok := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation soff1_lit := (@U.Mal_aslot__G1.Mal_aslot_I.soff1_lit s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation rng_lit := (@U.Mal_aslot__G1.Mal_aslot_I.rng_lit s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation sp0 := (@U.Mal_aslot__G1.Mal_aslot_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_aslot__G1.Mal_aslot_I.D0 rho).
Local Abbreviation ev_sp := (@U.Mal_aslot__G1.Mal_aslot_I.ev_sp s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation ev_v15 := (@U.Mal_aslot__G1.Mal_aslot_I.ev_v15 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation rng_stk := (@U.Mal_aslot__G1.Mal_aslot_I.rng_stk s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation ze_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.ze_ctz s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd Hsp).
Local Abbreviation od_ok_got := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok_got s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation od_ok_guard := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok_guard s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation od_ok_sct := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok_sct s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation od_ok_ctz := (@U.Mal_aslot__G1.Mal_aslot_I.od_ok_ctz s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S19aSb8VKc;VRF;VGF;VTR;A5").
Variable K : ltac2:(tb__ "0|0|
S2cS114A1S115OF_;F_;").
Hypothesis HK : implK Kc K.
Let rhoW : valuation := rho1 mW.
Local Abbreviation EV := (@U.Mal_aslot__G2.Mal_aslot_W.EV s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation EVu := (@U.Mal_aslot__G2.Mal_aslot_W.EVu s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation HOLDS := (@U.Mal_aslot__G2.Mal_aslot_W.HOLDS s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation rw_agrees := (@U.Mal_aslot__G2.Mal_aslot_W.rw_agrees s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation seg_run := (@U.Mal_aslot__G2.Mal_aslot_W.seg_run s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW Kc RF GF TR RR K HK).
Local Abbreviation POST := (@U.Mal_aslot__G2.Mal_aslot_W.POST s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation from_POST := (@U.Mal_aslot__G2.Mal_aslot_W.from_POST s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW Kc RF GF TR RR K).
Local Abbreviation leaf_fact := (@U.Mal_aslot__G2.Mal_aslot_W.leaf_fact s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation ZF_holds := (@U.Mal_aslot__G2.Mal_aslot_W.ZF_holds s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation agrees_setp := (@U.Mal_aslot__G2.Mal_aslot_W.agrees_setp s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation linkp := (@U.Mal_aslot__G2.Mal_aslot_W.linkp s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation soff_litX := (@U.Mal_aslot__G2.Mal_aslot_W.soff_litX sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation soff_semX := (@U.Mal_aslot__G2.Mal_aslot_W.soff_semX s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation in_od_ranges_dec := (@U.Mal_aslot__G2.Mal_aslot_W.in_od_ranges_dec s L sc rho 0 gd Hsc m0d bnc0_ok Hgd).
Local Abbreviation oStkF := (@U.Mal_aslot__G2.Mal_aslot_W.oStkF).
Local Abbreviation rmF := (@U.Mal_aslot__G2.Mal_aslot_W.rmF s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation HfrF := (@U.Mal_aslot__G2.Mal_aslot_W.HfrF s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW).
Local Abbreviation touched_dec := (@U.Mal_aslot__G2.Mal_aslot_W.touched_dec s L sc rho 0 gd Hsc m0d bnc0_ok Hgd).
Local Abbreviation rw'_low := (@U.Mal_aslot__G2.Mal_aslot_W.rw'_low sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation agree_vals_rho' := (@U.Mal_aslot__G2.Mal_aslot_W.agree_vals_rho' sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation rwF_low := (@U.Mal_aslot__G2.Mal_aslot_W.rwF_low s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW).
Local Abbreviation pre_reg_cs := (@U.Mal_aslot__G2.Mal_aslot_W.pre_reg_cs sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation reg_sv_ok := (@U.Mal_aslot__G2.Mal_aslot_W.reg_sv_ok sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation freg_sv_ok := (@U.Mal_aslot__G2.Mal_aslot_W.freg_sv_ok sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation negw_sll2_bits := (@U.Mal_aslot__G3.Mal_aslot_T.negw_sll2_bits sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation ze_avT := (@U.Mal_aslot__G3.Mal_aslot_T.ze_avT s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd maskv1_ok Hsp).
Local Abbreviation ze_bncdec := (@U.Mal_aslot__G3.Mal_aslot_T.ze_bncdec s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd).
Local Abbreviation zfact_of := (@U.Mal_aslot__G3.Mal_aslot_T.zfact_of s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation bnc_zero_of := (@U.Mal_aslot__G3.Mal_aslot_T.bnc_zero_of s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW K).
Local Abbreviation bnc_nz_of := (@U.Mal_aslot__G3.Mal_aslot_T.bnc_nz_of s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW K).
Local Abbreviation zf_T171 := (@U.Mal_aslot__G3.Mal_aslot_T.zf_T171 s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd maskv1_ok Hsp).
Local Abbreviation linkT := (@U.Mal_aslot__G3.Mal_aslot_T.linkT s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation smatch_rename := (@U.Mal_aslot__G3.Mal_aslot_T.smatch_rename sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation active_hd_set_hd := (@U.Mal_aslot__G3.Mal_aslot_T.active_hd_set_hd sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation loc_meta := (@U.Mal_aslot__G3.Mal_aslot_T.loc_meta s L sc rho 0 gd Hsc m0d bnc0_ok Hgd).
Local Abbreviation in_meta_locs_range := (@U.Mal_aslot__G3.Mal_aslot_T.in_meta_locs_range s L sc rho 0 gd Hsc m0d bnc0_ok Hgd).
Local Abbreviation size_range := (@U.Mal_aslot__G9.Mal_aslot_L.size_range sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation lor_low5 := (@U.Mal_aslot__G9.Mal_aslot_L.lor_low5 sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation ze_onesw_gen := (@U.Mal_aslot__G9.Mal_aslot_L.ze_onesw_gen s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d).
Local Abbreviation eq0_of := (@U.Mal_aslot__G9.Mal_aslot_L.eq0_of s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW K).
Local Abbreviation span_cnt_ge2 := (@U.Mal_aslot__G9.Mal_aslot_L.span_cnt_ge2 sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation regs_okb_sound := (@U.Mal_aslot__G9.Mal_aslot_L.regs_okb_sound sc rho 0 gd Hsc bnc0_ok Hgd Hsp).
Local Abbreviation rename_link := (@U.Mal_aslot__G9.Mal_aslot_L.rename_link sc rho 0 gd Hsc bnc0_ok Hgd Hsp K).
Local Abbreviation seg_runX := (@U.Mal_aslot__G9.Mal_aslot_L.seg_runX s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd mW Kc RF GF TR RR K HK).
Local Abbreviation ev_addw := (@U.Mal_aslot__G9.Mal_aslot_L.ev_addw s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd Hsp mW).
Local Abbreviation exit_edge := (@U.Mal_aslot__G9.Mal_aslot_L.exit_edge s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc m0d bnc0_ok Hgd spanv0_ok Hsp mW K).
Local Abbreviation HdsF_fixed := (@U.Mal_aslot__G10.Mal_aslot_G.HdsF_fixed s L sc req rho 0 0 0 0 0 0 gd 1 0 m0d mW ms).
Local Abbreviation rwG_low := (@U.Mal_aslot__G10.Mal_aslot_G.rwG_low sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation agree_vals_rhoG := (@U.Mal_aslot__G10.Mal_aslot_G.agree_vals_rhoG sc rho 0 gd Hsc bnc0_ok Hgd).
Local Abbreviation rwF_low_all := (@U.Mal_aslot__G10.Mal_aslot_G.rwF_low_all s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc Hreq m0d bnc0_ok Hgd Hsp mW).
Local Abbreviation rhoG_F := (@U.Mal_aslot__G10.Mal_aslot_G.rhoG_F s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc Hreq m0d bnc0_ok Hgd Hsp mW).
Local Abbreviation obj_G_transfer := (@U.Mal_aslot__G10.Mal_aslot_G.obj_G_transfer s L sc req rho 0 0 0 0 0 0 gd 1 0 Hsc Hreq m0d bnc0_ok Hgd Hsp mW).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Hypothesis HhdN : ltac2:(tb__ "0|0|
S0S31S98A1S74Vs;Vsc;A2S36S98A1A3").
Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.

Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0SbfQ40A1S31SbfQ8A1A1F_;VmW;S59Vrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S116Vvm;S117Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S2cS114A1M0S115VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S115R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S4fSb8Vrho;S188S187A1S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4A4").
Hypothesis Hsc_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PcA2A2Vsc;A3").
Hypothesis Hreq_rho : ltac2:(tb__ "0|0|
S0S3eSc0Q40S49Vrho;PdA2A2Vreq;A3").
Hypothesis Htier : ltac2:(tb__ "0|0|
S84S174Z40Sc0Q40S49Vrho;S1a3A2A2A2S8aS186S8eS189Vsc;A1A1A1A1A2").
Hypothesis Htp : tp_ok C_U rho.
Hypothesis HinitN : ltac2:(tb__ "0|1|
S0S2dSb6Vs;A1S3aA3S1S18cSb8S15aVL;Vrho;A4S0S2cS2fS98S9aA2M0A1Sb7Vs;A1S32G0A1A3A2F_;").

Lemma CactN : ltac2:(tb__ "0|0|
S92S83S7fS77S85S7aS88Z8Vsc;A2A2A1U8S80Z0A1A3S81Vs;A1A3").
Proof using Hgd HhdN Hsc Hsp. try clear Hsp_high. try clear Hdepth.
  unfold image. apply in_app_iff. left. unfold ctx_cells.
  apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc).
  rewrite Z2Nat.id by lia. split; [| apply in_seq; lia].
  unfold active_hd in HhdN. rewrite HhdN. reflexivity.
Qed.

Lemma hold_act0 : ltac2:(tb__ "0|0|
S56Sb8VrhoW;S180Vms;VmW;A2S25S43Z0A1A1A4").
Proof using Erd Ewok HMI Hgd HhdN Hrom Hsc Hsp req. try clear Hsp_high. try clear Hdepth.
  pose proof Hctx as HCX. pose proof Hsc.
  assert (B : bv_unsigned (eval rhoW (SLit 0x5a3c8)) = 0x5a3c8) by (cbn [eval]; apply u64; lia).
  assert (AD : loc_addr L (mc_loc (MCell (LCtx (CTX_active + 8 * sc)) 8 (VZ 0))) = 0x5a3c8 + (8 * sc + 88)).
  { cbn [mc_loc loc_addr]. rewrite HCX. unfold CTX_active. lia. }
  apply (obj_holds_sem segsU rhoW (with_mem ms mW) (carved (SLit 0x5a3c8) (8 * sc + 88) (8 * sc + 96) [(8 * sc + 88, 8%nat, SLit 0)])).
  - reflexivity.
  - cbn [ob_lo carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - cbn [ob_hi carved O_act]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_acthi | lia].
  - reflexivity.
  - cbn [ob_cells carved O_act map]. constructor; [|constructor].
    split; [|split; reflexivity]. cbn [c_off]. rewrite soff_lit_small by lia. apply soff_of_ev; [reflexivity | apply ze_actoff | lia].
  - apply obj_holds_frame_lit; rewrite ?B; try exact Hrom; try lia.
    + cells_inside_tac.
    + intros o Ho. apply (cell_rw0 _ 0 0x5a3c8 (8 * sc + 88) 8 CactN eq_refl eq_refl AD). lia.
    + unfold cells_in_view. constructor; [|constructor]. intros j Hj.
      apply (cell_view0 _ 0 0x5a3c8 (8 * sc + 88) 8 (SLit 0) CactN eq_refl eq_refl ltac:(lia) AD); [|exact Hj].
      cbn [eval]. reflexivity.
Qed.

Definition dsN : list od := ltac2:(tb__ "0|0|
S2bS5S11S2bS5S12S2bS5SdS43Z0A1A1S2bS5S14S2bS5S13S32S5A1A3A3A3A3A3").

Lemma holdN : ltac2:(tb__ "0|0|
ScdS45S56Sb8VrhoW;S180Vms;VmW;A2A3SccS5S45SfS19cA4A3").
Proof using Erd Ewok HMI Hgd Hgd_holds HhdN Hm_ctz Hm_sct Hrom Hsc Hsp req. try clear Hsp_high. try clear Hdepth.
  unfold dsN. cbn [map obj_of]. repeat apply Forall_cons; try apply Forall_nil.
  - apply hold_got. - apply hold_guard. - apply hold_act0. - apply hold_sct. - apply hold_ctz.
Qed.

Lemma rngN_got : ltac2:(tb__ "0|1|
S0S2fS3eS3eA2S5cVrhoW;S27A2S33S3eS3eS85Z28d50M0Z0A2S85G0Z8A2A4A3"). Proof using Hgd Hsc L mW req rho s. apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia]. Qed.
Lemma rngN_guard : ltac2:(tb__ "0|1|
S0S2fS3eS3eA2S5cVrhoW;S28A2S33S3eS3eS85S15cS15aA1M0Z0A2S85G0Z8A2A4A3").
Proof using Hgd Hsc L mW req rho s. drop_sp. apply rng_lit; [lia | lia | rewrite ev1u by reflexivity; rewrite ze173; reflexivity]. Qed.
Lemma rngN_sct : ltac2:(tb__ "0|1|
S0S2fS3eS3eA2S5cVrhoW;S29A2S33S3eS3eS85Z108ecM0Z0A2S85G0Z60A2A4A3"). Proof using Hgd Hsc L mW req rho s. apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia]. Qed.
Lemma rngN_ctz : ltac2:(tb__ "0|1|
S0S2fS3eS3eA2S5cVrhoW;S26A2S33S3eS3eS85Z108ccM0Z0A2S85G0Z20A2A4A3"). Proof using Hgd Hsc L mW req rho s. apply rng_lit; [lia | lia | cbn [eval]; apply u64; lia]. Qed.
Lemma rngN_act : ltac2:(tb__ "0|2|
S0S2fS3eS3eA2S5cVrhoW;S25S43Z0A1A1A2S33S3eS3eS85Z5a3c8M0S85S88Z8Vsc;A2M1Z58A2A2S85G0S85G1Z60A2A2A4A3").
Proof using Hgd Hsc Hsp L mW req s. try clear Hsp_high. try clear Hdepth.
  unfold obj_range, obj_lo_of, obj_hi_of, O_act. cbn [ob_base ob_lo ob_hi]. pose proof Hsc. unfold rhoW.
  replace (bv_unsigned (eval (rho1 mW) (SLit 369608))) with 369608 by (cbn [eval]; rewrite u64; lia).
  rewrite (soff_of_ev e_actoff (8 * sc + 88) eq_refl ze_actoff ltac:(lia)), (soff_of_ev e_acthi (8 * sc + 96) eq_refl ze_acthi ltac:(lia)). reflexivity.
Qed.

Lemma carveN : ltac2:(tb__ "0|1|
S69S3fS0S2cS45A1S4cR2A1S2bS45S19S32S45A1A3A3S5dS5eR3A1S6fR3A1S54R3A1S53R3A1S58R3A1S30S45S4cR3A1SccS5S45SfS19cA4A3S47R3A1R2S6eR3A1A9S69S0S2dS71R1A1S2eA3S4fSb8VrhoW;R5S33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4M0A4S4fSb8VrhoW;R3G0A4F_;F_;TS';F_;Fnx;FS;").
Proof using Erd Ewok HMI Hgd Hgd_holds HhdN Hm_ctz Hm_sct Hrom Hsc Hsp Hsp_high req. try clear Hdepth.
  intros S nx HO S' Hwf Hsm. pose proof Hsc. pose proof Hsp_high as SH.
  assert (GR : 0x5a338 = mc_chk_guard C_U) by reflexivity.
  pose proof holdN as HN. pose proof rngN_got as R1. pose proof rngN_guard as R2. pose proof rngN_act as R3. pose proof rngN_sct as R4. pose proof rngN_ctz as R5.
  unfold rhoW in HN, R1, R2, R3, R4, R5.
  apply smatch_extend_objs.
  - exact Hsm.
  - exact Hwf.
  - change (rm (rho1 mW)) with mW. exact HN.
  - rewrite HO. apply Forall_forall. intros o Ho. constructor; [|constructor]. unfold rhoW.
    rewrite rng_stk. unfold sp0, D0, SymState.ranges_disjoint. top_ranges.
    unfold dsN in Ho. cbn [map obj_of] in Ho. destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [obj_of];
      rewrite ?R1, ?R2, ?R3, ?R4, ?R5, <- ?GR; cbn [fst snd]; lia.
  - unfold dsN. cbn [map obj_of pairwise_disjoint]. unfold SymState.ranges_disjoint. unfold rhoW.
    repeat split; repeat (apply Forall_cons); try apply Forall_nil;
      rewrite ?R1, ?R2, ?R3, ?R4, ?R5, <- ?GR; cbn [fst snd]; try lia; exact I.
Qed.

Lemma SA_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cS127A1S2bS45S19SccS5S45SfS19cA4A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma swf_SA : swf SA_N = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ZF_N : ltac2:(tb__ "0|2|
ScdS44S176S18Vs;VL;Vsc;Vreq;Vrho;Z0M0G0G0G0G0G0Vgd;Z1M1G0S1afAfS17Vs;VL;Vsc;Vreq;Vrho;G0G0G0G0G0G0Vgd;G1G0S1afAfA2S47S127A1A3").
Proof using Hdepth Hgd Hsc Hsp Hsp_high. change (ss_facts SA_N) with F_base5. apply ZF_base5. Qed.

Definition S0N : sstate := ltac2:(tb__ "0|0|
S5dZ2126cSbaSb9S51S36S41A1S2bS45S19S32S45A1A3S47S127A1S122S3aA9").
Lemma carve_N : ltac2:(tb__ "0|1|
S4fSb8VrhoW;S19dS33S2cS114A1S154Vtr;S155Vms;Vmd;A2A4M0A4S4fSb8VrhoW;S127G0A4F_;").
Proof using Erd Ewok HMI Hgd Hgd_holds HhdN Hm_ctz Hm_sct Hrom Hsc Hsp Hsp_high req. try clear Hdepth.
  intros Hsm. change SA_N with (mkSS (ss_pc S0N) (ss_regs S0N) (ss_fregs S0N) (ss_fcsr S0N) (ss_resv S0N) (ss_objs S0N ++ map obj_of dsN) (ss_facts S0N) NXA (ss_lenient S0N)).
  apply (carveN S0N NXA eq_refl swf_SA Hsm).
Qed.

Definition LN : sstate := lfs LA_N 0 SA_N.
Lemma LN_objs : ltac2:(tb__ "0|0|
S0S2cS45A1S4cS19bA1S2bS45S162S18fA1S2bS45S27S2bS45S28S2bS45S25S43Z0A1A1S2bS45S29S2bS45S26S32S45A1A3A3A3A3A3A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma LN_pc : ss_pc LN = 0x2144c. Proof using . reflexivity. Qed.
Lemma LN_regs : regsG_okb LN = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LN_fregs : ltac2:(tb__ "0|0|
S0S2cS41A1S54S19bA1Sb9A3"). Proof using . reflexivity. Qed.
Lemma LN_fcsr : ltac2:(tb__ "0|0|
S0S57S53S19bA1S51A3"). Proof using . reflexivity. Qed.
Lemma LN_resv : ss_resv LN = None. Proof using . reflexivity. Qed.

Section PostN.
Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agrees rhoW rhoF.
Hypothesis HsmF : ltac2:(tb__ "0|0|
S4fSb8VrhoF;S19bS33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A4").
Hypothesis HKc' : Kc tr md.

Definition rwN (j : positive) : word := ltac2:(tb__ "0|3|
S2dSbfQ40A1L_;M0S8dS40Vj;A1M1Z64A2S49Vrho;Vj;A2G0S3bS91Zc8M2G1A2S8dG1Ze8A2A2S60VrhoF;S4bS19bS87G1G2A2A2A2S49VrhoF;Vj;A2X2dx2X2dx2").
Definition rhoN : valuation := ltac2:(tb__ "0|0|
S66S1acS68Vrho;A1S59Vrho;A1A3").

Lemma rwN_low j : ltac2:(tb__ "0|0|
S1a0Vj;P64A2S0SbfQ40A1S1acVj;A1S49Vrho;Vj;A2A3F_;").
Proof using Hgd Hsc. drop_sp. intros Hj. unfold rwN. replace (Z.pos j <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma agree_vals_rhoN : ltac2:(tb__ "0|0|
S153SbdVrho;S1abA3").
Proof using Hgd Hsc. drop_sp. split; [|reflexivity]. intros j Hj. cbn [rw rhoN]. symmetry. apply rwN_low. exact Hj. Qed.

Lemma rwF_lowN j : ltac2:(tb__ "0|0|
S1a0Vj;P64A2S0SbfQ40A1S49VrhoF;Vj;A2S49Vrho;Vj;A2A3F_;").
Proof using HagF Hgd Hreq Hreq_rho Hsc Hsc_rho Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hj. rewrite (rw_agrees rhoF j HagF) by (unfold below200; apply Pos.ltb_lt; lia).
  destruct (Pos.eq_dec j 12) as [->|N12].
  { rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 12%positive)), Hsc_rho. apply bv_eq. change (bv_unsigned (rw1 12%positive)) with (zr1 12%positive). rewrite zr1_12, u64 by (pose proof Hsc; lia). reflexivity. }
  destruct (Pos.eq_dec j 13) as [->|N13].
  { rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 13%positive)), Hreq_rho. apply bv_eq. change (bv_unsigned (rw1 13%positive)) with (zr1 13%positive).
    pose proof (MallocWfArith.class_size_bounds sc ltac:(pose proof Hsc; lia)). pose proof Hreq. unfold IB in *. rewrite zr1_13, u64 by lia. reflexivity. }
  apply rw1_low; assumption.
Qed.

Lemma rhoN_F u : ltac2:(tb__ "0|0|
S0S2dS18eVu;A1S2eA3S0SbfQ40A1S49VrhoF;Vu;A2S49S1abVu;A2A3F_;").
Proof using HagF Hgd Hreq Hreq_rho Hsc Hsc_rho Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hu. unfold fG in Hu. cbn [rw rhoN]. unfold rwN.
  destruct (Z.pos u <? 100) eqn:E.
  - apply Z.ltb_lt in E. apply rwF_lowN. lia.
  - apply Bool.orb_prop in Hu as [Hu|Hu]; [apply Bool.orb_prop in Hu as [Hu|Hu]|].
    + apply Pos.ltb_lt in Hu. apply Z.ltb_ge in E. lia.
    + apply Pos.eqb_eq in Hu. subst u. reflexivity.
    + apply Pos.eqb_eq in Hu. subst u. reflexivity.
Qed.

Theorem smatch_N : ltac2:(tb__ "0|0|
S4fSb8S1abS190S33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A4").
Proof using EmW Erd Evm Ewok HMI HagF Hdepth Hgd Hgd_holds HhdN Hm_ctz Hm_sct Hreq Hreq_rho Hsc Hsc_rho HsmF Hsm_pre Hsp Htier. try clear Hsp_high.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, LN_pc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  { intros r Hr0. rewrite (Hr r Hr0).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    assert (Hin : In (bv_unsigned r) (map Z.of_nat (seq 1 31))) by (apply in_map_iff; exists (Z.to_nat (bv_unsigned r)); split; [lia|]; apply in_seq; lia).
    pose proof (proj1 (forallb_forall _ _) LN_regs _ Hin) as P1. pose proof (proj1 (forallb_forall _ _) SG_regs_vars _ Hin) as P2. cbn beta in P1, P2.
    destruct (existsb (Z.eqb (bv_unsigned r)) [10; 11; 12]) eqn:E3.
    - cbn [existsb orb] in E3.
      assert (E : reg_sv SG (bv_unsigned r) = SVar (Z.to_pos (200 + bv_unsigned r)) /\ 10 <= bv_unsigned r <= 12).
      { destruct (Z.eqb_spec (bv_unsigned r) 10) as [->|]; [split; [reflexivity|lia]|].
        destruct (Z.eqb_spec (bv_unsigned r) 11) as [->|]; [split; [reflexivity|lia]|].
        destruct (Z.eqb_spec (bv_unsigned r) 12) as [->|]; [split; [reflexivity|lia]|]. cbn in E3. discriminate. }
      destruct E as [-> Rr]. cbn [eval rhoN rw]. unfold rwN.
      replace (Z.pos (Z.to_pos (200 + bv_unsigned r)) <? 100) with false by (symmetry; apply Z.ltb_ge; lia).
      replace ((200 <=? Z.pos (Z.to_pos (200 + bv_unsigned r))) && (Z.pos (Z.to_pos (200 + bv_unsigned r)) <? 232))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      replace (Z.pos (Z.to_pos (200 + bv_unsigned r)) - 200) with (bv_unsigned r) by lia. reflexivity.
    - cbn [orb] in P1, P2. apply sv_eqb_sound in P1. rewrite P1. apply andb_prop in P2 as [P2 P3].
      apply (eval_agree_vars_nl fG rhoF rhoN); [apply rhoN_F | exact P2 | exact P3]. }
  split.
  { intros r. rewrite (Hf r). unfold freg_sv. rewrite LN_fregs. change (ss_fregs SG) with pre_fregs.
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    destruct (freg_sv_ok (bv_unsigned r) ltac:(lia)) as (vv & _ & E2 & Hvv). rewrite E2.
    cbn [eval rhoN rw]. rewrite rwN_low by lia. apply rwF_lowN. lia. }
  split. { rewrite LN_fcsr in Hc. exact Hc. }
  split. { unfold resv_match in *. rewrite LN_resv in Hv. cbn [ss_resv SG]. exact Hv. }
  split.
  { destruct Hm as (Hall & Hpd & Hfrm). rewrite LN_objs in Hall, Hpd, Hfrm.
    assert (TRF : forall o, In o [oStkG; oGot; oGuard; oAct0] -> obj_holds segsU rhoF msF o -> obj_holds segsU rhoN msF o).
    { intros o Ho HO. eapply (obj_holds_agree_vars_nl segsU fG rhoF rhoN); [apply rhoN_F | | | exact HO]; destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. }
    split; [|split].
    - constructor. { apply TRF; [cbn; tauto|]. apply (proj1 (Forall_forall _ _) Hall). left. reflexivity. }
      constructor. { apply TRF; [cbn; tauto|]. apply (proj1 (Forall_forall _ _) Hall). right. left. reflexivity. }
      constructor. { apply TRF; [cbn; tauto|]. apply (proj1 (Forall_forall _ _) Hall). right. right. left. reflexivity. }
      constructor. { apply TRF; [cbn; tauto|]. apply (proj1 (Forall_forall _ _) Hall). right. right. right. left. reflexivity. }
      constructor.
    - assert (RG : forall o, In o [oStkG; oGot; oGuard; oAct0] -> obj_range rhoN o = obj_range rhoF o).
      { intros o Ho. apply (obj_range_agree_vars_nl fG rhoF rhoN); [apply rhoN_F | |]; destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. }
      apply pairwise_disjoint_pdr. erewrite map_ext_in by exact RG.
      apply pairwise_disjoint_pdr in Hpd. cbn [map] in Hpd.
      change [oStkG; oGot; oGuard; oAct0] with [oStkF stkcG; O_got; O_guard; O_act (SLit 0)]. cbn [map]. exact (pdr_prefix4 _ _ _ _ _ Hpd).
    - intros a Ha. cbn [rm rhoN]. rewrite <- EmW.
      destruct (in_ranges_dec rhoF [O_sct; O_ctz] a) as [IN|OUT].
      +
        destruct IN as (o & Ho & Ra). pose proof Hsc.
        assert (RGF : forall o', In o' [O_sct; O_ctz] -> obj_range rhoF o' = obj_range rhoW o').
        { intros o' Ho'. apply (obj_range_agree_vars below200 rhoW rhoF); [intros u Hu; symmetry; exact (proj1 HagF u Hu) | intros l; symmetry; exact (proj1 (proj2 HagF) l) |].
          destruct Ho' as [<-|[<-|[]]]; vm_compute; reflexivity. }
        rewrite (RGF o Ho) in Ra. pose proof (urange_n 64 a) as UA. change (2 ^ Z.of_N 64) with (2 ^ 64) in UA.
        pose proof rngN_sct as R4. pose proof rngN_ctz as R5. unfold rhoW in Ra, R4, R5.
        destruct Ho as [<-|[<-|[]]].
        * rewrite R4 in Ra. cbn [fst snd] in Ra.
          rewrite <- (Z_to_bv_bv_unsigned 64 a). replace (bv_unsigned a) with (67820 + (bv_unsigned a - 67820)) by lia.
          rewrite Hm_sct by lia. apply HroX. replace (67820 + (bv_unsigned a - 67820)) with (67788 + (bv_unsigned a - 67788)) by lia. apply ro_tables_P. lia.
        * rewrite R5 in Ra. cbn [fst snd] in Ra.
          rewrite <- (Z_to_bv_bv_unsigned 64 a). replace (bv_unsigned a) with (67788 + (bv_unsigned a - 67788)) by lia.
          rewrite Hm_ctz by lia. apply HroX. apply ro_tables_P. lia.
      + etransitivity; [apply Hfrm | rewrite (proj2 (proj2 HagF)); reflexivity].
        apply Forall_cons_iff in Ha as [HaS Ha]. apply Forall_cons_iff in Ha as [HaG Ha]. apply Forall_cons_iff in Ha as [HaD Ha]. apply Forall_cons_iff in Ha as [HaA _].
        assert (RG' : forall o, In o [oStkG; oGot; oGuard; oAct0] -> obj_range rhoN o = obj_range rhoF o).
        { intros o Ho. apply (obj_range_agree_vars_nl fG rhoF rhoN); [apply rhoN_F | |]; destruct Ho as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity. }
        cbn zeta in HaS, HaG, HaD, HaA.
        rewrite (RG' oStkG ltac:(cbn; tauto)) in HaS. rewrite (RG' oGot ltac:(cbn; tauto)) in HaG. rewrite (RG' oGuard ltac:(cbn; tauto)) in HaD. rewrite (RG' oAct0 ltac:(cbn; tauto)) in HaA.
        change (oStkF stkcG) with oStkG. change O_got with oGot. change O_guard with oGuard. change (O_act (SLit 0)) with oAct0.
        constructor; [exact HaS|]. constructor; [exact HaG|]. constructor; [exact HaD|]. constructor; [exact HaA|].
        apply Forall_forall. intros o Ho. cbn zeta. intros R. apply OUT. exists o. split; [exact Ho | exact R]. }

  unfold SG. cbn [ss_facts]. unfold factsG.
  assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rhoN f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rhoN f agree_vals_rhoN Hb) Hh). }
  pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts Pre_as] in HF0.
  apply Forall_app. split.
  - apply Forall_forall. intros f Hf0. apply AGR; [|exact (proj1 (Forall_forall _ _) HF0 f Hf0)].
    cbn in Hf0. decompose [or] Hf0; subst; try reflexivity; contradiction.
  - constructor; [|constructor]. cbn [SymState.holds eval rhoN rw]. rewrite rwN_low by lia. rewrite (u64 47) by lia. pose proof Hsc. lia.
Qed.

Theorem post_N : ltac2:(tb__ "0|0|
S191VX;VU;S156Vs;VL;A2VKc;Vrho;S33S2cS114A1S154Vtr;S155VmsF;Vmd;A2A4A6").
Proof using EmW Erd Evm Ewok HKc' HMI HXr HagF Hdepth Hgd Hgd_holds HhdN HinitN Hm_ctz Hm_sct Hreq Hreq_rho Hsc Hsc_rho HsmF Hsm_pre Hsp Hsp_high Htier Htp.
  unfold GX. cbn [ma_s ma_L]. rewrite Hsc_rho.
  exists (mkMA s L), rhoN. cbn [ma_s ma_L].
  split; [exact agree_vals_rhoN|]. split; [reflexivity|]. split; [intros; reflexivity|]. split; [apply ub_same_refl|].
  split; [intros a _ _ _ _ _; reflexivity|].
  split; [exact HhdN|].
  split. { cbn [rw rhoN]. unfold rwN. cbn. rewrite (rw_agrees rhoF 173%positive HagF eq_refl). apply bv_eq. change (bv_unsigned (rw1 173%positive)) with (zr1 173%positive). rewrite zr1_173, u64; [reflexivity|]. cbn. lia. }
  split. { unfold try_avail. rewrite (TryAvailPost.bind_eq _ _ s _ s (TryAvailPost.get_head_eq s sc)), HhdN. reflexivity. }
  split; [reflexivity|].
  split. { cbn [rw rhoN]. unfold rwN. cbn. rewrite (rw_agrees rhoF 174%positive HagF eq_refl). change (bv_unsigned (rw1 174%positive)) with (zr1 174%positive). rewrite zr1_174.
           rewrite <- EmW. pose proof Hgd_holds as HG. rewrite Erd in HG. exact HG. }
  split; [exact smatch_N|].
  unfold J_as_pre. cbn [w_tr w_cfg cfg_model fst snd ma_s].
  split. { unfold MInvIR. cbn [rm rhoN]. rewrite <- EmW, <- Evm. pose proof HMI as H. rewrite Erd, Ewok in H. exact H. }
  split; [exact HXr|]. split; [exact HKc'|].
  cbn [rw rhoN]. rewrite !rwN_low by (unfold V_DEPTH; lia). rewrite Hsc_rho, Hreq_rho. pose proof Hsc. pose proof Hreq.
  split; [repeat split; try lia; try exact Htier|].
  split. { unfold tp_ok. cbn [rw rhoN]. rewrite rwN_low by lia. exact Htp. }

  split. { intros Hinit. destruct (HinitN Hinit) as [HA HM]. split; [|exact HM].
  apply (auxv_init_mono segsU C_U L rho rhoN); [reflexivity | | exact HA].
  cbn [rw rhoN]. rewrite rwN_low by lia. lia. }

  unfold top_high, V_DEPTH. cbn [ma_L rw rhoN]. rewrite !rwN_low by lia. exact Hsp_high.
Qed.
End PostN.

Theorem variant_N : ltac2:(tb__ "0|0|
VTR;Z0S181Sb8VK;S127VrhoW;A4S191VX;VU;S156Vs;VL;A2VKc;Vrho;A5A3").
Proof using EmW Erd Evm Ewok HK HKc HMI HXr Hdepth Hgd Hgd_holds HhdN HinitN Hm_ctz Hm_sct Hreq Hreq_rho Hsc Hsc_rho Hsm_pre Hsp Hsp_high Htier Htp RR.
  apply (seg_run 300 SA_N LA_N _ rhoW eq_refl eq_refl runA_N (agrees_refl rhoW)).
  intros Lf rhoF [tr' [msF md']] Hin HagF [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  rewrite (single_leaf LA_N _ SA_N Lf LA_N_shape Hin) in HsmF. change (lfs LA_N 0 SA_N) with LN in HsmF.
  exact (post_N msF rhoF HagF HsmF HKc').
Qed.
End N.
End Mal_aslot_VN.
