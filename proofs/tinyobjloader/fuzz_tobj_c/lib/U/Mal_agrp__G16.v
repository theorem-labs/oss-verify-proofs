(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "list"; "pair"; "true"; "nil"; "bool"; "option"; "prod"; "None"; "Some"; "false"; "app"; "nat"; "length"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sobj"; "rw"; "SLit"; "rm"; "smatch"; "cell"; "mkCell"; "sprop"; "ss_next"; "rl"; "ss_objs"; "mkSS"; "ss_facts"; "ss_lenient"; "valuation"; "mkObj"; "obj_holds"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "DUnknown"; "SAlu"; "SPBranch"; "SPUle"; "sstate"; "eval"; "obj_range"; "reg_sv"; "DRom"; "FcsrFrm0"; "SPAlign"; "agree_below"; "holds"; "mkVal"; "sv_eqb"; "swf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "kreq"; "IB"; "alloc_slot"; "ameta"; "class_size"; "region"; "st_init_done"; "st_regions"; "PGSZ"; "UNIT"; "alloc_meta"; "am_last"; "am_sc"; "stride_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "opp"; "sub"; "modulo"; "div"; "mul"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "holds"; "mc_chk_guard"; "mc_errno"; "topL"; "addr_of"; "ctz_tab_bytes"; "mc_tp"; "med_cnt_tab_bytes"; "small_cnt_tab_bytes"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC.NC.World"; "rhoB"; "m1"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "Pre_as"; "MInvIR"; "L_as_fail"; "AS_D"; "L_as_ok"; "JL_as_fail"; "JL_as_ok"; "tier"; "J_as_pre"; "canary_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "ij"; "itotal"; "ia_rho"; "obj_of2"; "ia_L"; "ia_U"; "ia_X"; "ia_m"; "ia_mW"; "ia_s"; "icnt0"; "live"; "rho2"; "rl2"; "rw2"; "D_act0"; "D_got"; "D_guard"; "D_m"; "D_med"; "D_pgs"; "D_s2c"; "D_sct"; "D_small"; "D_usg"; "ia_gd"; "ia_sc"; "instA_ok"; "isize"; "mkInstA"; "od2_entry"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs"; "SokA"; "SnullA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC.NC.World.Call"; "rho1"; "inFrm"; "oFrm"; "rhoP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "RsSymJump"; "mkLeaf"; "list_set"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs"; "RcN"; "sN"; "EvN"; "SNfail"; "SNok"; "SNr0"; "SNS"; "SNr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "ma_L"; "MA"; "mkMA"; "layout_extends"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_N0"; "LN0"; "SnullG"; "CUTS_N0"; "sN0"; "LN0r"; "RN0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B"; "SokA1"; "SokA0"; "SokA2"; "dsC"; "mkia"; "stkA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "O_got"; "O_guard"; "O_sct"; "SN2pre"; "O_m"; "SCsym"; "STKC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "dsCs"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "rho_sub"; "rho_absorb"; "wsub_id_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "mem_kept"; "rd_of"; "wok_of"; "stack_win"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC.NC.World.Call.Out"; "rhoP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_rNF"; "CN0"; "CNR"; "XN0"; "XNR"; "RN0"; "RNR"; "mkCN0"; "mkCNR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "import_okP"; "J_ofP"; "import_post"; "LQP"; "obj_vars_all"; "state_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "active_hd"; "yields"; "Inv"; "layout"; "keys"; "le_byte"; "memb"; "usedX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "in_vars"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B.B.E"; "rhoK1"; "SEM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "w_tr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "am_post_common"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A"; "contA_null"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC.NC"; "JN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC"; "contN_fail"; "contN_frame"; "contN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "NREL2"; "SFr"; "dcond2"; "m'"; "oStkF"; "od2_semb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "rhoW";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF"; "addO"; "F_R"; "O_fh0"; "O_fhR"; "O_fmp"; "O_hpn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "patchf"; "rho_patch"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK"; "Posts_asG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "objs_matchb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B.B"; "mkia"; "mkia_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_N0.N0.W.Exit"; "rhoF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_B.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SokA0 : sstate := ltac2:(tb__ "0|0|
S22S2aS9dA1Sa7S15S2bS9dA1U0S16P14A1A4S29S9dA1S28S9dA1S2cS9dA1S21S9dA1S23S9dA1S1fS9dA1SaA9").
Lemma SokA0_swf : swf SokA0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SokA0_regs : ltac2:(tb__ "0|0|
S3fS10S53Z0R1A2S53R1Z20A2A2SfS5S3bS34SbcR2A2S34S9dR2A2A2S3A3F_;Fz;").
Proof. intros z Hz. exact (forall_range_dec (fun z => sv_eqb (reg_sv SokA0 z) (reg_sv SokA z)) 1 31 ltac:(vm_compute; reflexivity) z ltac:(lia)). Qed.

Lemma smatch_SokA0 rho w : ltac2:(tb__ "0|0|
S1bS3dVrho;S9dVw;A4S1bS3dVrho;SbcVw;A4F_;").
Proof.
  destruct w as [tr [ms md]]. intros Hsm.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact SokA0_swf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [|exact (conj Hfregs (conj Hfcsr (conj Hresv (conj Hmem Hfacts))))].
  intros r Hr. unfold regs_match in Hregs. cbn [fst snd cfg_ms]. rewrite (Hregs r Hr). pose proof (urange_n 5 r) as R. change (2 ^ Z.of_N 5) with 32 in R.
  pose proof (SokA0_regs (bv_unsigned r) ltac:(lia)) as E. apply sv_eqb_sound in E. rewrite E. reflexivity.
Qed.

Definition stkA : sobj := nth 0 (ss_objs SokA) O_stk.
Definition SokA1 : sstate := ltac2:(tb__ "0|0|
S22S2aS9dA1Sa7S15S2bSbcA1UaS108PbeA1A4S29S9dA1S28S9dA1S2cS9dA1S0S17Sc0S0S17Sc8S0S17Sc6S4S17A1A3A3A3S23S9dA1S1fS9dA1SaA9").
Lemma SokA1_swf : swf SokA1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_SokA1 : ltac2:(tb__ "0|5|
SfS6S7S1S7S15S15A2M0A1M1S1S1eA1M2A2M3A1SeeSbcSbbA2S9G3S2G1G2S0G0S2S15S15S16P136A1S108PbeA1A4M4S0G0G4S4G0A1A3A3S4S1eA1A4A2A3").
Proof. match goal with |- ?l = _ => vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) l) end. Qed.

Definition dsC0 : list od2 := ltac2:(tb__ "0|1|
S0S7aS8dS19Z0A1M0G0G0G0G0G0A6S0S7aS91S4S7aA1A3A3").
Definition dsC : list od2 := ltac2:(tb__ "0|0|
S0S7aS8bS0S7aS8cS0S7aS8aS19Z0A1A1S0S7aS8fS0S7aS93S108Pc0A1A1S0S7aS92S0S7aS8eS0S7aS90S4S7aA1A3A3A3A3A3A3A3A3").
Definition SokA2 (ia : instA) : sstate := ltac2:(tb__ "0|0|
S22S2aSbbA1S2bSbbA1S29SbbA1S28SbbA1S2cSbbA1SbS17S21SbbA1SccS7aS17S7eSbeA4A3S23SbbA1P154S24SbbA1A9").
Section B.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 rhoK : valuation).
Variables (tr : list event) (ms : machine_state) (md : Model).
Variables (A1 : MA) (m : sptr).
Let sc : Z := bv_unsigned (rw rho0 12%positive).
Let req : Z := bv_unsigned (rw rho0 13%positive).
Let gd : Z := bv_unsigned (rw rho0 174%positive).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S1bS3dVrhoK;S9dS2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Hypothesis HF : contA_frame rho0 rhoK.
Hypothesis HKc : Kc tr md.
Hypothesis HP : contA_pure rho0.

Hypothesis Htop0 : top_high A rho0.
Hypothesis Em : ltac2:(tb__ "0|0|
SfS3fS61Sb1VA1;A1Vm;A2S68Q40S18VrhoK;P136A2A2A3").
Hypothesis HMI : ltac2:(tb__ "0|0|
S71S3dS5bS0S41Vm;VX;A3S8S7S41S3fA2A1VU;VA1;VrhoK;Vmd;A8").
Hypothesis HC : ltac2:(tb__ "0|0|
S10dVX;S0S41Vm;VX;A3VA;VA1;A4").
Hypothesis Hmemb : ltac2:(tb__ "0|0|
SfS5S101Vm;VX;A2SaA3").
Hypothesis Hkey : ltac2:(tb__ "0|0|
Se4S41Vm;SffSb0VA1;A1A1A3").
Hypothesis Hhd : ltac2:(tb__ "0|0|
SfS6S41A1SfbSb0VA1;A1Vsc;A2S8S41A1A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S3fSfS3fVU;R1A1Z0A3Fc;").

Let mW : word -> option byte := rm rhoK.
Let rd0 : word -> option byte := Glue.rd_of segsU mW.

Lemma errno_readable : ltac2:(tb__ "0|0|
S11S3fS3fS5dS5cVrd0;S66Q40A1S3L_;A2S5fS5bA1U4R1A4Lerv;A2").
Proof using gd mW req sc.
  apply holds_of_readable. intros k Hk. assert (EE : mc_errno C_U = 0x3a02c) by reflexivity. rewrite EE. unfold byteview_of.
  replace ((0 <=? 0x3a02c + Z.of_nat k) && (0x3a02c + Z.of_nat k <? 2 ^ 64) && true)%bool with true
    by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  assert (IMG : exists b, image_byte segsU (Z_to_bv 64 (0x3a02c + Z.of_nat k)) = Some b).
  { pose proof (forall_range_dec (fun k => match image_byte segsU (Z_to_bv 64 (0x3a02c + k)) with Some _ => true | None => false end) 0 4
                  ltac:(vm_compute; reflexivity) (Z.of_nat k) ltac:(lia)) as Hb. cbn beta in Hb.
    destruct (image_byte segsU (Z_to_bv 64 (0x3a02c + Z.of_nat k))) as [b|]; [exists b; reflexivity | discriminate]. }
  destruct IMG as [b Hb]. unfold rd0, Glue.rd_of. destruct (mW (Z_to_bv 64 (0x3a02c + Z.of_nat k))) as [b'|].
  - exists (bv_unsigned b'). split; [reflexivity|]. pose proof (urange_n 8 b'). change (2 ^ Z.of_N 8) with 256 in H. lia.
  - rewrite Hb. exists (bv_unsigned b). split; [reflexivity|]. pose proof (urange_n 8 b). change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Definition mkia (erv : Z) : instA := ltac2:(tb__ "0|0|
S98Sb0VA1;A1Sb1VA1;A1VX;S8S7S41S3fA2A1VU;Vsc;Vreq;VrhoK;Vm;Vgd;Verv;S6dVmd;A1VmW;Z0Ae").

Let u10 : Z := bv_unsigned (rw rhoK 10%positive).
Let u15 : Z := bv_unsigned (rw rhoK 15%positive).
Lemma B_facts : ltac2:(tb__ "0|0|
ScdS1eS39VrhoK;A1S23S9dA1A3"). Proof using Hsm. exact (smatch_facts_hold segsU _ _ _ Hsm). Qed.
Lemma B_win : ltac2:(tb__ "0|5|
S10S51Sc3Z40M0Vu15;A2M1S55S73A1A2S10S51S55S54Z2M2Z28A2A1G1A2S10S51Z0M3S52Vu10;G1A2M4A2S10S51Z7fff7f800000G4A2S10SfS3fS57Vu10;Z10A2G3A3S53Vu10;S54G2G0A2A2A2A2A2A2A2").
Proof using Hsm gd req sc.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hf). cbn [fst snd cfg_ms ss_objs ss_facts] in Hall, Hf.
  assert (F3 : Forall (SymState.holds rhoK) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)).
  { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hf).
    cbn in Hp. cbn. decompose [or] Hp; subst; tauto. }
  pose proof (window_facts segsU rhoK ms AS_D stkA ltac:(unfold AS_D; lia) F3 eq_refl eq_refl (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & _).
  unfold u10, u15. repeat split; assumption.
Qed.
Lemma B_4096 : 4096 <= u10.
Proof using Hsm gd req sc u15.
  pose proof (proj1 (Forall_forall _ _) B_facts (SPUle (SLit 4096) (SVar 10)) ltac:(cbn; tauto)) as H.
  cbn [SymState.holds eval] in H. rewrite u64 in H by lia. exact H.
Qed.

Lemma rw0 j : ltac2:(tb__ "0|0|
Se6Vj;P12cA2SfS66Q40A1S18VrhoK;Vj;A2S18Vrho0;Vj;A2A3F_;"). Proof using HF. exact (proj1 HF j). Qed.

Lemma mkia_ok erv : ltac2:(tb__ "0|0|
S10S51Z0Verv;A2S53Verv;S54Z2Z20A2A2A2S5dS5cVrd0;S66Q40A1S3L_;A2S5fS5bA1U4Verv;A4S96S12dVerv;A1A1F_;F_;").
Proof using HC HF HMI HP HU Hhd Hkey Hsm Htop0.
  intros Herv Hervh. pose proof HP as (P1 & P2 & P3 & P4 & P5 & P6). cbn zeta in P1, P2, P3, P4.
  pose proof B_win as (W1 & W2 & W3 & W4 & W5 & W6). pose proof B_4096 as W7.
  pose proof HF as (F1 & F2 & F3 & F4 & F5 & F6).
  constructor; cbn [ia_s ia_L ia_X ia_R ia_U ia_sc ia_req ia_rho ia_m ia_gd ia_erv ia_vm ia_mW mkia].
  - exact (mig_I HMI).
  - exact (proj1 HC).
  - exact P1.
  - split; [exact P2 | exact P3].
  - exact Hhd.
  - exact Hkey.
  - exact (proj1 HC m ltac:(left; reflexivity)).
  - exact HMI.
  - apply urange.
  - exact Herv.
  - split; [exact W7 | exact W5].
  - split; [| exact W2]. unfold u15. rewrite (rw0 15) by (cbv; reflexivity). exact P4.
  -
    rewrite (rw0 10), (rw0 15) by (cbv; reflexivity).
    rewrite (layout_extends_top _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HC)))))))). exact Htop0.
  - unfold tp_ok in P5. rewrite (rw0 24) by (cbv; reflexivity). exact P5.
  - exact F4.
  - intros k Hk. unfold byteview_of.
    replace ((0 <=? mc_chk_guard C_U + Z.of_nat k) && (mc_chk_guard C_U + Z.of_nat k <? 2 ^ 64) && true)%bool with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; cbn; lia).
    pose proof (F6 k Hk) as E. rewrite rd_of_CG in E. unfold rd0, mW. rewrite E. cbn [option_map]. f_equal.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
  - exact Hervh.
  - exact HU.
Qed.

Section E.
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
S5dS5cVrd0;S66Q40A1S3L_;A2S5fS5bA1U4Verv;A4").
Let ia : instA := mkia erv.
Let Hi : instA_ok ia := ltac2:(tb__ "0|0|
S12eVerv;VHerv;VHervh;A3").
Let rhoW : valuation := rho2 ia mW.

Definition rhoK1 : valuation := ltac2:(tb__ "0|3|
SeaSeaSeaVrhoK;P2SccS3fS66Q8M0A1M1S67G0A1M2S65A4A3P3SccS3fG1G2S64A4A3P4SccS3fG1G2S62A4A3").
Lemma smatch_K1 : ltac2:(tb__ "0|0|
S1bS3dS106SbcS2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using Hsm.
  unfold rhoK1. apply SymCall.smatch_set_rl; [vm_cast_no_check (@eq_refl bool false)|].
  apply SymCall.smatch_set_rl; [vm_cast_no_check (@eq_refl bool false)|].
  apply SymCall.smatch_set_rl; [vm_cast_no_check (@eq_refl bool false)|].
  apply smatch_SokA0. exact Hsm.
Qed.

Definition SEM : list positive := ltac2:(tb__ "0|0|
S0S40Pa8S0S40Pa9S0S40Pa4S0S40Pa5S0S40Pa6S0S40Pa7S0S40PacS0S40PafS0S40Pb0S0S40Pb1S0S40Pb6S0S40PbeS0S40PbfS0S40Pc0S0S40Pc1S0S40Pc2S0S40Pc3S0S40Pc4S0S40Pc5S0S40Pc6S0S40Pc7S0S40Pa3S0S40Pa2S0S40Pa1S0S40PbbS4S40A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma SokA0_vars : ltac2:(tb__ "0|0|
SfS5Sf7S40SeS105S107R1A2A1Lu;SbcA2S3A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma rwW_agree v : ltac2:(tb__ "0|0|
SfS5SeS105S107Vv;A2A1S3A3SfS66Q40A1S18S106Vv;A2S18VrhoW;Vv;A2A3F_;").
Proof using HC HF HMI HP HU Herv Hervh Hhd Hkey Hsm ia.
  intros Hv. pose proof HP as (_ & _ & _ & _ & _ & P6).
  change (rw rhoK1 v) with (rw rhoK v). change (rw rhoW v) with (rw2 ia v). unfold rw2, rw2v.
  cbn [ia_sc ia_req ia_gd ia_erv ia_rho ia_m ia_L ia mkia].
  assert (NI : forall x, In x SEM -> (Z.pos v =? Z.pos x) = false).
  { intros x Hx. apply Z.eqb_neq. intros E. apply Pos2Z.inj in E. subst v. unfold in_vars in Hv. apply Bool.negb_true_iff in Hv.
    assert (C : existsb (Pos.eqb x) SEM = true) by (apply existsb_exists; exists x; split; [exact Hx | apply Pos.eqb_refl]).
    rewrite C in Hv. discriminate Hv. }
  destruct (Z.eqb_spec (Z.pos v) 12) as [E12|N12].
  { assert (v = 12%positive) by lia. subst v. unfold sc. rewrite Z_to_bv_bv_unsigned. apply rw0. reflexivity. }
  destruct (Z.eqb_spec (Z.pos v) 13) as [E13|N13].
  { assert (v = 13%positive) by lia. subst v. unfold req. rewrite Z_to_bv_bv_unsigned. apply rw0. reflexivity. }
  rewrite !NI by (cbn; tauto).
  destruct (Z.eqb_spec (Z.pos v) 173) as [E173|N173].
  { assert (v = 173%positive) by lia. subst v. rewrite (rw0 173) by reflexivity. exact P6. }
  destruct (Z.eqb_spec (Z.pos v) 174) as [E174|N174].
  { assert (v = 174%positive) by lia. subst v. unfold gd. rewrite Z_to_bv_bv_unsigned. apply rw0. reflexivity. }
  rewrite !NI by (cbn; tauto). reflexivity.
Qed.

Lemma rlW_agree l : ltac2:(tb__ "0|0|
SfS1S66Q8A1A1S20S106Vl;A2S20VrhoW;Vl;A2A3").
Proof using HF ia.
  pose proof HF as (_ & F2 & F3 & _).
  change (rl rhoW l) with (rl2 ia l). unfold rl2, rhoK1, rho_set_rl. cbn [rl ia_rho ia mkia].
  destruct (Pos.eqb_spec l 1) as [->|N1]; [cbn; exact F2|].
  destruct (Pos.eqb_spec l 4) as [->|N4]; [reflexivity|].
  destruct (Pos.eqb_spec l 3) as [->|N3]; [reflexivity|].
  destruct (Pos.eqb_spec l 2) as [->|N2]; [reflexivity|].
  reflexivity.
Qed.

Lemma smatch_W0 : ltac2:(tb__ "0|0|
S1bS3dVrhoW;SbcS2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using HC HF HMI HP HU Herv Hervh Hhd Hkey Hsm ia u10 u15.
  apply (smatch_agree_vars segsU (fun u => negb (in_vars SEM u)) rhoK1 rhoW SokA0 _ rwW_agree rlW_agree eq_refl SokA0_vars smatch_K1).
Qed.

Lemma smatch_W1 : ltac2:(tb__ "0|0|
S1bS3dVrhoW;SbbS2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using Em Hi.
  apply (smatch_restate segsU rhoW SokA0 SokA1 _ _ [] smatch_W0 SokA1_swf sd_SokA1); [|constructor].
  assert (E : eval rhoW (SVar 310) = eval rhoW (v 190)).
  { change (eval rhoW (SVar 310)) with (rw rhoK 310%positive).
    unfold rhoW. rewrite (ev2 ia mW (v 190) eq_refl), (ze190 ia Hi). unfold U.Mal_agrp__G1.Mal_agrp_I.zA. cbn [ia_L ia_m ia mkia]. rewrite Em. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold diffs_ok. constructor; [exact E|]. constructor; [exact E|]. constructor.
Qed.

Lemma B_rom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma swf_SokA2 : ltac2:(tb__ "0|0|
SfS5S3cSbdVia;A1A1S3A3").
Proof using A1 U X erv gd m mW md req sc. reflexivity. Qed.
Lemma smatch_W2 : ltac2:(tb__ "0|0|
S1bS3dVrhoW;SbdVia;A1S2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using Em Hi.
  unfold SokA2.
  apply (carve2p ia Hi _ _ _ _ (live_A ia Hi) ms B_rom SokA1 STKC dsC0 dsC 340%positive tr md).
  - reflexivity.
  - repeat constructor.
  - unfold dsC. repeat constructor; try exact Hervh; try reflexivity.
  - apply od2_pairwiseb_ok. reflexivity.
  - exact swf_SokA2.
  - exact smatch_W1.
Qed.

Lemma SokA2_eq : ltac2:(tb__ "0|0|
SfS31SbdVia;A1Sc9A3").
Proof using A1 U X erv gd m mW md req sc.
  unfold SokA2, SCsym. f_equal; first [vm_compute; reflexivity | cbn [ss_objs SokA1 app map dsC]; reflexivity].
Qed.
Theorem smatch_SCsym : ltac2:(tb__ "0|0|
S1bS3dVrhoW;Sc9S2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using Em Hi. rewrite <- SokA2_eq. exact smatch_W2. Qed.
End E.
End B.
End Mal_agrp_B.

Module Mal_agrp_NC.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractASK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition contN_frame (ia : instA) (rhoK : valuation) : Prop := ltac2:(tb__ "0|3|
S10S40SfS5S103R1A1S3A3SfS66Q40M0A1M1S18VrhoK;R2A2S89Via;R2A2A3F_;Fj;S10S40SfS1S66Q8A1M2A1S20VrhoK;R1A2S88Via;R1A2A3Fl;S10S3fS10S51Z0R1A2S53R1Za0A2A2SfS6G2A1S1aVrhoK;S67G0S52Z108ccR2A2A2A2S8G2A1A3F_;Fkk;S5dS5cSd5S3dS1aVrhoK;A1A2G1S3L_;A2S5eS5bA1U8S94Via;A1A4A2A2A2").

Definition contN_fail (ia : instA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|4|
S25S1S6bA1S6cS82Via;A1S41S81Via;A1S1S41A1S80Via;A1S3fS3fF_;S84Via;A1S42S7fVia;A1SfeS10S116Via;R8A2S10VKc;R7R6A2S11Sb2Sb2S10S71S3dS5bS0S41R6R5A3M0S8S7S41S3fA2A1R4R1R9R7A8S10Se3G0Sb0R1A1M1A2S10Sb4R2Sb1R1A1SdS48S4aR3A1A2A3S10S111R3G1S7bVia;A1M2A3S10S110R3G1A2S10Sd4S3dS5bSb3R3R2A2R1S83Via;A1S1aR9A1A6ScS109S10fG2A1R1A2S11S1S7S43S3fA2A1M3G3SfcS7S3fS42A2S45R3G2S7cVia;A1R6A4R1S2S3fS42N1Sb0R4A1A4A4Lktr;A2F_;Ffuel;A2A2A2A2A2A2LA2;A2A2A2TL;Ts;TU;TX;Tm;LmdK;LtrK;LrhoK;").

Definition contN_ok (ia : instA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|5|
S25S1S6bA1S6cS82Via;A1S41S81Via;A1S1S41A1S80Via;A1S3fS3fF_;S84Via;A1S42S7fVia;A1SfeS68Q40S18R8P136A2A2S3fS10S116Via;R9A2S10VKc;R8R7A2S11Sb2Sb2S11S41S41S11S46S46S10S71S3dS5bS0S41R9R8A3M0S9S7S41S3fA2S2S41S3fR2R4A4A2R7R3RcRaA8S10Se3G0Sb0R3A1M1A2S10Sb4R5Sb1R3A1SdS48S4aR6A1A2A3S10SfS6S41A1SfbG1S7bVia;A1M2A2S9S41R2A2A3S10S102G0G1R2R1A4S10SfS3fS4fR1A1G2A3S10S51S52S7cVia;A1M3S44A2S50R1A1A2S10S10S51Z0R4A2S51R4S4eR1A1A2A2S10S111R6G1G2A3S10S110R6G1A2S10Sd4S3dS5bSb3R6R5A2R3S83Via;A1S1aRcA1A6ScS109S10fG2A1R1A2S11S1S7S43S3fA2A1M4G4SfcS7S3fS42A2S45R3G2G3R9A4R1S2S3fS42R7Sb0R6A1A4A4Lktr;A2F_;Ffuel;A2A2A2A2A2A2A2A2A2A2A2Lamg;A2Lg;A2LA2;A2A2A2Tidx;TL;Ts;TU;TX;Tm;LmdK;LtrK;LrhoK;").

Section NC.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S112S3dVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let s : astate := ia_s ia. Let L : layout := ia_L ia.
Let mW : word -> option byte := ia_mW ia. Let vm : VmMaps := ia_vm ia. Let X : list sptr := ia_X ia. Let U : Z -> Z := ia_U ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S51S52S59S97Via;A1S85Via;A1A2S4cA2S58S4bZ2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S10aS77S7bVia;A1A1S77Vsc;A1A2").
Let A1 : MA := mkMA s L.

Definition JN : jpred := ltac2:(tb__ "0|0|
S25S1S6bA1S6cS10S78S3dS5bS0S41Vm;VX;A3VU;VA1;VKc;R3R2R1A9SfS3fS68Q40S18R3PcA2A2S7bVia;A1A3A2Lmd;Ltr;Lrho;").

Variable kas : Z.
Hypothesis Hkas : 0 <= kas.
Hypothesis AS : ltac2:(tb__ "0|0|
S25VTR;Vkas;Sc1S3dS114S70S6fA1R1A4Sf5S3dS3eR1S129S3dS5bS6fVNf;VOg;S0S41Vm;VX;A3VU;VA1;VKc;A9A4A3Frho1;").

Lemma HLA : ltac2:(tb__ "0|0|
S86Via;Vs;VL;VmW;Vvm;A5"). Proof using Hi. exact (live_A ia Hi). Qed.
Lemma N_facts : ltac2:(tb__ "0|4|
S10S51Vsc;Z17A2S10S51Z2S85Via;A1A2S10S10S51Z0M0S7cVia;A1M1A2S51G1Z7fcA2A2S10S10S53Vsc;S7bVia;A1M2A2S51G2Z18A2A2S10S10S51G0G2A2S53G2Z30A2A2S10S51S52G1S44A2S47G2A1M3A2S53S47Vsc;A1G3A2A2A2A2A2A2A2").
Proof using Hi Hnest Htier.
  pose proof (iok_sc ia Hi) as SC. fold sc in SC.
  pose proof (initial_cnt_facts sc (usg ia) SC) as (C1 & _ & C26).
  change (initial_cnt sc (usg ia)) with (icnt0 ia) in C1, C26.
  assert (HN : class_size sc * icnt0 ia + UNIT <= PGSZ / 2) by (unfold U.Mal_agrp__G1.Mal_agrp_I.isize in Hnest; exact Hnest).
  pose proof (nested_facts sc (icnt0 ia) SC ltac:(lia) C26 HN) as NF. cbv zeta in NF.
  assert (ET : UNIT + icnt0 ia * class_size sc - IB = itotal ia) by (unfold itotal, U.Mal_agrp__G1.Mal_agrp_I.isize; reflexivity).
  rewrite ET in NF.
  assert (EJ : size_to_class (itotal ia) = ij ia).
  { unfold ij. symmetry. apply Z.mod_small. lia. }
  rewrite EJ in NF. exact NF.
Qed.
Lemma tier_sc_pos : (1 <= ContractI.tier sc)%nat. Proof using Htier. lia. Qed.

Let u10 : Z := ltac2:(tb__ "0|0|
S68Q40S18S7dVia;A1PaA2A2").
Let u15 : Z := ltac2:(tb__ "0|0|
S68Q40S18S7dVia;A1PfA2A2").
Lemma N_sp : ltac2:(tb__ "0|3|
S10S51Z1000Vu10;A2S10SfS3fS57Vu10;Z10A2Z0A3S10S51S60VL;A1S52Vu10;Sc3Z40M0Vu15;A2M1A2A2S10S51G1N1b0A2S10S51S55S54Z2M2Z28A2A1G1A2S53Vu10;S54G2G0A2A2A2A2A2A2A2").
Proof using Hi Htier.
  pose proof (iok_sp ia Hi) as [S1 S2]. pose proof (iok_depth ia Hi) as [D1 D2]. pose proof (iok_sp_high ia Hi) as SH. pose proof tier_sc_pos as TP.
  fold u10 u15 sc in S1, S2, D1, D2, SH |- *. unfold as_stack in D1.
  pose proof (bv_unsigned_in_range 64 (rw (ia_rho ia) 10%positive)) as U10. change (bv_modulus 64%N) with (2 ^ 64) in U10. fold u10 in U10.
  repeat split; try assumption; lia.
Qed.

Section World.
Variables (rhoF : valuation) (tr : list event) (msF : machine_state) (md : Model).
Hypothesis HagF : ltac2:(tb__ "0|0|
S104S87Via;VmW;A2VrhoF;A2").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S1bS3dVrhoF;Sc7S2S1S6bA1S9aVtr;S9bVmsF;Vmd;A2A4A4").
Hypothesis HKF : ltac2:(tb__ "0|0|
S11eVKc;Via;Vtr;Vmd;A4").

Lemma SN2pre_objs : ltac2:(tb__ "0|0|
SfS1S17A1S21Sc7A1S0S17S11cScaA1SccS7aS17S7eScbA4A3A3"). Proof using . reflexivity. Qed.
Lemma dsCs_match : ltac2:(tb__ "0|0|
SfS5S12bSccS7aS17S7eScbA4S118ScbA1A2S3A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsCs_vars : ltac2:(tb__ "0|0|
SfS5Se5S17Sf6S103A1S118ScbA1A3S3A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsCs_semb : ltac2:(tb__ "0|0|
SfS5Se5S7aS11dScbA3S3A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma dsCs_cond : ltac2:(tb__ "0|0|
S7aSe4S7aR1ScbA3S11aS95Via;A1R2A2F_;Fd;").
Proof using Hi Htier. intros d Hd. pose proof (iok_sc ia Hi). apply (dcond2b_sound 0 47); [lia | exact (proj1 (forallb_forall _ _) ltac:(vm_cast_no_check (@eq_refl bool true)) d Hd)]. Qed.
Lemma dsCs_ent : ltac2:(tb__ "0|0|
S7aSe4S7aR1ScbA3S13S99Via;Vs;VmW;R2A4Se4S7aR2S4S7aA1A3A2F_;Fd;").
Proof using .
  intros d Hd. left. unfold dsCs, D_m0 in Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [od2_entry]; repeat split; reflexivity.
Qed.

Definition m1 : word -> option byte := ltac2:(tb__ "0|0|
S11bVmsF;VrhoF;ScbA3").
Definition rhoB : valuation := set_rm rhoF m1.

Lemma HLV1 : ltac2:(tb__ "0|0|
S86Via;Vs;VL;S6aVvm;A5").
Proof using HagF Hi HsmF Htier.
  exact (live' ia Hi s L mW vm HLA tr md msF rhoF HagF SN2pre STKC (map obj_of2 dsCs) dsCs [] SN2pre_objs dsCs_match HsmF dsCs_vars dsCs_semb dsCs_cond dsCs_ent
           s [] (iok_I ia Hi) (iok_Xr ia Hi) (delta_refl s) ltac:(intros d []) ltac:(intros l []) (iok_hd ia Hi) (iok_m_raw ia Hi)).
Qed.
Lemma SFr_eq : ltac2:(tb__ "0|0|
SfS31S119Sc7ScaA2SadA3"). Proof using . reflexivity. Qed.
Lemma smatch_SNr0 : ltac2:(tb__ "0|0|
S1bS3dS69SadS2S1S6bA1S9aVtr;S9bVmsF;Vmd;A2A4A4").
Proof using HsmF. rewrite <- SFr_eq. exact (smatch_released tr md msF rhoF SN2pre STKC (map obj_of2 dsCs) dsCs SN2pre_objs dsCs_match HsmF ltac:(rewrite SFr_eq; exact SNr0_swf)). Qed.
Lemma AG1 : ltac2:(tb__ "0|0|
S104S87Via;S6aA2S69A2"). Proof using HagF. exact (agrees_released ia mW msF rhoF HagF dsCs). Qed.
Lemma rwB j : ltac2:(tb__ "0|0|
SfS5S103Vj;A1S3A3SfS66Q40A1S18S69Vj;A2S89Via;Vj;A2A3F_;"). Proof using HagF. intros Hj. exact (proj1 AG1 j Hj). Qed.
Lemma rwB_low j : ltac2:(tb__ "0|0|
Se6Vj;P64A2S12SfS40Vj;PcA3A1S12SfS40Vj;PdA3A1SfS66Q40A1S18S69Vj;A2S18S7dVia;A1Vj;A2A3F_;F_;F_;").
Proof using HagF Hi Htier. intros H1 H2 H3. rewrite rwB by (unfold below200; apply Pos.ltb_lt; lia). exact (rw2_low ia Hi j H1 H2 H3). Qed.
Lemma rlB l : ltac2:(tb__ "0|0|
SfS1S66Q8A1A1S20S69Vl;A2S88Via;Vl;A2A3"). Proof using HagF. exact (proj1 (proj2 AG1) l). Qed.
Lemma rmB : rm rhoB = m1. Proof using . reflexivity. Qed.
Lemma F_rom : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.

Lemma smatch_SNr : ltac2:(tb__ "0|0|
S1bS3dS69SafS2S1S6bA1S9aVtr;S9bVmsF;Vmd;A2A4A4").
Proof using HagF Hi HsmF Htier u10 u15.
  pose proof N_sp as (S1 & _ & _ & D1 & D2 & U10).
  apply (smatch_restate segsU rhoB SNr0 SNr _ [] _ smatch_SNr0 SNr_swf sd_SNr); [constructor|].
  constructor; [|constructor; [|constructor]].
  - cbn [SymState.holds eval]. rewrite (rwB_low 10) by (cbv; first [reflexivity | discriminate]). rewrite u64 by lia. exact S1.
  - rewrite (holds_zholds rhoB) by reflexivity. cbn [zholds zcond zeval]. unfold zr_of.
    rewrite (rwB_low 15) by (cbv; first [reflexivity | discriminate]). fold u15.
    pose proof (bv_unsigned_in_range 64 (rw (ia_rho ia) 15%positive)) as U15. change (bv_modulus 64%N) with (2 ^ 64) in U15. fold u15 in U15.
    rewrite (Z.mod_small u15) by lia. replace (toS 64 ((- 432) mod 2 ^ 64)) with (- 432) by reflexivity.
    apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma smatch_SNS : ltac2:(tb__ "0|0|
S1bS3dS69SaeS2S1S6bA1S9aVtr;S9bVmsF;Vmd;A2A4A4").
Proof using HagF Hi HsmF Htier u10 u15. exact (smatch_xforms segsU _ rhoB SNr SNS _ SNS_ok smatch_SNr). Qed.

Section Call.
Variable ms1 : machine_state.
Hypothesis HsmC : ltac2:(tb__ "0|0|
S1bS3dS69SaaS2S1S6bA1S9aVtr;S9bVms1;Vmd;A2A4A4").
Definition rho1 : valuation := ltac2:(tb__ "0|0|
Sd1Sd2S69Sa8Vms1;A3Sa9A2").

Lemma C_rom : rom_ok segsU ms1. Proof using HsmC. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmC))))). Qed.

Definition oFrm : sobj := nth 1 (ss_objs EvN) O_stk.
Lemma rng_frm : ltac2:(tb__ "0|0|
SfS7S3fS3fA2S33S69Sa1A2S2S3fS3fS52Vu10;N90A2S52Vu10;Z0A2A4A3").
Proof using HagF Hi Htier u15.
  unfold obj_range, obj_lo_of, obj_hi_of, oFrm. cbn [nth ss_objs EvN ob_base ob_lo ob_hi eval].
  rewrite (rwB_low 10) by (cbv; first [reflexivity | discriminate]). rewrite !soff_lit_small by lia. reflexivity.
Qed.
Definition inFrm (a : Z) : Prop := ltac2:(tb__ "0|0|
S10S51S56Vu10;Z90A2Va;A2S53Va;Vu10;A2A2").
Lemma in_RcN a : ltac2:(tb__ "0|0|
S10S51Z0Va;A2S53Va;S54Z2Z40A2A2A2S14ScfS69Sa8S67Q40Va;A2A3Sa0Va;A1A2F_;").
Proof using HagF Hi Htier.
  intros Ha. unfold in_ranges, inFrm. rewrite RcN_eq, u64 by lia. change (nth 1 (ss_objs EvN) O_stk) with oFrm. split.
  - intros (o & Ho & R0). destruct Ho as [<-|[]]. rewrite rng_frm in R0. cbn [fst snd] in R0. lia.
  - intros H. exists oFrm. split; [left; reflexivity|]. rewrite rng_frm. cbn [fst snd]. lia.
Qed.
Lemma rm1_at a : ltac2:(tb__ "0|3|
SfS6S66Q8A1A1M0S1aS9fVa;A2Se7ScfS69Sa8Va;A3M1S12G1A1M2A2G0L_;Sd0S69Sa8Va;A3G1SecVms1;Va;A2L_;G2S6aVa;A1L_;Xe7x2A3").
Proof using . unfold rho1, rho_sub, rho_absorb. cbn [rm]. destruct (in_ranges_dec rhoB RcN a); reflexivity. Qed.

Lemma frm_holds : ltac2:(tb__ "0|0|
S27S3dS69Vms1;Sa1A4").
Proof using HsmC.
  destruct HsmC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [snd cfg_ms] in Hall.
  exact (proj1 (Forall_forall _ _) Hall oFrm ltac:(cbn; tauto)).
Qed.
Lemma frm_byte a : ltac2:(tb__ "0|1|
Sa0Va;A1S11S66Q8A1M0G0SfS6G0A1SecVms1;S67Q40Va;A2A2S9G0R1A2A3Lb;A2F_;").
Proof using HagF Hi HsmC Htier.
  intros Ha. pose proof N_sp as (S1 & _ & SH & D1 & _ & U10). top_ranges. unfold inFrm in Ha.
  destruct (dunk_byte segsU rhoB ms1 oFrm a frm_holds eq_refl ltac:(rewrite rng_frm; cbn [fst snd]; lia)) as [[b Hb] _].
  unfold rd, ms_read_byte in Hb. destruct (ms_mem ms1 (Z_to_bv 64 a)) as [b0|] eqn:E; [exists b0; reflexivity|].
  exfalso. rewrite (C_rom (Z_to_bv 64 a)) in Hb. rewrite (image_byte_none_high rhoB) in Hb; [discriminate|]. rewrite segs_topU, u64 by lia. lia.
Qed.

Lemma E_sp1 : ltac2:(tb__ "0|0|
SfS3fS68Q40S18S9fPaA2A2S56Vu10;Z90A2A3").
Proof using HagF Hi Htier u15.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sN 10%positive) with (SAlu ALU_ADD (SVar 10) (SLit (-144))).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. rewrite (rwB_low 10) by (cbv; first [reflexivity | discriminate]). fold u10.
  pose proof N_sp as (S1 & _ & _ & _ & _ & U10).
  rewrite (Z.mod_small u10) by lia. change ((-144) mod 2 ^ 64) with (2 ^ 64 - 144).
  replace (u10 + (2 ^ 64 - 144)) with ((u10 - 144) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma E_depth1 : ltac2:(tb__ "0|1|
SfS3fSc3Z40M0S68Q40S18S9fPfA2A2A2S52Sc3G0Vu15;A2Z90A2A3").
Proof using HagF Hi Htier u10.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sN 15%positive) with (SAlu ALU_ADD (SVar 15) (SLit 144)).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. rewrite (rwB_low 15) by (cbv; first [reflexivity | discriminate]). fold u15.
  pose proof N_sp as (_ & _ & _ & D1 & D2 & _).
  pose proof (bv_unsigned_in_range 64 (rw (ia_rho ia) 15%positive)) as U15. change (bv_modulus 64%N) with (2 ^ 64) in U15. fold u15 in U15.
  rewrite (Z.mod_small u15) by lia. change (144 mod 2 ^ 64) with 144. apply toS64_add_small; lia.
Qed.
Lemma E_a0 : ltac2:(tb__ "0|0|
SfS3fS68Q40S18S9fPcA2A2S7bVia;A1A3").
Proof using HagF Hi.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sN 12%positive) with (SVar 169%positive). cbn [eval].
  rewrite (rwB 169) by reflexivity. pose proof (zr2_169 ia Hi) as E. unfold zr2, zr_of, rho2 in E. cbn [rw] in E.
  exact E.
Qed.
Lemma E_a1 : ltac2:(tb__ "0|0|
SfS3fS68Q40S18S9fPdA2A2S7cVia;A1A3").
Proof using HagF Hi.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sN 13%positive) with (SVar 168%positive). cbn [eval].
  rewrite (rwB 168) by reflexivity. pose proof (zr2_168 ia Hi) as E. unfold zr2, zr_of, rho2 in E. cbn [rw] in E.
  exact E.
Qed.
Lemma E_tp1 : ltac2:(tb__ "0|0|
SfS3fS68Q40S18S9fP18A2A2S63S5bA1A3").
Proof using HagF Hi Htier u10 u15.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sN 24%positive) with (SVar 24%positive). cbn [eval].
  rewrite (rwB_low 24) by (cbv; first [reflexivity | discriminate]). exact (iok_tp ia Hi).
Qed.

Lemma MI_1 : ltac2:(tb__ "0|0|
S10eS5bS0S41Vm;VX;A3S8S7S41S3fA2A1VU;Sb3Vs;VL;A2Sd5S3dS6aA2Sd6S3dS6aA2Vvm;A8").
Proof using HR0 HagF Hi HsmF Htier u10 u15. rewrite rd_of_CG, wok_of_CG, <- HR0. exact (lv_MI ia s L m1 vm HLV1). Qed.
Lemma ctx1 : ly_ctx L = 0x5a3d0. Proof using HR0 HagF Hi HsmF Htier U X m s u10 u15 vm. exact (mig_ctx MI_1). Qed.
Lemma init1 : st_init_done s = true. Proof using HagF Hi HsmF Htier L u10 u15 vm. exact (init_true ia s L m1 vm HLV1). Qed.

Lemma MI_call : ltac2:(tb__ "0|2|
SfS6eS6dVmd;A1M0Vvm;A3S10eS5bS0S41Vm;VX;A3S8S7S41S3fA2A1VU;Sb3Vs;VL;A2Sd5S3dS1aS9fA1M1A2Sd6S3dG1A2G0A8F_;").
Proof using HR0 HagF Hi HsmC HsmF Htier u10 u15.
  intros ->. pose proof N_sp as (S1 & S2 & SH & D1 & D2 & U10). top_ranges.
  unfold MInvI. apply (minvG_frame_core C_U (m :: X) None U s L _ _ _ _ vm inFrm MI_1 (iok_Xr ia Hi)).
  -
    intros a Ha NF.
    assert (E : rm rho1 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
    { rewrite rm1_at. destruct (in_ranges_dec rhoB RcN (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcN a Ha) in I0. exfalso. exact (NF I0). }
    unfold Contract.rd_of, Contract.wok_of. rewrite E. split; reflexivity.
  -
    intros a Ha _. unfold Contract.rd_of. rewrite rm1_at. destruct (in_ranges_dec rhoB RcN (Z_to_bv 64 a)) as [I0|O0].
    + destruct (frm_byte a Ha) as [b Hb]. exists b. rewrite Hb. reflexivity.
    + exfalso. apply O0. unfold inFrm in Ha. apply (in_RcN a ltac:(lia)). exact Ha.
  - intros a. unfold inFrm. lia.
  -
    intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s l n He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. rewrite ctx1 in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L s vm p n (mig_vm MI_1) (mig_ledger MI_1) He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. lia.
  - intros a Ha Hs. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  - intros Hf. exfalso. rewrite init1 in Hf. discriminate Hf.
Qed.

Lemma IN_ok : ltac2:(tb__ "0|0|
SfS6eS6dVmd;A1Vvm;A3VKc;Vtr;Vmd;A2S114S9fVtr;Vmd;A3F_;F_;").
Proof using HR0 HagF Hi Hnest HsmC HsmF Htier.
  intros Hvm HKc. pose proof N_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof N_sp as (_ & _ & _ & D1 & _).
  pose proof (iok_depth ia Hi) as [DP _]. fold sc u15 in DP.
  split; [|exact E_a0]. split; [exact (MI_call Hvm)|]. split; [exact (iok_Xr ia Hi)|]. split; [exact HKc|].
  split.
  - cbn zeta. rewrite E_a0, E_a1. change (bv_unsigned (rw rho1 V_DEPTH)) with (bv_unsigned (rw rho1 15%positive)). rewrite E_depth1.
    split; [exact F5|]. split; [lia|]. split; [exact F6|].
    unfold as_stack in *. pose proof Htier as HT. fold sc in HT.
    assert (Z.of_nat (ContractI.tier (ij ia)) + 1 <= Z.of_nat (ContractI.tier sc)) by lia. nia.
  - split; [unfold tp_ok; exact E_tp1|].
    split; [intros Hf; exfalso; unfold A1 in Hf; cbn [ma_s] in Hf; rewrite init1 in Hf; discriminate Hf|].

    unfold top_high, V_DEPTH, A1. cbn [ma_L]. rewrite E_sp1, E_depth1. pose proof N_sp as (_ & _ & SH & _). lia.
Qed.

Section Out.
Variables (Lx : sstate) (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S1bS3dVrhoL;VLx;S2S1S6bA1S9aVtr';S9bVms';Vmd';A2A4A4").
Hypothesis HLx_objs : ltac2:(tb__ "0|0|
SfS1S17A1S21VLx;A1S0S17Sd7S73A1S4S17A1A3A3").
Variable A2 : MA.
Hypothesis Hkept : ltac2:(tb__ "0|0|
Sd4S3dS5bVA1;VA2;S1aS9fA1S1aVrhoL;A1A6").

Hypothesis Htop2 : ltac2:(tb__ "0|0|
SfS3fS60Sb1VA2;A1A1S60VL;A1A3").
Hypothesis HagL : ltac2:(tb__ "0|0|
Sf0S3eS9fVrhoL;A3").

Lemma rhoL_10 : ltac2:(tb__ "0|0|
SfS3fS68Q40S18VrhoL;PaA2A2S56Vu10;Z90A2A3").
Proof using HagF HagL Hi Htier u15. try clear Htop2. rewrite <- (proj1 HagL 10%positive) by (cbv; reflexivity). exact E_sp1. Qed.
Lemma rhoL_15 : ltac2:(tb__ "0|1|
SfS3fSc3Z40M0S68Q40S18VrhoL;PfA2A2A2S52Sc3G0Vu15;A2Z90A2A3").
Proof using HagF HagL Hi Htier u10. try clear Htop2. rewrite <- (proj1 HagL 15%positive) by (cbv; reflexivity). exact E_depth1. Qed.
Lemma stkL_rng : ltac2:(tb__ "0|2|
SfS7S3fS3fA2S33VrhoL;Sd7S73A1A2S2S3fS3fS52S56Vu10;Z90M0A2M1S52Sc3Z40Vu15;A2G0A2A2S52G1Z0A2A4A3").
Proof using HagF HagL Hi Htier. try clear Htop2.
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd eval].
  rewrite soff_lit_small by lia. unfold soff, V_DEPTH. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  cbn [eval]. rewrite rhoL_10, rhoL_15. reflexivity.
Qed.

Lemma rhoL_rom a : ltac2:(tb__ "0|2|
S10S51Z108ccM0Va;A2S53Va;S52G0Za0A2A2A2SfS6S66Q8A1M1A1S1aVrhoL;S67Q40Va;A2A2S8G1A1A3F_;").
Proof using HLx_objs HagF HagL Hi HsmL Htier u10 u15. try clear Htop2.
  intros Ha. pose proof N_sp as (_ & _ & SH & _ & _ & _). top_ranges.
  destruct HsmL as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr; [apply Hro; replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia|].
  unfold outside_all. rewrite HLx_objs. constructor; [|constructor]. cbn zeta. rewrite u64 by lia. rewrite stkL_rng. cbn [fst snd]. lia.
Qed.

Lemma kept_RcN a : ltac2:(tb__ "0|0|
ScfS69Sa8Va;A3SfS6S66Q8A1A1S1aVrhoL;Va;A2S1aS9fVa;A2A3F_;").
Proof using HagF Hi Hkept Htop2 Htier u10 u15.
  intros IN0. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64%N) with (2 ^ 64) in Ra.
  rewrite <- (Z_to_bv_bv_unsigned 64 a) in IN0 |- *.
  pose proof N_sp as (_ & _ & SH & D1 & _ & _). top_ranges.
  pose proof (proj1 (in_RcN (bv_unsigned a) Ra) IN0) as F. unfold inFrm in F.
  apply (Hkept (bv_unsigned a) Ra).
  - left. unfold A1. cbn [ma_L]. lia.
  - left. rewrite Htop2. lia.
  - unfold errno_range, mc_errno. cbn [mc_tp C_U]. lia.
  - unfold alloc_static. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]. lia.
Qed.

Lemma iok_L : ltac2:(tb__ "0|0|
Sf2S69Vms1;Sa8Sa9S70S6fA1VLx;VrhoL;A7").
Proof using HLx_objs HagF Hi Hkept Htop2 Htier u10 u15.
  split.
  - intros a Ha. exact (kept_RcN a Ha).
  - intros o' oR Hin' _. exfalso. revert Hin'. unfold new_objs. rewrite HLx_objs. cbn. tauto.
Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
Sf1S69Vms1;Sa8Sa9S70S6fA1SaaVLx;Vrho'';VrhoL;A9").
Definition rhoP : valuation := ltac2:(tb__ "0|0|
S128Vrho'';S127S69Vrho'';Sa8A3A2").

Lemma rmP_at a : ltac2:(tb__ "0|3|
SfS6S66Q8A1A1M0S1aSd8Va;A2Se7ScfS69Sa8Va;A3M1S12G1A1M2A2G0L_;Sd0S69Sa8Va;A3G1S6aVa;A1L_;G2S1aVrhoL;Va;A2L_;Xe7x2A3").
Proof using Hlink. try clear Htop2.
  unfold rhoP, rho_patch, patchf. cbn [rm]. destruct (in_ranges_dec rhoB RcN a); [reflexivity | apply (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink)].
Qed.
Lemma rwP j : ltac2:(tb__ "0|0|
Se6Vj;P12cA2SfS66Q40A1S18Sd8Vj;A2S18S69Vj;A2A3F_;").
Proof using Hlink. try clear Htop2.
  intros Hj. unfold rhoP, rho_patch. cbn [rw]. rewrite (call_linkP_rw _ _ _ _ _ _ _ _ _ j Hlink) by (change (ss_next EvN) with 300%positive; exact Hj). reflexivity.
Qed.
Lemma rlP l : ltac2:(tb__ "0|0|
SfS1S66Q8A1A1S20Sd8Vl;A2S20S69Vl;A2A3").
Proof using Hlink. try clear Htop2. unfold rhoP, rho_patch. cbn [rl]. exact (call_linkP_rl _ _ _ _ _ _ _ _ _ l Hlink). Qed.

Lemma MI_patch R2 md2 : ltac2:(tb__ "0|2|
S71S3dS5bS0S41Vm;VX;A3M0VR2;VU;VA2;VrhoL;Vmd2;A8Se3G0Sb0VA2;A1M1A2SfS5S49G1A1S3A3S71S3dS5bG0VR2;VU;VA2;Sd8Vmd2;A8F_;F_;F_;").
Proof using HagF Hi Hkept Htop2 Hlink Htier u10 u15.
  pose proof Htop2 as ET. clear Htop2.
  destruct A2 as [s2 L2]. cbn [ma_s]. intros HM HX1 Hinit1. unfold MInvIR, MInvI in *. cbn [ma_s ma_L] in *.
  pose proof N_sp as (S1 & S2 & SH & D1 & D2 & U10). top_ranges.
  apply (minvG_frame_core C_U (m :: X) R2 U s2 L2 _ _ _ _ (m_vmmaps md2) inFrm HM HX1).
  - intros a Ha NF.
    assert (E : rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
    { rewrite rmP_at. destruct (in_ranges_dec rhoB RcN (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcN a Ha) in I0. exfalso. exact (NF I0). }
    unfold Contract.rd_of, Contract.wok_of. rewrite E. split; reflexivity.
  - intros a Ha Hg. exfalso. unfold inFrm in Ha. cbn [mc_chk_guard C_U] in Hg. top_ranges. lia.
  - intros a. unfold inFrm. lia.
  - intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s2 l n He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. pose proof (mig_ctx HM) as CX. cbn [ma_L mc_ctx C_U] in CX. rewrite CX in Hx. unfold CTX_SIZE in Hx. top_ranges. lia.
    + pose proof (fp_mem_range C_U L2 s2 (m_vmmaps md2) p n (mig_vm HM) (mig_ledger HM) He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. top_ranges. lia.
  - intros a Ha Hs. top_ranges. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  - intros Hf. rewrite Hinit1 in Hf. discriminate Hf.
Qed.

Lemma kept_patch : ltac2:(tb__ "0|0|
Sd4S3dS5bVA1;VA2;S6aS1aSd8A1A6").
Proof using Hkept Hlink. try clear Htop2.
  intros a Ha HcA HcA1 Hne Hns.
  rewrite rmP_at. destruct (in_ranges_dec rhoB RcN (Z_to_bv 64 a)) as [I0|O0]; [reflexivity|].
  rewrite (Hkept a Ha HcA HcA1 Hne Hns). rewrite rm1_at. destruct (in_ranges_dec rhoB RcN (Z_to_bv 64 a)) as [I0|_]; [exfalso; exact (O0 I0)|]. reflexivity.
Qed.

Lemma kept_all : ltac2:(tb__ "0|0|
Sd4S3dS5bVA1;VA2;VmW;S1aSd8A1A6").
Proof using HagF Hi Hkept Hlink HsmF Htier u10 u15 vm. try clear Htop2.
  intros a Ha HcA HcA1 Hne Hns. rewrite (kept_patch a Ha HcA HcA1 Hne Hns).
  exact (lv_kept ia s L m1 vm HLV1 a Ha HcA HcA Hne Hns).
Qed.

Hypothesis Hcan : ltac2:(tb__ "0|0|
S79S3dS5bS1aS9fA1S1aVrhoL;A1A4").
Lemma contN_frame_P : contN_frame ia rhoP.
Proof using HLx_objs HagF HagL Hcan Hi Hlink HsmF HsmL Htier. try clear Htop2.
  pose proof N_sp as (S1 & S2 & SH & D1 & D2 & U10). top_ranges.
  split; [intros j Hj; rewrite rwP by (unfold below200 in Hj; apply Pos.ltb_lt in Hj; lia); exact (rwB j Hj)|].
  split; [intros l; rewrite rlP; exact (rlB l)|].
  split.
  - intros kk Hk. rewrite rmP_at. destruct (in_ranges_dec rhoB RcN _) as [I0|_]; [|apply rhoL_rom; lia].
    apply (in_RcN (0x108cc + kk) ltac:(lia)) in I0. unfold inFrm in I0. exfalso. lia.
  -
    intros k Hk. pose proof (lv_gd ia s L m1 vm HLV1 k Hk) as G.
    assert (EG : mc_chk_guard C_U = 369464) by reflexivity. rewrite EG in G |- *.
    assert (NR : ~ in_ranges rhoB RcN (Z_to_bv 64 (369464 + Z.of_nat k))).
    { intros I0. apply (in_RcN (369464 + Z.of_nat k) ltac:(lia)) in I0. unfold inFrm in I0. lia. }
    assert (E1 : Glue.rd_of segsU (rm rhoP) (Z_to_bv 64 (369464 + Z.of_nat k)) = Glue.rd_of segsU (rm rhoL) (Z_to_bv 64 (369464 + Z.of_nat k))).
    { apply rd_of_mem. rewrite rmP_at. destruct (in_ranges_dec rhoB RcN _) as [I0|_]; [exfalso; exact (NR I0) | reflexivity]. }
    pose proof (Hcan (369464 + Z.of_nat k) ltac:(rewrite EG; lia)) as CK. rewrite (rd_of_CG (rm rhoL)), (rd_of_CG (rm rho1)) in CK.
    assert (E3 : Glue.rd_of segsU (rm rho1) (Z_to_bv 64 (369464 + Z.of_nat k)) = Glue.rd_of segsU m1 (Z_to_bv 64 (369464 + Z.of_nat k))).
    { apply rd_of_mem. rewrite rm1_at. destruct (in_ranges_dec rhoB RcN _) as [I0|_]; [exfalso; exact (NR I0) | reflexivity]. }
    rewrite rd_of_CG. unfold byteview_of in G |- *. rewrite E1, CK, E3. exact G.
Qed.
End Out.

Lemma init_of_xraw X2 R2 U2 s2 : ltac2:(tb__ "0|0|
SfdVX2;VR2;VU2;Vs2;A4Se3VX2;Vs2;A2Se4S41Vm;VX2;A3SfS5S49Vs2;A1S3A3F_;F_;F_;").
Proof using ia.
  intros HI HX Hm. destruct (st_init_done s2) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 HI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  assert (K : In m (keys s2)).
  { destruct (HX m Hm) as [H|H]; exact (MT_Some_In_keys _ _ _ H). }
  unfold keys in K. rewrite M in K. destruct K.
Qed.

Section OutFail.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S1bS3dVrhoL;S72S6fA1S2S1S6bA1S9aVtr';S9bVms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
Sf0S3eS9fVrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
S75S3dS5bS0S41Vm;VX;A3VU;VA1;VKc;S9fVrhoL;Vtr';Vmd';Aa").

Lemma iok_fail : ltac2:(tb__ "0|0|
Sf2S69Vms1;Sa8Sa9S70S6fA1S72S6fA1VrhoL;A7").
Proof using HJL HagF Hi Htier u10 u15. destruct HJL as (A2 & _ & _ & Hext & _ & _ & Hkept & _). exact (iok_L (L_as_fail IEC_U) rhoL eq_refl A2 Hkept (layout_extends_top _ _ _ Hext)). Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
Sf1S69Vms1;Sa8Sa9S70S6fA1SaaS72S6fA1Vrho'';VrhoL;A9").

Lemma cont_fail w : ltac2:(tb__ "0|0|
VKc;S10cVw;A1S9cS10bVw;A1A1A2Sc1S3dSf3S75S3dS5bS0S41Vm;VX;A3VU;VA1;VKc;A6S9fVrhoL;A3Sf4Sa9S1fS70S6fA1A1S72S6fA1S1fSaaA1Sa8A5Vrho'';Vw;A5Sc1S3dS115Via;VKc;A2SabSa2Vrho'';A1Vw;A5F_;F_;").
Proof using HagF HagL Hi Hlink HsmC HsmF HsmL Htier.
  intros HKw [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ', HKw.
  destruct HJ' as (A2 & HM2 & HX2 & Hext2 & Hhb2 & Hub2 & Hkept2 & Hcan2 & Hy2 & HKc2).
  assert (Hag'' : agree_vals (ss_next EvN) rhoB rho'') by exact (proj1 Hlink).
  split.
  - apply (smatch_xforms segsU _ _ TfailN SNfail _ SNfail_ok). rewrite <- TfailN_eq.
    exact (cont_smatch segsU EvN (Pre_as IEC_U) (L_as_fail IEC_U) sN RcN rhoB rho'' tr ms1 md _ entN HsmC eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model]. unfold contN_fail. cbv zeta.
    split; [exact (contN_frame_P (L_as_fail IEC_U) rhoL tr' ms' md' HsmL eq_refl HagL rho'' Hlink Hcan2)|].
    split; [exact HKc2|].
    exists A2.
    split; [exact (MI_patch (L_as_fail IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink None mdw HM2 HX2 (init_of_xraw _ _ _ _ (mig_I HM2) HX2 ltac:(left; reflexivity)))|].
    split; [exact HX2|]. split; [exact Hext2|].
    cbn zeta in Hhb2, Hy2. rewrite E_a0 in Hhb2, Hy2. rewrite E_a1 in Hy2.
    split; [exact Hhb2|]. split; [exact Hub2|].
    split; [exact (kept_all (L_as_fail IEC_U) rhoL A2 Hkept2 rho'' Hlink)|].
    exact Hy2.
Qed.
End OutFail.

Section OutOk.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S1bS3dVrhoL;S74S6fA1S2S1S6bA1S9aVtr';S9bVms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
Sf0S3eS9fVrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
S76S3dS5bS0S41Vm;VX;A3VU;VA1;VKc;S9fVrhoL;Vtr';Vmd';Aa").

Lemma iok_ok : ltac2:(tb__ "0|0|
Sf2S69Vms1;Sa8Sa9S70S6fA1S74S6fA1VrhoL;A7").
Proof using HJL HagF Hi Htier u10 u15. destruct HJL as (A2 & g & amg & _ & _ & Hext & _ & _ & _ & _ & _ & _ & _ & Hkept & _). exact (iok_L (L_as_ok IEC_U) rhoL eq_refl A2 Hkept (layout_extends_top _ _ _ Hext)). Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
Sf1S69Vms1;Sa8Sa9S70S6fA1SaaS74S6fA1Vrho'';VrhoL;A9").

Lemma cont_ok w : ltac2:(tb__ "0|0|
VKc;S10cVw;A1S9cS10bVw;A1A1A2Sc1S3dSf3S76S3dS5bS0S41Vm;VX;A3VU;VA1;VKc;A6S9fVrhoL;A3Sf4Sa9S1fS70S6fA1A1S74S6fA1S1fSaaA1Sa8A5Vrho'';Vw;A5Sc1S3dS117Via;VKc;A2SacSa2Vrho'';A1Vw;A5F_;F_;").
Proof using HagF HagL Hi Hlink HsmC HsmF HsmL Htier.
  intros HKw [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ', HKw.
  destruct HJ' as (A2 & g & amg & HM2 & HX2 & Hext2 & Hhd2 & Hu2 & Hsc2 & Hfit2 & Hidx2 & Hhb2 & Hub2 & Hkept2 & Hcan2 & Hy2 & HKc2).
  assert (Hag'' : agree_vals (ss_next EvN) rhoB rho'') by exact (proj1 Hlink).
  assert (E310 : rw (rhoP rho'') 310%positive = rw rhoL V_RES).
  { unfold rhoP. cbn [rho_patch rw]. destruct Hlink as (_ & _ & _ & L4).
    rewrite (L4 V_RES eq_refl ltac:(cbv; lia)).
    change (ss_next (Pre_as IEC_U)) with NF. change (ss_next EvN) with 300%positive. rewrite impN_VRES. reflexivity. }
  split.
  - apply (smatch_xforms segsU _ _ TokN SNok _ SNok_ok). rewrite <- TokN_eq.
    exact (cont_smatch segsU EvN (Pre_as IEC_U) (L_as_ok IEC_U) sN RcN rhoB rho'' tr ms1 md _ entN HsmC eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model]. unfold contN_ok. cbv zeta. rewrite E310.
    split; [exact (contN_frame_P (L_as_ok IEC_U) rhoL tr' ms' md' HsmL eq_refl HagL rho'' Hlink Hcan2)|].
    split; [exact HKc2|].
    exists A2, g, amg.
    split; [exact (MI_patch (L_as_ok IEC_U) rhoL A2 Hkept2 (layout_extends_top _ _ _ Hext2) rho'' Hlink (Some (g, bv_unsigned (rw rhoL V_RES))) mdw HM2 HX2 (init_of_xraw _ _ _ _ (mig_I HM2) HX2 ltac:(left; reflexivity)))|].
    split; [exact HX2|]. split; [exact Hext2|].
    cbn zeta in Hhd2, Hsc2, Hfit2, Hhb2, Hy2. rewrite E_a0 in Hhd2, Hsc2, Hhb2, Hy2. rewrite E_a1 in Hfit2, Hy2.
    split; [exact Hhd2|]. split; [exact Hu2|]. split; [exact Hsc2|]. split; [exact Hfit2|]. split; [exact Hidx2|].
    split; [exact Hhb2|]. split; [exact Hub2|].
    split; [exact (kept_all (L_as_ok IEC_U) rhoL A2 Hkept2 rho'' Hlink)|].
    exact Hy2.
Qed.
End OutOk.
End Call.
End World.

Variable Q : assn.
Hypothesis CONT_fail : ltac2:(tb__ "0|0|
VNf;S25VTR;VkB;Sc1S3dS115Via;VKc;A2SabR1A4VQ;A3FrhoK;F_;").
Hypothesis CONT_ok : ltac2:(tb__ "0|0|
VOg;S25VTR;VkB;Sc1S3dS117Via;VKc;A2SacR1A4VQ;A3FrhoK;F_;").

Theorem step_N : ltac2:(tb__ "0|0|
VTR;S52Vkas;VkB;A2S12cS3dS11eVKc;Via;A2S11fVia;VmW;A2Sc7A4VQ;A3").
Proof using AS CONT_fail CONT_ok HR0 Hi HkB Hkas Hnest Htier RR.
  unfold WalkSeg.POST. (apply (trr_ex RR); [lia|]). intros rhoF.
  (apply (trr_inhP RR); [lia|]). intros [tr [msF md]] [HagF [HsmF HKF]]. change (agrees (rho2 ia mW) rhoF) in HagF.
  pose proof HKF as [HKc Hvm]. cbn [w_tr w_cfg cfg_model] in HKc, Hvm.
  set (K0 := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  exists (SPJ segsU (liftK K0) EvN (rhoB rhoF msF)). split.
  { apply (SPJ_unbase segsU (liftK K0) (rhoB rhoF msF) SNS 0 (-144) EvN _ EvN_ok).
    split; [exact (smatch_SNS rhoF tr msF md HagF HsmF)|]. cbn. split; [exact HKc | split; reflexivity]. }
  apply ((trr_callP RR) kas kB (liftK K0) JN EvN (Pre_as IEC_U) sN RcN (Posts_asG segsU C_U IEC_U Nf Og (m :: X) U A1 Kc) Q (rhoB rhoF msF) HkB entN chkN AS).
  -
    intros tr1 ms1 md1 HsmE [HK [-> ->]].
    exact (IN_ok rhoF tr msF md HagF HsmF ms1 HsmE Hvm HKc).
  -
    intros L1 JL tr1 ms1 md1 rhoL tr' ms' md' HinL HsmE [HK [-> ->]] HagL HsmL HJL.
    cbn [Posts_asG In] in HinL. destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L1 JL; [destruct HJL as [HG HJL] | destruct HJL as [HG HJL]].
    +
      split; [exact (iok_fail rhoF msF HagF ms1 rhoL tr' md' HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU (contN_fail ia Kc) SNfail (rhoP rhoF msF rho'')) _ Q); [|apply (CONT_fail HG)].
      intros w [HsmW [_ HJw]]. apply (cont_fail rhoF tr msF md HagF HsmF ms1 HsmE rhoL tr' ms' md' HsmL HagL rho'' Hlink w); [|exact (conj HsmW HJw)]. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJw |- *.
      destruct HJw as (A2 & _ & _ & _ & _ & _ & _ & _ & _ & HKc2). exact HKc2.
    +
      split; [exact (iok_ok rhoF msF HagF ms1 rhoL tr' md' HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU (contN_ok ia Kc) SNok (rhoP rhoF msF rho'')) _ Q); [|apply (CONT_ok HG)].
      intros w [HsmW [_ HJw]]. apply (cont_ok rhoF tr msF md HagF HsmF ms1 HsmE rhoL tr' ms' md' HsmL HagL rho'' Hlink w); [|exact (conj HsmW HJw)]. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJw |- *.
      destruct HJw as (A2 & g & amg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKc2). exact HKc2.
Qed.
End NC.
End Mal_agrp_NC.

Module Mal_agrp_rNF.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs.

Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Set Printing Width 300. Set Printing Depth 100000.

Definition mkCN0 (E : sstate) : sstate := ltac2:(tb__ "0|0|
S120VE;S0S17Sc8S0S17Sc4S0S17Sc5S0S17S122S4S17A1A3A3A3A3S4S1eA1A3").
Definition mkCNR (E : sstate) : sstate := ltac2:(tb__ "0|0|
S120VE;S0S17Sc8S0S17Sc4S0S17Sc5S0S17S123S0S17S124S0S17S125S4S17A1A3A3A3A3A3A3S121A3").

Definition CN0 : sstate := ltac:(let y := eval vm_compute in (mkCN0 SNfail) in exact y).
Lemma CN0_eq : ltac2:(tb__ "0|0|
SfS31SdfSabA1Sd9A3"). Proof. vm_cast_no_check (@eq_refl sstate CN0). Qed.
Definition MRN0 : option (list leaf) := ltac2:(tb__ "0|0|
Sa4Se2U1f4Se1Sd9S3A5").
Definition MRN0__f : option (list leaf) := ltac2:(tb__ "0|0|
SefSe2U1f4Se1Sd9S3A5").
Definition RN0 : option (list leaf) := ltac:(let y := eval vm_compute in MRN0__f in exact y).
Lemma MRN0_c : MRN0 = RN0. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN0 MRN0__f. Qed.
Definition XN0 : sstate := ltac:(let y := eval vm_compute in (leaf1 RN0) in exact y).
Lemma RN0_shape : ltac2:(tb__ "0|1|
SfS6S1Sa3A1M0A1SddS9G0S0Sa3Sa6SdbSa5A2S4Sa3A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RN0). Qed.
Lemma runN0 : ltac2:(tb__ "0|1|
SfS6S1Sa3A1M0A1Sa4Se2U1f4Se1Sd9S3A5S9G0S0Sa3Sa6SdbSa5A2S4Sa3A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CN0 true) MRN0 _ (@eq_refl _ (sym_run segs 500 CUTS_K CN0 true)) (@eq_trans _ MRN0 RN0 _ MRN0_c RN0_shape)). Qed.

Definition CNR : sstate := ltac:(let y := eval vm_compute in (mkCNR SNfail) in exact y).
Lemma CNR_eq : ltac2:(tb__ "0|0|
SfS31Se0SabA1SdaA3"). Proof. vm_cast_no_check (@eq_refl sstate CNR). Qed.
Definition MRNR : option (list leaf) := ltac2:(tb__ "0|0|
Sa4Se2U1f4Se1SdaS3A5").
Definition MRNR__f : option (list leaf) := ltac2:(tb__ "0|0|
SefSe2U1f4Se1SdaS3A5").
Definition RNR : option (list leaf) := ltac:(let y := eval vm_compute in MRNR__f in exact y).
Lemma MRNR_c : MRNR = RNR. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRNR MRNR__f. Qed.
Definition XNR : sstate := ltac:(let y := eval vm_compute in (leaf1 RNR) in exact y).
Lemma RNR_shape : ltac2:(tb__ "0|1|
SfS6S1Sa3A1M0A1SdeS9G0S0Sa3Sa6SdcSa5A2S4Sa3A1A3A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) RNR). Qed.
Lemma runNR : ltac2:(tb__ "0|1|
SfS6S1Sa3A1M0A1Sa4Se2U1f4Se1SdaS3A5S9G0S0Sa3Sa6SdcSa5A2S4Sa3A1A3A2A3").
Proof. exact (@eq_trans _ (sym_run segs 500 CUTS_K CNR true) MRNR _ (@eq_refl _ (sym_run segs 500 CUTS_K CNR true)) (@eq_trans _ MRNR RNR _ MRNR_c RNR_shape)). Qed.

Lemma SNfail_misc : ltac2:(tb__ "0|1|
S10SfS5S24SabA1SaA3S10SfS5S24Sd9A1SaA3S10SfS40S1fSd9A1S1fSabA1M0A3S10SfS5S24SdaA1SaA3SfS40S1fSdaA1G0A3A2A2A2A2").
Proof. repeat split; reflexivity. Qed.
Lemma CN0_swf : swf CN0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma CNR_swf : swf CNR = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Mal_agrp_rNF.

Module Mal_agrp_N0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition SnullG : sstate := ltac2:(tb__ "0|0|
S22S2aS9eA1S2bS9eA1S29S9eA1S28S9eA1S2cS9eA1SbS17S21S9eA1S0S17Sc4S0S17Sc5S4S17A1A3A3A3S23S9eA1S1fS9eA1S24S9eA1A9").
Lemma SnullG_swf : swf SnullG = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition CUTS_N0 : list Z := [0x202a8].
Definition MRN0 : option (list leaf) := ltac2:(tb__ "0|0|
Sa4S3dU12cSb7Sb6S3A5").
Definition MRN0__f : option (list leaf) := ltac2:(tb__ "0|0|
SefS3dU12cSb7Sb6S3A5").
Definition RN0 : option (list leaf) := ltac:(let x := eval vm_compute in MRN0__f in exact x).
Lemma MRN0_c : MRN0 = RN0. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRN0 MRN0__f. Qed.
Lemma runN0 : ltac2:(tb__ "0|0|
SfS6S1Sa3A1A1Sa4S3dU12cSb7Sb6S3A5SbaA3").
Proof. exact (@eq_trans _ (sym_run segsU 300 CUTS_N0 SnullG true) MRN0 RN0 (@eq_refl _ (sym_run segsU 300 CUTS_N0 SnullG true)) MRN0_c). Qed.
Definition LN0 : sstate := ltac:(let x := eval vm_compute in (match RN0 with Some [l] => lf_state l | _ => bad_state end) in exact x).
Lemma RN0_shape : ltac2:(tb__ "0|1|
SfS6S1Sa3A1M0A1SbaS9G0S0Sa3Sa6Sb5Sa5A2S4Sa3A1A3A2A3"). Proof. reflexivity. Qed.

Definition LN0r : sstate := ltac2:(tb__ "0|0|
S22S2aSb5A1S2bSb5A1S29Sb5A1S28Sb5A1S2cSb5A1SceS17U1S21Sb5A1A3S23Sb5A1S1fSb5A1S24Sb5A1A9").
Lemma LN0_objs : ltac2:(tb__ "0|1|
SfS1S17A1S21Sb5A1M0SbS17SceS17U1G0A3S0S17Sc6S0S17Sc4S0S17Sc5S4S17A1A3A3A3A3A3"). Proof. reflexivity. Qed.
Lemma LN0r_swf : swf LN0r = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition sN0 : wsub := ltac:(let x := eval vm_compute in (infer_sub NF LN0r (L_as_fail IEC_U)) in exact x).
Lemma entN0 : ltac2:(tb__ "0|0|
SfS5S126Sb9S72S6fA1Sb8A3S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sN0_id : ltac2:(tb__ "0|0|
SfS5Sd3Sb8S3eA2S3A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma Lfail_norl l : ltac2:(tb__ "0|0|
SfS5SebVl;S72S6fA1A2SaA3"). Proof. destruct l; reflexivity. Qed.

Section N0.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 rhoK : valuation).
Variables (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S112S3dVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HNf : Nf.

Section W.
Variables (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S1bS3dVrhoK;S9eS2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Hypothesis HC : ltac2:(tb__ "0|0|
S113VX;VU;VA;VKc;Vrho0;VrhoK;Vtr;Vmd;A8").
Let K : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S1S6bA1S6cS10VKc;R2R1A2SfS6cR1Vmd;A3A2Lmd';Ltr';").

Lemma N_frame : contA_frame rho0 rhoK. Proof using HC. exact (proj1 HC). Qed.
Lemma N_pure : contA_pure rho0. Proof using HC. exact (proj1 (proj2 (proj2 HC))). Qed.
Lemma N_rom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.
Lemma rwK j : ltac2:(tb__ "0|0|
Se6Vj;P12cA2SfS66Q40A1S18VrhoK;Vj;A2S18Vrho0;Vj;A2A3F_;"). Proof using HC. exact (proj1 N_frame j). Qed.
Lemma E173K : ltac2:(tb__ "0|1|
SfS66Q40M0A1S18VrhoK;PadA2S67G0S5eS5bA1A2A3").
Proof using HC. rewrite (rwK 173) by reflexivity. exact (proj2 (proj2 (proj2 (proj2 (proj2 N_pure))))). Qed.

Lemma got_wsegN k : ltac2:(tb__ "0|0|
S10S51Z0Vk;A2S53Vk;Z8A2A2SfS5SfaS3dS67Q40S52Z28d50Vk;A2A2A2S3A3F_;").
Proof using K tr. intros Hk. exact (forall_range_dec (fun k => wseg_addr segsU (Z_to_bv 64 (0x28d50 + k))) 0 8 ltac:(vm_compute; reflexivity) k ltac:(lia)). Qed.
Lemma guard_wsegN k : ltac2:(tb__ "0|0|
S10S51Z0Vk;A2S53Vk;Z8A2A2SfS5SfaS3dS67Q40S52Z5a338Vk;A2A2A2S3A3F_;").
Proof using K tr. intros Hk. exact (forall_range_dec (fun k => wseg_addr segsU (Z_to_bv 64 (0x5a338 + k))) 0 8 ltac:(vm_compute; reflexivity) k ltac:(lia)). Qed.

Lemma hold_word (base : sv) (cv : sv) (b z : Z) : ltac2:(tb__ "0|9|
SfS3fS68Q40M0S32VrhoK;Vbase;A2A2Vb;A3SfS66G0A1S32VrhoK;Vcv;A2S67G0Vz;A2A3S10S51Z0M1Vz;A2S53Vz;S54Z2Z40A2M2A2A2S51G1Vb;A2S51S52Vb;Z8M3A2G2A2S3fS10S51G1R1A2S53R1G3A2A2SfS5SfaS3dS67G0S52Vb;R2A2A2A2S3A3F_;Fk;ScS10aR1U8M4A2SfS6S66Q8M5A1M6A1Sd5S3dS1aVrhoK;A1M7S67G0S52Vb;S5aR2A1A2A2A3S9G6S67G5S100Vz;G4R2A3A2A2A3F_;Fk;S27S3dVrhoK;SedVms;G7A2S26Vbase;S19G1A1M8S19G3A1S0S1cS1dG8G3Vcv;A3S4S1cA1A3S2dA5A4F_;F_;F_;F_;F_;F_;F_;").
Proof using Hsm K.
  intros Hb Hv Hz Hb0 Hb1 Hw Hrd.
  change (mkObj base (SLit 0) (SLit 8) [mkCell (SLit 0) 8 cv] DUnknown) with (carved base 0 8 [(0, 8%nat, cv)]).
  apply obj_holds_frame_lit; rewrite ?Hb; try exact N_rom; try lia.
  - unfold cells_inside. repeat constructor; cbn; lia.
  - intros o Ho. split.
    + unfold Glue.wok_of. destruct (rm rhoK (Z_to_bv 64 (b + o))); [reflexivity|]. apply Hw. lia.
    + pose proof (Hrd (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite rd_of_CG in E. eexists. exact E.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    pose proof (Hrd j Hj) as E. rewrite rd_of_CG in E. rewrite E, Hv, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma hold_gotN : ltac2:(tb__ "0|0|
S27S3dVrhoK;SedVms;S1aVrhoK;A1A2Sc4A4").
Proof using HC Hsm K.
  apply (hold_word (SLit 0x28d50) (v 173) 0x28d50 (mc_chk_guard C_U)); try (cbn; lia).
  - cbn [eval]. apply u64. lia.
  - cbn [eval v]. exact E173K.
  - exact got_wsegN.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 N_frame))))).
Qed.
Lemma hold_guardN : ltac2:(tb__ "0|0|
S27S3dVrhoK;SedVms;S1aVrhoK;A1A2Sc5A4").
Proof using HC Hsm K.
  apply (hold_word (v 173) (v 174) (mc_chk_guard C_U) (bv_unsigned (rw rho0 174%positive))); try (cbn; lia).
  - cbn [eval v]. rewrite E173K. reflexivity.
  - cbn [eval v]. rewrite (rwK 174) by reflexivity. symmetry. apply Z_to_bv_bv_unsigned.
  - apply urange.
  - exact guard_wsegN.
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 N_frame))))).
Qed.

Let u10 : Z := bv_unsigned (rw rhoK 10%positive).
Let u15 : Z := bv_unsigned (rw rhoK 15%positive).
Lemma N_win : ltac2:(tb__ "0|5|
S10S51Sc3Z40M0Vu15;A2M1S55S73A1A2S10S51S55S54Z2M2Z28A2A1G1A2S10S51Z0M3S52Vu10;G1A2M4A2S10S51Z7fff7f800000G4A2S10SfS3fS57Vu10;Z10A2G3A3S53Vu10;S54G2G0A2A2A2A2A2A2A2").
Proof using Hsm K.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hf). cbn [fst snd cfg_ms ss_objs ss_facts] in Hall, Hf.
  assert (F3 : Forall (SymState.holds rhoK) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)).
  { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hf). cbn in Hp. cbn. decompose [or] Hp; subst; tauto. }
  pose proof (window_facts segsU rhoK ms AS_D (nth 0 (ss_objs SnullA) O_stk) ltac:(unfold AS_D; lia) F3 eq_refl eq_refl (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & _).
  unfold u10, u15. repeat split; assumption.
Qed.

Lemma smatch_SnullG : ltac2:(tb__ "0|0|
S1bS3dVrhoK;Sb6S2S1S6bA1S9aVtr;S9bVms;Vmd;A2A4A4").
Proof using HC Hsm K.
  pose proof N_win as (W1 & W2 & W3 & W4 & W5 & W6). top_ranges.
  apply (smatch_extend_objs segsU rhoK SnullA tr ms md [O_got; O_guard] (ss_next SnullA) Hsm SnullG_swf).
  - constructor; [exact hold_gotN|]. constructor; [exact hold_guardN|]. constructor.
  - assert (RG : obj_range rhoK O_got = (0x28d50, 0x28d50 + 8)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_got. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. }
    assert (RU : obj_range rhoK O_guard = (mc_chk_guard C_U, mc_chk_guard C_U + 8)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_guard. cbn [ob_base ob_lo ob_hi eval v]. rewrite E173K, !soff_lit_small, u64 by (cbn; lia). reflexivity. }
    assert (RS : obj_range rhoK (nth 0 (ss_objs SnullA) O_stk) = (u10 + toS 64 u15, u10 + 0)).
    { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval nth ss_objs SnullA]. rewrite soff_lit_small by lia.
      unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). reflexivity. }
    assert (RT : obj_range rhoK (nth 1 (ss_objs SnullA) O_stk) = (0x108ec + 0, 0x108ec + 96)).
    { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval nth ss_objs SnullA]. rewrite !soff_lit_small, u64 by lia. reflexivity. }
    change (ss_objs SnullA) with [nth 0 (ss_objs SnullA) O_stk; nth 1 (ss_objs SnullA) O_stk].
    constructor; [|constructor; [|constructor]]; (constructor; [|constructor; [|constructor]]); unfold SymState.ranges_disjoint;
      rewrite ?RG, ?RU, ?RS, ?RT; cbn [fst snd mc_chk_guard C_U]; lia.
  - cbn [pairwise_disjoint]. split; [|split; [constructor | exact I]]. constructor; [|constructor].
    unfold SymState.ranges_disjoint.
    unfold obj_range, obj_lo_of, obj_hi_of, O_got, O_guard. cbn [ob_base ob_lo ob_hi eval v fst snd]. rewrite E173K, !soff_lit_small, !u64 by (cbn; lia). cbn. lia.
Qed.

Section Exit.
Variables (rho' : valuation) (tr' : list event) (ms' : machine_state).
Hypothesis Hab : ltac2:(tb__ "0|0|
S38S1fS9eA1VrhoK;Vrho';A3").
Hypothesis HSP : ltac2:(tb__ "0|0|
S1bS3dVrho';Sb5S2S1S6bA1S9aVtr';S9bVms';Vmd;A2A4A4").
Hypothesis HKc' : Kc tr' md.

Let m' : word -> option byte := ltac2:(tb__ "0|0|
S12aVrho';S0S17Sc6S0S17Sc4S0S17Sc5S4S17A1A3A3A3Vms';A3").
Let rhoR : valuation := ltac2:(tb__ "0|0|
S3aS18Vrho';A1S20Vrho';A1Vm';A3").
Definition rhoF : valuation := ltac2:(tb__ "0|1|
SeaSd1VrhoR;Sb8A2P1M0S20Vrho0;G0A2A3").

Lemma rw' j : ltac2:(tb__ "0|0|
Se6Vj;P154A2SfS66Q40A1S18Vrho';Vj;A2S18VrhoK;Vj;A2A3F_;"). Proof using Hab. intros Hj. symmetry. exact (proj1 Hab j Hj). Qed.
Lemma rl' l : ltac2:(tb__ "0|0|
SfS1S66Q8A1A1S20Vrho';Vl;A2S20VrhoK;Vl;A2A3"). Proof using Hab. symmetry. exact (proj1 (proj2 Hab) l). Qed.
Lemma rm' a : ltac2:(tb__ "0|0|
SfS6S66Q8A1A1S1aVrho';Va;A2S1aVrhoK;Va;A2A3"). Proof using Hab. symmetry. exact (proj2 (proj2 Hab) a). Qed.

Lemma rel : ltac2:(tb__ "0|5|
S10S1bS3dVrhoR;Sb9S2S1S6bA1S9aVtr';S9bVms';Vmd;A2A4A4S10S66Q40A1M0S12ScfVrho';S0S17Sc6S0S17Sc4S0S17Sc5S4S17A1A3A3A3M1R1A3M2A1SfS6S66Q8A1A1M3Vm';R2A1M4S1aVrho';R2A2A3F_;Fa;S10G0G2SfG3G4SecVms';R2A2A3F_;Fa;ScdS17S27S3dVrho';Vms';A3G1A3A2A2A2").
Proof using HSP. exact (smatch_release_suffix segsU rho' LN0 tr' ms' md (firstn 1 (ss_objs LN0)) [O_sct; O_got; O_guard] (ss_next LN0) HSP LN0_objs LN0r_swf). Qed.

Lemma E173' : ltac2:(tb__ "0|1|
SfS66Q40M0A1S18Vrho';PadA2S67G0S5eS5bA1A2A3"). Proof using HC Hab. rewrite (rw' 173) by reflexivity. exact E173K. Qed.
Lemma rngs a : ltac2:(tb__ "0|4|
S10S51Z0Va;A2S53Va;S54Z2Z40A2A2A2S14ScfVrho';S0S17Sc6S0S17Sc4S0S17Sc5S4S17A1A3A3A3S67Q40Va;A2A3S13S10S51Z108ecM0Va;A2S53Va;S52G0Z60A2A2A2S13S10S51Z28d50M1Va;A2S53Va;S52G1Z8M2A2A2A2S10S51S5eS5bA1M3Va;A2S53Va;S52G3G2A2A2A2A2A2A2F_;").
Proof using HC Hab K tr' u10 u15.
  intros Ha.
  assert (RT : obj_range rho' O_sct = (0x108ec + 0, 0x108ec + 96)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_sct. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. }
  assert (RG : obj_range rho' O_got = (0x28d50 + 0, 0x28d50 + 8)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_got. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. }
  assert (RU : obj_range rho' O_guard = (mc_chk_guard C_U + 0, mc_chk_guard C_U + 8)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_guard. cbn [ob_base ob_lo ob_hi eval v]. rewrite E173', !soff_lit_small, u64 by (cbn; lia). reflexivity. }
  unfold in_ranges. rewrite u64 by lia. split.
  - intros (o & Ho & R0). destruct Ho as [<-|[<-|[<-|[]]]]; [rewrite RT in R0 | rewrite RG in R0 | rewrite RU in R0]; cbn [fst snd] in R0; lia.
  - intros [H|[H|H]]; [exists O_sct | exists O_got | exists O_guard]; (split; [cbn; tauto|]); [rewrite RT | rewrite RG | rewrite RU]; cbn [fst snd]; lia.
Qed.

Lemma C_ro' : ro_clear segsU ms'. Proof using HSP. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HSP)))))). Qed.
Lemma C_rom' : rom_ok segsU ms'. Proof using HSP. exact (proj1 (proj2 (proj2 (proj2 (proj2 HSP))))). Qed.

Lemma canary_m' : ltac2:(tb__ "0|0|
Sf9S3dS5bS68Q40S18Vrho0;PaeA2A2Vm';A4").
Proof using HC HSP Hab K rhoR u10 u15.
  pose proof (proj2 (proj2 (proj2 rel))) as HO. apply Forall_cons_iff in HO as [_ HO]. apply Forall_cons_iff in HO as [HG HO]. apply Forall_cons_iff in HO as [HU _].
  pose proof (proj1 (proj2 (proj2 rel))) as IN.
  split; intros k Hk; cbn [mc_chk_guard_got C_U].
  - assert (Ha : 0 <= 0x28d50 + Z.of_nat k < 2 ^ 64) by lia.
    rewrite rd_of_CG, (rd_of_at segsU m' ms' _ C_rom' (IN _ (proj2 (rngs _ Ha) ltac:(right; left; lia)))).
    pose proof (cell_bytes_sym segsU rho' ms' O_got (mkCell (SLit 0) 8 (v 173)) k HG ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base O_got c_off c_val c_width eval v] in B. rewrite soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E173'. rewrite nth_enc_bytes by (cbn; lia). reflexivity.
  - assert (Ha : 0 <= mc_chk_guard C_U + Z.of_nat k < 2 ^ 64) by (cbn; lia).
    rewrite rd_of_CG, (rd_of_at segsU m' ms' _ C_rom' (IN _ (proj2 (rngs _ Ha) ltac:(right; right; lia)))).
    pose proof (cell_bytes_sym segsU rho' ms' O_guard (mkCell (SLit 0) 8 (v 174)) k HU ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base O_guard c_off c_val c_width eval v] in B. rewrite E173', soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite (rw' 174) by reflexivity. rewrite (rwK 174) by reflexivity.
    rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho0 174%positive)). rewrite nth_enc_bytes by (pose proof (urange (rw rho0 174%positive)); lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma m'_views a : ltac2:(tb__ "0|2|
S10S51Z0Va;A2S53Va;S54Z2Z40A2A2A2S10SfS6S66Q8A1A1Sd5S3dVm';S67Q40Va;A2M0A3Sd5S3dS1aVrhoK;A1M1G0A3A3SfS5Sd6S3dVm';G0A3Sd6S3dG1G0A3A3A2F_;").
Proof using HC HSP Hab K rhoR.
  intros Ha. pose proof rel as (_ & OUT & IN & _). pose proof N_frame as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (in_ranges_dec rho' [O_sct; O_got; O_guard] (Z_to_bv 64 a)) as [I0|O0].
  2:{ rewrite !rd_of_CG, !wok_of_CG. pose proof (OUT _ O0) as E. rewrite rm' in E. split; [apply rd_of_mem; exact E | apply wok_of_mem; exact E]. }
  pose proof (IN _ I0) as E. apply (rngs a Ha) in I0. destruct I0 as [T|[G|G]].
  -
    assert (E0 : m' (Z_to_bv 64 a) = rm rhoK (Z_to_bv 64 a)).
    { rewrite E. rewrite (C_ro' (Z_to_bv 64 a)) by (replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia).
      symmetry. replace a with (0x108cc + (a - 0x108cc)) by lia. apply F4. lia. }
    rewrite !rd_of_CG, !wok_of_CG. split; [apply rd_of_mem; exact E0 | apply wok_of_mem; exact E0].
  - split.
    + pose proof (proj1 canary_m' (Z.to_nat (a - 0x28d50)) ltac:(lia)) as C1. cbn [mc_chk_guard_got C_U] in C1. rewrite Z2Nat.id in C1 by lia.
      replace (167248 + (a - 167248)) with a in C1 by lia. rewrite C1.
      pose proof (F5 (Z.to_nat (a - 0x28d50)) ltac:(lia)) as C2. cbn [mc_chk_guard_got C_U] in C2. rewrite Z2Nat.id in C2 by lia.
      replace (167248 + (a - 167248)) with a in C2 by lia. rewrite C2. reflexivity.
    + unfold Contract.wok_of. pose proof (got_wsegN (a - 0x28d50) ltac:(lia)) as W. replace (0x28d50 + (a - 0x28d50)) with a in W by lia.
      change (Contract.wseg_addr segsU (Z_to_bv 64 a)) with (wseg_addr segsU (Z_to_bv 64 a)).
      destruct (m' (Z_to_bv 64 a)); destruct (rm rhoK (Z_to_bv 64 a)); rewrite ?W; reflexivity.
  - split.
    + pose proof (proj2 canary_m' (Z.to_nat (a - mc_chk_guard C_U)) ltac:(lia)) as C1. rewrite Z2Nat.id in C1 by lia.
      replace (mc_chk_guard C_U + (a - mc_chk_guard C_U)) with a in C1 by lia. rewrite C1.
      pose proof (F6 (Z.to_nat (a - mc_chk_guard C_U)) ltac:(lia)) as C2. rewrite Z2Nat.id in C2 by lia.
      replace (mc_chk_guard C_U + (a - mc_chk_guard C_U)) with a in C2 by lia. rewrite C2. reflexivity.
    + unfold Contract.wok_of. cbn [mc_chk_guard C_U] in G. pose proof (guard_wsegN (a - 0x5a338) ltac:(lia)) as W.
      replace (0x5a338 + (a - 0x5a338)) with a in W by lia.
      change (Contract.wseg_addr segsU (Z_to_bv 64 a)) with (wseg_addr segsU (Z_to_bv 64 a)).
      destruct (m' (Z_to_bv 64 a)); destruct (rm rhoK (Z_to_bv 64 a)); rewrite ?W; reflexivity.
Qed.

Lemma MI_exit X1 (A1 : MA) : ltac2:(tb__ "0|1|
S71S3dS5bVX1;S8S7S41S3fA2A1M0VU;VA1;VrhoK;Vmd;A8Se3VX1;Sb0VA1;A1A2S71S3dS5bVX1;G0VU;VA1;S12fVmd;A8F_;F_;").
Proof using HC HSP Hab K.
  destruct A1 as [s1 L1]. cbn [ma_s]. intros HM HX1. unfold MInvIR, MInvI in *. cbn [ma_s ma_L rm rhoF rho_set_rl rho_sub rhoR] in *.
  apply (minvG_frame_core C_U X1 None U s1 L1 _ _ _ _ (m_vmmaps md) (fun _ => False) HM HX1).
  - intros a Ha _. exact (m'_views a Ha).
  - intros a [].
  - intros a. right. intros [].
  - intros a [].
  - intros a [].
  - intros Hf. pose proof (mig_auxv HM Hf) as AV.
    replace (byteview_of (Contract.rd_of segsU m') (fun _ => true)) with (byteview_of (Contract.rd_of segsU (rm rhoK)) (fun _ => true)); [exact AV|].
    apply FunctionalExtensionality.functional_extensionality. intros a. unfold byteview_of.
    destruct ((0 <=? a) && (a <? 2 ^ 64) && true)%bool eqn:Eb; [|reflexivity].
    apply andb_prop in Eb as [Eb _]. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (proj1 (m'_views a ltac:(lia))). reflexivity.
Qed.

Theorem exit_post : ltac2:(tb__ "0|0|
Sf8S3dS5bS6fVNf;VOg;VX;VU;VA;VKc;Vrho0;S2S1S6bA1S9aVtr';S9bVms';Vmd;A2A4Ab").
Proof using HC HKc' HNf HSP Hab rhoR u10 u15.
  pose proof HC as (HF & _ & HP & A1 & HM1 & HPC & Hhd1 & Hkept & Hy). pose proof N_frame as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof rel as (HsmR & OUT & IN & _).
  exists (L_as_fail IEC_U), (JLg_failG segsU C_U Nf X U A Kc), rhoF.
  split; [left; reflexivity|].
  split.
  {   split.
    - intros i Hi. unfold rhoF, rho_set_rl, rho_sub. cbn [rw]. rewrite (wsub_get_id sN0 NF i sN0_id Hi). cbn [eval rhoR rw].
      rewrite (rw' i) by (unfold NF in Hi; lia). symmetry. apply F1. unfold NF in Hi. lia.
    - intros l. unfold rhoF, rho_set_rl, rho_sub. cbn [rl rhoR]. destruct (Pos.eqb_spec l 1) as [->|Hl]; [reflexivity|].
      rewrite rl'. symmetry. exact (F3 l Hl). }
  split.
  { unfold rhoF. apply SymCall.smatch_set_rl; [apply Lfail_norl|]. exact (entails_sound segsU LN0r (L_as_fail IEC_U) sN0 rhoR _ entN0 HsmR). }
  cbn [w_tr w_cfg cfg_model]. unfold JLg_failG. split; [exact HNf|]. unfold JLg_fail.
  assert (E12 : bv_unsigned (rw rho0 12%positive) = bv_unsigned (rw rho0 12%positive)) by reflexivity.
  exists A1.
  split; [exact (MI_exit X A1 HM1 (proj1 HPC))|].
  split; [exact (proj1 HPC)|].
  split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPC)))))))|].
  split. { intros c Hc. destruct HPC as (_ & _ & _ & (EA & _) & _). unfold active_hd. rewrite EA. reflexivity. }
  split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPC))))))|].
  split.
  { intros a Ha HcA HcA1 Hne Hns. cbn [rm rhoF rho_set_rl rho_sub rhoR].
    rewrite <- (Hkept a Ha HcA HcA1 Hne Hns).
    destruct (in_ranges_dec rho' [O_sct; O_got; O_guard] (Z_to_bv 64 a)) as [I0|O0]; [|rewrite (OUT _ O0); apply rm'].
    pose proof (IN _ I0) as E. apply (rngs a Ha) in I0. destruct I0 as [T|[G|G]].
    - rewrite E. rewrite (C_ro' (Z_to_bv 64 a)) by (replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia).
      symmetry. replace a with (0x108cc + (a - 0x108cc)) by lia. apply F4. lia.
    - exfalso. apply Hns. unfold alloc_static. cbn [mc_chk_guard_got C_U]. lia.
    - exfalso. apply Hns. unfold alloc_static. lia. }
  split; [exact canary_m'|].
  split; [|exact HKc'].
  intros fuel Hfuel. destruct Hy as [ktr Hy]. exists ktr. destruct fuel as [|f]; [pose proof (need_ge2 (bv_unsigned (rw rho0 12%positive))); lia|]. apply ag_nometa. exact Hy.
Qed.
End Exit.

Theorem null_sound_w : ltac2:(tb__ "0|0|
VTR;VkB;Sc2S3dVK;Sb6VrhoK;A4Sf8S3dS5bS6fVNf;VOg;VX;VU;VA;VKc;Vrho0;AaA3").
Proof using HC HNf HkB RR.
  apply ((trr_run RR) kB 300%nat CUTS_N0 K SnullG [mkLeaf LN0 RsSymJump] rhoK _ HkB (eq_trans runN0 RN0_shape) eq_refl ltac:(intros t m [H _]; exact H)).
  intros Lf rho' [<-|[]] Hab. cbn [lf_state].
  (apply (trr_skip RR); [lia|]). intros [tr' [ms' md']] [HsmL [HK Emd]]. cbn [w_tr w_cfg cfg_model fst snd] in HK, Emd, HsmL. subst md'.
  exact (exit_post rho' tr' ms' Hab HsmL HK).
Qed.
End W.

Theorem null_path : ltac2:(tb__ "0|0|
VTR;VkB;Sc1S3dS113VX;VU;VA;VKc;Vrho0;A5S9eVrhoK;A4Sf8S3dS5bS6fVNf;VOg;VX;VU;VA;VKc;Vrho0;AaA3").
Proof using HNf HkB RR.
  (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HC]. cbn [w_tr w_cfg cfg_model] in HC.
  exists (SymSoundR.SP segsU (fun tr' md' => Kc tr' md' /\ md' = md) SnullG rhoK). split.
  - split; [exact (smatch_SnullG tr ms md Hsm HC)|]. cbn. split; [exact (proj1 (proj2 HC)) | reflexivity].
  - exact (null_sound_w tr md HC).
Qed.
End N0.
End Mal_agrp_N0.

Module Mal_agrp_Pv.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record prov (ia : instA) (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation) : Prop := mkProv {
  pv_X : ia_X ia = X;
  pv_U : ia_U ia = U;
  pv_R : ia_R ia = None;
  pv_sc : ia_sc ia = bv_unsigned (rw rho0 12%positive);
  pv_req : ia_req ia = bv_unsigned (rw rho0 13%positive);
  pv_gd : ia_gd ia = bv_unsigned (rw rho0 174%positive);
  pv_mW : ia_mW ia = rm (ia_rho ia);
  pv_frame : contA_frame rho0 (ia_rho ia);
  pv_pure : contA_pure rho0;
  pv_ext : layout_extends (ma_L A) (ia_L ia) (length (st_regions (ma_s A)));
  pv_nreg : (length (st_regions (ma_s A)) <= length (st_regions (ia_s ia)))%nat;
  pv_ub : ub_same (ma_s A) (ia_s ia);
  pv_kept : mem_kept segsU C_U A (mkMA (ia_s ia) (ia_L ia)) (rm rho0) (ia_mW ia);
  pv_I0 : Inv X None U (ma_s A);
  pv_hd0 : active_hd (ma_s A) (ia_sc ia) = None;
  pv_am : exists ktr, yields (alloc_meta (ma_s A)) ktr (Some (ia_m ia), ia_s ia) }.

Section PV.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 rhoK : valuation).
Variables (tr : list event) (ms : machine_state) (md : Model).
Variables (A1 : MA) (m : sptr).
Let sc : Z := bv_unsigned (rw rho0 12%positive).
Hypothesis HF : contA_frame rho0 rhoK.
Hypothesis HP : contA_pure rho0.
Hypothesis HC : ltac2:(tb__ "0|0|
S10dVX;S0S41Vm;VX;A3VA;VA1;A4").
Hypothesis Hkept : ltac2:(tb__ "0|0|
Sd4S3dS5bVA;VA1;S1aVrho0;A1S1aVrhoK;A1A6").
Hypothesis Hy : ltac2:(tb__ "0|2|
S11S1S7S43S3fA2A1M0G0SfcS7S6S41A1M1S42A2S4dSb0VA;A1A1R1S2G1S42S9S41Vm;A2Sb0VA1;A1A4A4Lktr;A2").
Hypothesis HI0 : ltac2:(tb__ "0|0|
SfdVX;S8S7S41S3fA2A1VU;Sb0VA;A1A4").
Hypothesis Hhd0 : ltac2:(tb__ "0|0|
SfS6S41A1SfbSb0VA;A1Vsc;A2S8S41A1A3").

Lemma mkia_prov erv : ltac2:(tb__ "0|0|
S130SbfVX;VU;Vrho0;VrhoK;Vmd;VA1;Vm;Verv;A8VX;VU;VA;Vrho0;A5").
Proof using HC HF HI0 HP Hhd0 Hkept Hy.
  pose proof HC as (_ & _ & Hfr & _ & _ & Hub & _ & Hext). pose proof Hfr as (_ & _ & _ & Hlen & _).
  constructor; cbn [ia_s ia_L ia_X ia_R ia_U ia_sc ia_req ia_rho ia_m ia_gd ia_erv ia_vm ia_mW mkia]; try reflexivity.
  - exact HF.
  - exact HP.
  - exact Hext.
  - exact Hlen.
  - exact Hub.
  - destruct A1. exact Hkept.
  - exact HI0.
  - exact Hhd0.
  - destruct A1. exact Hy.
Qed.
End PV.
End Mal_agrp_Pv.
