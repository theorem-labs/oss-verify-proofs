(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "option"; "list"; "prod"; "true"; "Some"; "bool"; "None"; "false"; "app"; "fst"; "nat"; "snd"; "negb"; "andb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sv"; "SLit"; "sprop"; "cell"; "mkCell"; "SPUle"; "SAlu"; "sobj"; "SPBranch"; "sstate"; "rm"; "mkObj"; "rw"; "DUnknown"; "SPAlign"; "mkSS"; "obj_range"; "ss_next"; "FcsrFrm0"; "smatch"; "SPNot"; "ss_facts"; "valuation"; "DRom"; "reg_sv"; "rl"; "ss_pc"; "SExt"; "SLBytes"; "eval"; "ss_fcsr"; "ss_fregs"; "ss_objs"; "ss_regs"; "ss_resv"; "ss_lenient"; "rd"; "sprop_eqb"; "swf"; "obj_holds"; "image_byte"; "ranges_disjoint"; "ro_addr"; "holds"; "mkVal"; "rom_ok"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "pre_fregs"; "pre_regs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "ALU_SLL"; "BC_EQ"; "instr"; "ALU_AND"; "ALU_SLTU"; "BC_LTU"; "Ecall"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "modulo"; "mul"; "sub"; "opp"; "leb"; "of_N"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "topL"; "wz"; "mc_chk_guard"; "byteview_of"; "holds"; "mc_img_hi"; "mc_img_lo"; "mc_errno"; "size_classes_bytes"; "addr_of"; "auxv_ok"; "mc_auxv"; "mc_chk_guard_got"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "AS_D"; "MInvIR"; "auxv_init"; "J_as_pre"; "L_as_ok"; "L_as_fail"; "Pre_as"; "am_reads"; "as_stack"; "canary_kept"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "st_init_done"; "alloc_meta"; "kreq"; "IB"; "class_size"; "mslot"; "st_metas"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "RsCut"; "mkLeaf"; "instr_at"; "lf_state"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs"; "RcA"; "sA"; "EvA"; "SGS"; "CUTS_A"; "SGT"; "SnullA"; "SokA"; "ClA"; "RA"; "TnullA"; "TokA"; "factsA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G"; "SG"; "oStkG"; "oAct0"; "oGot"; "oGuard"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "m1v"; "SN2pre"; "O_stk"; "NXA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSplit"; "XSelect"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A.A.Call"; "rho1"; "oFrm"; "inFrm"; "rhoP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K"; "EK"; "SK"; "K_v"; "dsM23"; "LK"; "grant_ok"; "segs_inside"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "wok_of"; "mem_kept"; "V_RES"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "stack_win"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zholds"; "psupported";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A.A"; "mR"; "rhoT"; "RP"; "rhoR"; "SGT'"; "SGr"; "inG"; "inRP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T.T"; "m1"; "K1"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "Pre_am"; "L_am_ok"; "L_am_null"; "am_post_common"; "JL_am_null"; "JL_am_ok"; "J_am_pre"; "meta_obj0"; "AM_D"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "rho2"; "live"; "ineeded"; "set_R"; "zl2"; "zr2"; "ia_erv"; "ia_vm"; "instA_ok"; "obj_of2"; "D_ctr"; "D_errno"; "D_usg2"; "ia_L"; "@Corelib.Init.Peano"; "lt"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "in_vars"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T"; "LVc"; "STx"; "SVx"; "SWx"; "LTc"; "f_lt"; "LT"; "LV"; "SKTo"; "LW"; "e_aiF"; "e_aiT"; "e_divu"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "MA"; "ma_L"; "mkMA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "in_ranges_dec"; "wsub_get"; "rho_absorb"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "le_byte"; "active_hd"; "CTX_SIZE"; "yields"; "alloc_owned"; "in_footprint"; "keys"; "ly_ctx"; "memb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs"; "EvN"; "RcN"; "sN"; "SNS"; "SNr"; "TfailN"; "TokN"; "SNfail"; "SNok"; "SNr0"; "factsN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A.A.Call.Out"; "rhoP"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_rw_vm"; "mmap_nZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "agree_vals"; "call_linkP"; "J_ofP"; "call_checkP"; "import_okP"; "import_post"; "import_sub"; "LQP"; "obj_vars_all"; "sprop_vars_all"; "sv_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "patchf"; "rho_patch"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "F_T"; "O_map"; "SJ3"; "F_J"; "mkSKF"; "mkSKT"; "mkSKV"; "mkSKW"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "CUTS_K"; "lfs"; "LK_a"; "LK_b"; "LK_c"; "LK_d"; "LT_a"; "LT_b"; "LT_c"; "LT_d"; "LV_a"; "LV_b"; "LV_c"; "LV_d"; "LW_a"; "LW_b"; "LW_c"; "LW_d"; "SK_a"; "SK_b"; "SK_c"; "SK_d"; "ST_a"; "ST_b"; "ST_c"; "ST_d"; "SV_a"; "SV_b"; "SV_c"; "SV_d"; "SW_a"; "SW_b"; "SW_c"; "SW_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I"; "O_sct"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wseg_addr"; "wok_of";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "implK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "m1_hi"; "m1_lo"; "dsCs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR"; "NXA"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "eqb"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "zero_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A"; "contA_frame"; "contA_null"; "contA_ok"; "contA_pure"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "sym_run_fast"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "segs_top"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT"; "Posts_amG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "dcond2b"; "od2_semb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require Stdlib.Logic.FunctionalExtensionality.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_Adefs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G.

Import ListNotations.
Open Scope Z_scope.

Definition bad_state : sstate := ltac2:(tb__ "0|0|
S21ZbadS4bS4aS24S9S12A1S2S19A1S2S14A1S49SaA9").
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => bad_state end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some s => s | None => [] end.

Definition factsA : list sprop := ltac2:(tb__ "0|0|
SbS14S27S9aA1S0S14S17S13Z1000A1S11PaA1A2S2S14A1A3A3").
Definition SGT : sstate := ltac2:(tb__ "0|0|
S21S2cS9aA1S33S9aA1S31S9aA1S30S9aA1S34S9aA1S0S19S9bS0S19S162S2S19A1A3A3S99S16eSaA9").

Definition SGS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast SGT [XSplit 0 (SLit (-144))])) in exact x).
Lemma SGS_ok : ltac2:(tb__ "0|0|
S40S3S1bA1Sa4S92S0Sa3Sa7U0S13N90A1A2S2Sa3A1A3A2S7S1bS90A2A3").
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma SGS_swf : swf SGS = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition CUTS_A : list Z := [ie_am_entry IEC_U].
Definition MRA : option (list leaf) := ltac2:(tb__ "0|0|
S88S48Uc8S91S90S6A5").
Definition MRA__f : option (list leaf) := ltac2:(tb__ "0|0|
S17dS48Uc8S91S90S6A5").
Definition RA : option (list leaf) := ltac:(let x := eval vm_compute in MRA__f in exact x).
Lemma MRA_c : MRA = RA. Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.memo_cast MRA MRA__f. Qed.
Lemma runA : ltac2:(tb__ "0|0|
S40S3S4S87A1A1S88S48Uc8S91S90S6A5S96A3").
Proof. exact (@eq_trans _ (sym_run segsU 200 CUTS_A SGS true) MRA RA (@eq_refl _ _) MRA_c). Qed.
Definition ClA : sstate := ltac:(let x := eval vm_compute in (match RA with Some [l] => lf_state l | _ => bad_state end) in exact x).
Lemma RA_shape : ltac2:(tb__ "0|1|
S40S3S4S87A1M0A1S96S7G0S0S87S8aS95S89A2S2S87A1A3A2A3"). Proof. reflexivity. Qed.

Definition EvA : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast ClA 0 (-144))) in exact x).
Lemma EvA_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S177S95U0N90A3S7S1bS8fA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition sA : wsub := ltac:(let x := eval vm_compute in (infer_sub 10 EvA (Pre_am IEC_U)) in exact x).
Definition RcA : list sobj := ltac:(let x := eval vm_compute in (optR (entails_fr EvA (Pre_am IEC_U) sA)) in exact x).
Lemma entA : ltac2:(tb__ "0|1|
S40S3S4S19A1M0A1S176S8fSd3S72A1S8eA3S7G0S8dA2A3"). Proof. vm_cast_no_check (@eq_refl (option (list sobj)) (Some RcA)). Qed.
Lemma chkA : ltac2:(tb__ "0|0|
S40S8S12dS8fSd3S72A1S8eS8dS0S1bSd5S72A1S0S1bSd4S72A1S2S1bA1A3A3A5S6A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition TnullA : sstate := ltac:(let x := eval vm_compute in (T_after EvA sA RcA (L_am_null IEC_U)) in exact x).
Definition TokA : sstate := ltac:(let x := eval vm_compute in (T_after EvA sA RcA (L_am_ok IEC_U)) in exact x).
Lemma TnullA_eq : ltac2:(tb__ "0|0|
S40S1bS135S8fS8eS8dSd5S72A1A4S97A3"). Proof. vm_cast_no_check (@eq_refl sstate TnullA). Qed.
Lemma TokA_eq : ltac2:(tb__ "0|0|
S40S1bS135S8fS8eS8dSd4S72A1A4S98A3"). Proof. vm_cast_no_check (@eq_refl sstate TokA). Qed.
Definition SnullA : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TnullA [XRebase 0; XMerge 0])) in exact x).
Lemma SnullA_ok : ltac2:(tb__ "0|1|
S40S3S1bA1Sa4S97S0Sa3Sa6U0M0A1S0Sa3Sa5G0A1S2Sa3A1A3A3A2S7S1bS93A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition SokA : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TokA [XRebase 0; XSelect [0; 2; 1; 3]%nat; XMerge 0])) in exact x).
Lemma SokA_ok : ltac2:(tb__ "0|1|
S40S3S1bA1Sa4S98S0Sa3Sa6U0M0A1S0Sa3Sa8S0SdG0S0SdU2S0SdU1S0SdU3S2SdA1A3A3A3A3A1S0Sa3Sa5G0A1S2Sa3A1A3A3A3A2S7S1bS94A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

End Mal_agrp_Adefs.

Module Mal_agrp_K.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition K_v (Kc : list event -> Model -> Prop) (vmc : VmMaps) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S4SadA1SaeS41VKc;R2R1A2S40Sb2SafR1A1Vvmc;A3A2Lmd;Ltr;").
Lemma K_v_impl Kc vmc : ltac2:(tb__ "0|0|
S16aVKc;Sb5VKc;Vvmc;A2A2"). Proof. intros tr md [H _]. exact H. Qed.
Lemma K_ia_v Kc ia : ltac2:(tb__ "0|0|
S40S4SadA1SaeOF_;F_;S185VKc;Via;A2Sb5VKc;Se4Via;A1A2A3"). Proof. reflexivity. Qed.

Definition SK (x : m1v) : sstate := ltac2:(tb__ "0|0|
S9fS1bLx;Vx;S152S153S154S155X9fx4").
Definition LK (x : m1v) : list leaf := ltac2:(tb__ "0|0|
S9fS4S87A1Lx;Vx;S142S143S144S145X9fx4").
Definition EK (x : m1v) : sstate := ltac2:(tb__ "0|0|
S141Sb7Vx;A1U0Sb4Vx;A1A3").

Lemma SK_eq x : ltac2:(tb__ "0|0|
S40S1bS13aVx;A1Sb4Vx;A1A3"). Proof. destruct x; [exact SK_a_eq | exact SK_b_eq | exact SK_c_eq | exact SK_d_eq]. Qed.
Lemma runK x : ltac2:(tb__ "0|1|
S40S3S4S87A1M0A1S88S48U1f4S140Sb4Vx;A1S6A5S7G0S0S87S8aSb3Vx;A1S89A2S2S87A1A3A2A3").
Proof. destruct x; [exact (eq_trans runK_a eq_refl) | exact (eq_trans runK_b eq_refl) | exact (eq_trans runK_c eq_refl) | exact (eq_trans runK_d eq_refl)]. Qed.

Lemma EK_shape x : ltac2:(tb__ "0|3|
S41S40S3S50A1S8bS48S2cSb3Vx;A1M0A1A2S7S50S54A2A3S41S40S12S2aG0Z11A2S13ZdeA1A3S41S40S12S2aG0ZaA2S13Z0A1M1A3S41S40S12S2aG0ZbA2M2S11Pb1A1A3S41S40S12S2aG0ZcA2S13Z3A1A3S41S40S12S2aG0ZdA2S13Z22A1A3S41S40S12S2aG0ZeA2S13ZffffffffffffffffA1A3S41S40S12S2aG0ZfA2G1A3S41S40S8S35Sb4Vx;A1A1SaA3S40S8S134S46SfS170R1PbbA2A1Lu;G2A2S6A3A2A2A2A2A2A2A2A2A2").
Proof. destruct x; repeat split; vm_compute; reflexivity. Qed.

Definition dsM23 (x : m1v) : list od2 := ltac2:(tb__ "0|2|
SbSdcS16dSbSdcS0SdcSe7S163Pc5A1A1S0SdcSe8S163Pb6A1A1S2SdcA1M0A3A3S9fS4SdcA1Lx;Vx;S0SdcSe9S163Pc4A1A1G0A3M1G1G1G0X9fx4A3A3").
Lemma EK_objs x : ltac2:(tb__ "0|1|
S43S4S15A1M0G0S40S4S19A1S32Sb3Vx;A1A1S0S19S1dS11PaA1S11PfA1S13Z0A1R1S1fA5S105SdcS19Se6Sb6Vx;A1A4A3A3Lstkc;A2").
Proof. destruct x; eexists; vm_compute; reflexivity. Qed.
Lemma EK_facts x : ltac2:(tb__ "0|0|
S40S8SedS14S14SeeS14S37R1A1S27Sb3Vx;A1A1A3Lp;SbS14S0S14SbfS0S14Sc0S73A1S2S14A1A3A3SbS14SbeS73A1S13bA3A3A3S6A3").
Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma EK_no187 x : ltac2:(tb__ "0|0|
S40S8S129S46SfS170R1PbbA2A1Lu;S128Sb3Vx;A1A1A2S6A3").
Proof. destruct x; vm_compute; reflexivity. Qed.

Definition segs_inside (sgs : list Segment) (lo hi : Z) : bool := ltac2:(tb__ "0|1|
SedS172S172S10S5eVlo;S5fS173R1A1A1M0A2S5eS56G0S5fS174R1A1A1A2Vhi;A2A2Lseg;Vsgs;A3").
Lemma segs_inside_P : ltac2:(tb__ "0|0|
S40S8Sb9S48S68S61A1S67S61A1A3S6A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ro_addr_outside_image : ltac2:(tb__ "0|2|
S6fQ40M0A1S42S41S55S68S61A1S71G0R1A2M1A2S57G1S67S61A1A2A2A1S40S8S3cS48R2A2SaA3F_;Fx;").
Proof.
  intros x Hx. apply ro_addr_false_of_no_segment.
  destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  destruct (find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
  pose proof segs_inside_P as SI. unfold segs_inside in SI. rewrite forallb_forall in SI. specialize (SI seg Hin).
  apply andb_prop in SI as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. lia.
Qed.

Definition grant_ok (ia : instA) (a : Z) : Prop := ltac2:(tb__ "0|7|
S41S40S47S5aVa;Z1000A2Z0M0A3S41S57G0Va;A2S41S55S56Va;SdfVia;A1A2M1S62SeaVia;A1A1A2S5S6fQ40M2A1M3G3A2M4SecG4R1SbG4Sb1Se4Via;A1M5A1Sb0G5A1A3A3S47S41S55S71G2ScG3G3R3A3A2M6R1A2S57R1S56G6S71G2SeG3G3R3A3A2A2A2A2S42S41S55Va;R2A2S57R2G1A2A2A1F_;Fy;F_;Fe;A2A2A2").

Lemma disjoint_of_pointwise lo hi a n : ltac2:(tb__ "0|1|
S47S41S55Vlo;R1A2S57R1Vhi;A2A2S42S41S55Va;R2A2S57R2S56Va;Vn;A2M0A2A2A1F_;Fy;S3bS1S47S47Vlo;Vhi;A4S1S47S47Va;G0A4A2F_;").
Proof.
  intros H. unfold SymState.ranges_disjoint. cbn [fst snd].
  destruct (Z_lt_dec lo hi); [|lia]. destruct (Z_lt_dec a (a + n)); [|lia].
  destruct (Z_le_dec hi a); [lia|]. destruct (Z_le_dec (a + n) lo); [lia|]. exfalso.
  apply (H (Z.max lo a)); lia.
Qed.
Lemma dsM23_checks x : ltac2:(tb__ "0|0|
S40S8SedSdcSdcS10S10S132Sf3Se6R1A1A2S184R1A1A2S183S16cVx;A1S16bVx;A1R1A3A2Ld;Sb6Vx;A1A3S6A3").
Proof. destruct x; reflexivity. Qed.

Section K.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S169S48VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HVI : vm_insensitive Kc.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let L : layout := ia_L ia. Let vm : VmMaps := ia_vm ia. Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia.
Variables (cur : astate) (mWc : word -> option byte).
Hypothesis HLV : ltac2:(tb__ "0|0|
SdeVia;Vcur;VL;VmWc;Vvm;A5").
Let K := K_ia Kc ia.
Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|0|
S41S55S16cVx;A1Vsc;A2S55Vsc;S16bVx;A1A2A2").
Variable Q : assn.
Hypothesis HkK : 2 ^ 23 <= kB.
Hypothesis CONT_F : ltac2:(tb__ "0|0|
VRF;S28Sf1SddVia;VmWc;A2R1A2VTR;VkB;Sf0S48VK;S13cSb3Vx;A1A1R2A4VQ;A3F_;Frho';F_;").
Hypothesis CONT_T : ltac2:(tb__ "0|2|
VGF;S47S28Sb8Via;R2A2Sf1SddSe0Via;R3A2S175VmWc;S63R3A1S125S63SdfVia;A1A1M0A1A3A2R2A2S40S6fQ40A1S1eR3S23Sb3Vx;A1M1A1A2S63R4A1A3VTR;S5cVkB;S58Z2Z17A2A2Sf0S48Sb5VKc;S126Vvm;G0S63R5A1A3A2S128G1A1R4A4VQ;A3F_;F_;F_;FrhoT;Fza;F_;").

Lemma len_facts : ltac2:(tb__ "0|4|
S41S41S55Z1000M0SdfVia;A1M1A2S55G1S58Z2Z17A2A2A2S41S40S47S5aG1G0A2Z0A3S41S40S47S71Q40M2S63G1A1M3A2G1A3S41S40S47S127G3A1G1A3S40S47S71G2S125G3A1A2G1A3A2A2A2A2").
Proof using Hi.
  pose proof (ineeded_facts ia Hi) as [R1 R2].
  assert (U : bv_unsigned (wz (ineeded ia)) = ineeded ia) by (unfold wz; apply u64; lia).
  assert (N : mmap_nZ (wz (ineeded ia)) = ineeded ia).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite U. Z.to_euclidean_division_equations; lia. }
  split; [lia|]. split; [lia|]. split; [exact U|]. split; [exact N|].
  unfold mmap_n. rewrite N. unfold wz in U. exact U.
Qed.

Theorem gen_K : ltac2:(tb__ "0|0|
VTR;VkB;S181S48VK;SddVia;VmWc;A2S13aVx;A1A4VQ;A3").
Proof using CONT_F CONT_T HLV HVI Hi HkB HkK Hx RR.
  pose proof (iok_sc ia Hi) as SC. pose proof len_facts as (LR & LA & LU & LN & LM).
  pose proof (EK_shape x) as (Mecall & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mlen & M11v).
  (apply (trr_ex RR); [lia|]). intros rhoB. (apply (trr_inh RR); [lia|]). intros w0 [Hag _]. clear w0.
  apply (trr_pre RR (SymSoundR.SP segsU K (SK x) rhoB)); [intros w [_ HSP0]; rewrite <- SK_eq; exact HSP0|].
  apply ((trr_run RR) kB 500%nat CUTS_K K (SK x) [mkLeaf (EK x) RsCut] rhoB Q HkB (runK x) Mlen (K_ia_impl Kc ia)).
  intros Lf rho1 [<-|[]] Hab. cbn [lf_state].
  assert (Hag1 : agrees (rho2 ia mWc) rho1) by (eapply agrees_below; [exact Hag | exact Hab | rewrite <- SK_eq; cbv; discriminate]).
  clear Hab.

  assert (Elen : eval rho1 (reg_sv (EK x) 11) = wz (ineeded ia)).
  { rewrite M11. cbn [eval]. rewrite (proj1 Hag1 177%positive eq_refl). reflexivity. }

  destruct (EK_objs x) as [stkc EO].
  pose proof HLV as [LMI LXr Lhd Lkey Lraw Lro Lgd Lma Lkept Lblk Ltop].
  assert (DSd : forall d, In d (dsM23 x) -> DS2 ia d).
  { intros d Hd. pose proof (proj1 (forallb_forall _ _) (dsM23_checks x) d Hd) as C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
    split; [exact C1|]. split; [| exact (dcond2b_sound _ _ _ d Hx C3)].
    apply forallb_forall. intros [[off w] e] Hc. unfold od2_semb in C2. pose proof (proj1 (forallb_forall _ _) C2 e (dcells2_svs sc d off w e Hc)) as Y.
    unfold sv_sem in Y. apply andb_prop in Y as [_ Y]. exact Y. }

  destruct (key_area (m :: ia_X ia) (ia_R ia) (ia_U ia) cur (mig_I LMI) m Lkey) as (ar & k & Har & Hk & Em).
  assert (Hmr : addr_of L ar <= zA ia m /\ zA ia m + 40 <= addr_of L ar + PGSZ).
  { unfold m in *. rewrite <- Lma. rewrite Em. unfold addr_of, loc_addr. destruct ar; cbn [padd prid poff]. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }
  destruct (proj1 (proj2 (proj2 (proj2 (mig_vm LMI)))) ar PGSZ (e_area_In cur ar Har)) as (em & Hem & Em1 & Em2). cbn [ma_L] in Em1, Em2.
  pose proof (mig_img LMI) as HIR.

  change (TR kB (SPJ segsU (liftK K) (EK x) rho1) Q).
  apply ((trr_mmap_rw RR) kB kB (kB - 2 ^ 23) (liftK K) (liftK K)
           (fun a => liftK (fun tr md => K_v Kc (mmap_rw_vm vm (wz (ineeded ia)) a) tr md /\ grant_ok ia (bv_unsigned a)))
           (EK x) rho1 Q (fun rho tr md HK => proj1 HK) Mecall M17);
    [ | | | clear - HkK; lia | rewrite Elen, LN; clear - HkK LR; lia | rewrite Elen, LN; clear - LR; lia ].
  - intros tr ms md Hsp [HKc Hvm].
    pose proof (pending_args segsU rho1 (EK x) tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    rewrite M10 in G0. rewrite Elen in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5.
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite LU in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].
    split; [split; [exact HKc | exact Hvm]|].
    intros a Hpl. pose proof Hpl as (Hal & Hpos & Hceil & Hfree & _). rewrite G1, LN in Hceil. rewrite G1 in Hfree |- *. rewrite Hvm in Hfree.

    assert (Hceil' : bv_unsigned a + ineeded ia <= topL L).
    { rewrite (vm_ok_top L cur vm (mig_vm LMI)). replace vm with (m_vmmaps md) by exact Hvm. exact Hceil. }
    clear Hceil. rename Hceil' into Hceil.
    assert (FREE : forall e, In e (vm_reserved vm ++ vm_maps vm) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + ineeded ia)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite LM in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (IMG : forall y, mc_img_lo C_U <= y < mc_img_hi C_U -> ~ (bv_unsigned a <= y < bv_unsigned a + ineeded ia)).
    { intros y Hy. destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    assert (META : forall y, zA ia m <= y < zA ia m + 40 -> ~ (bv_unsigned a <= y < bv_unsigned a + ineeded ia)).
    { intros y Hy. refine (FREE em ltac:(apply in_app_iff; right; exact Hem) y _). unfold PGSZ in *. lia. }
    split.
    +
      intros o Ho. rewrite EO in Ho. rewrite LN. destruct Ho as [<-|Ho].
      *
        pose proof (smatch_pending_mem segsU _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segsU _ _ _ _ _ Hsp) as Hfacts.
        cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts. rewrite EO in Hall.
        assert (HF3 : Forall (SymState.holds rho1) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)).
        { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hfacts).
          apply (facts_incl_sound ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D ++ F_J)); [exact (EK_facts x)|]. rewrite app_assoc. apply in_app_iff. left. exact Hp. }
        pose proof (window_facts segsU rho1 ms AS_D (mkObj (SVar 10) (SVar 15) (SLit 0) stkc DUnknown) ltac:(unfold AS_D; lia) HF3 eq_refl eq_refl (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

        assert (TOPW : topL L <= bv_unsigned (rw rho1 10%positive) + toS 64 (bv_unsigned (rw rho1 15%positive))).
        { rewrite (proj1 Hag1 10%positive eq_refl), (proj1 Hag1 15%positive eq_refl). exact (iok_sp_high ia Hi). }
        unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite WS, soff_lit_small by lia.
        unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      * apply in_map_iff in Ho as (d & <- & Hd).
        rewrite (rngD ia Hi mWc d rho1 (DSd d Hd) Hag1).
        apply disjoint_of_pointwise. intros y Hy. pose proof (m_R ia Hi) as MR. top_ranges.
        unfold dlo2, dhi2, od2_range, od2_rangeP in Hy.
        destruct d; cbn [fst snd mc_tp C_U] in Hy; try (apply IMG; cbn [mc_img_lo mc_img_hi C_U]; unfold sc in *; lia).
        apply META. unfold m. lia.
    + split.
      * intros y Hy. apply ro_addr_outside_image. intros Himg. rewrite LN in Hy. exact (IMG (bv_unsigned y) Himg Hy).
      *
        cbn [liftK]. split; [split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) | change (m_vmmaps (with_vmmaps ?h' md)) with h'; rewrite Hvm; reflexivity]|].
        split; [exact Hal|]. split; [exact Hpos|]. split; [exact Hceil | exact FREE].
  -
    intros HRF. change (TR kB (SymSoundR.SP segsU K (mkSKF (EK x)) rho1) Q). exact (CONT_F HRF rho1 Hag1).
  -
    intros HGF a. rewrite Elen.
    (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm [HKv Hgr]]. cbn [w_tr w_cfg cfg_model] in HKv, Hgr.
    set (rhoA := rho_after_zero rho1 (ss_next (EK x)) a a (mmap_n (wz (ineeded ia)))).
    set (rhoT := rho_set_rw rhoA 187%positive a).
    exists (SymSoundR.SP segsU (K_v Kc (mmap_rw_vm vm (wz (ineeded ia)) a)) (S_ret_fresh (EK x)) rhoT). split.
    + split; [|exact HKv].
      apply (smatch_agree_vars segsU (fun u => negb (Pos.eqb u 187)) rhoA rhoT); [| intros l; reflexivity | reflexivity | exact (EK_no187 x) | exact Hsm].
      intros u Hu. unfold rhoT, rho_set_rw. cbn [rw]. destruct (Pos.eqb u 187) eqn:E187; [discriminate Hu | reflexivity].
    + rewrite <- (Z_to_bv_bv_unsigned 64 a) at 1. change (Z_to_bv 64 (bv_unsigned a)) with (wz (bv_unsigned a)).
      apply (CONT_T HGF (bv_unsigned a) rhoT Hgr).
      2:{ unfold rhoT, rhoA, rho_after_zero, rho_set_rw, set_rm. cbn [rw].
          replace (Pos.eqb (ss_next (EK x)) 187) with false by (destruct x; reflexivity). rewrite Pos.eqb_refl. unfold wz. rewrite Z_to_bv_bv_unsigned. reflexivity. }

      destruct Hag1 as (AW & AL & AM).
      split; [|split].
      * intros u Hu. unfold rhoT, rhoA, rho_after_zero, rho_set_rw, set_rm. cbn [rw].
        destruct (Pos.eqb_spec u 187) as [->|N187].
        { cbn [rho2 rw]. unfold rw2. cbn [rw2v]. unfold wz. rewrite <- (Z_to_bv_bv_unsigned 64 a) at 1. f_equal.
          symmetry. apply Z.mod_small. apply urange. }
        destruct (Pos.eqb_spec u (ss_next (EK x))) as [->|Nnx].
        { exfalso. revert Hu. destruct x; vm_compute; discriminate. }
        rewrite (AW u Hu). cbn [rho2 rw]. unfold rw2, rw2v.
        destruct (Z.eqb_spec (Z.pos u) 187) as [E|_]; [exfalso; apply N187; lia | reflexivity].
      * intros l. unfold rhoT, rhoA, rho_after_zero, rho_set_rw, set_rm. cbn [rl]. rewrite (AL l). reflexivity.
      * unfold rhoT, rhoA, rho_after_zero, rho_set_rw, set_rm. cbn [rm]. rewrite AM. unfold wz. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
End K.
End Mal_agrp_K.

Module Mal_agrp_A.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAMT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_runsR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G10.Mal_aslot_G OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma got_wseg k : ltac2:(tb__ "0|0|
S41S55Z0Vk;A2S57Vk;Z8A2A2S40S8S166S48S70Q40S56Z28d50Vk;A2A2A2S6A3F_;").
Proof.
  intros Hk. exact (forall_range_dec (fun k => wseg_addr segsU (Z_to_bv 64 (0x28d50 + k))) 0 8 ltac:(vm_compute; reflexivity) k ltac:(cbn; lia)).
Qed.
Lemma ctx_wseg k : ltac2:(tb__ "0|0|
S41S55Z0Vk;A2S57Vk;S111A2A2S40S8S166S48S70Q40S56Z5a3d0Vk;A2A2A2S6A3F_;").
Proof.
  intros Hk. exact (forall_range_dec (fun k => wseg_addr segsU (Z_to_bv 64 (0x5a3d0 + k))) 0 928 ltac:(vm_compute; reflexivity) k ltac:(unfold CTX_SIZE in Hk; cbn; lia)).
Qed.

Lemma ro_tabs_P : ltac2:(tb__ "0|0|
S47S41S55Z0R1A2S57R1Za0A2A2S40S8S3cS48S70Q40S56Z108ccR2A2A2A2S6A3F_;Fkk;").
Proof.
  intros kk Hk. exact (forall_range_dec (fun kk => ro_addr segsU (Z_to_bv 64 (0x108cc + kk))) 0 160 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
Qed.

Lemma holds_rd (rd : word -> option byte) a w v k : ltac2:(tb__ "0|3|
S66S65Vrd;S6fQ40M0A1S6L_;A2Va;Vw;Vv;A4SebVk;Vw;A2S40S3S6fQ8M1A1M2A1Vrd;S70G0S56Va;S59Vk;A1A2A2A1S7G2S70G1S10fVv;Vw;Vk;A3A2A2A3F_;F_;").
Proof.
  intros H Hk. specialize (H k Hk). unfold byteview_of in H.
  destruct ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64) && true)%bool; [|discriminate].
  destruct (rd (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate]. injection H as E. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- E. symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range 8 b). exact H.
Qed.

Lemma bv_rd (rd : word -> option byte) (wok : word -> bool) x v : ltac2:(tb__ "0|3|
S40S3S47A1S65Vrd;Vwok;Vx;A3S7S47Vv;A2A3S41S40S3S6fQ8M0A1M1A1Vrd;S70Q40Vx;A2M2A1S7G1S70G0Vv;A2A2A3S40S8Vwok;G2A1S6A3A2F_;").
Proof.
  intros H. unfold byteview_of in H.
  destruct ((0 <=? x) && (x <? 2 ^ 64))%bool; [|discriminate]. cbn [andb] in H.
  destruct (wok (Z_to_bv 64 x)); [|discriminate].
  destruct (rd (Z_to_bv 64 x)) as [b|]; [|discriminate]. injection H as <-. split; [|reflexivity]. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma am_reads_holds (m : word -> option byte) a w v : ltac2:(tb__ "0|0|
S55Z0Va;A2S55S56Va;S59Vw;A1A2S58Z2Z40A2A2S7aS48Vm;Va;Vw;Vv;A5S66S65SbaS48Vm;A2S6fQ40A1S6L_;A2Va;Vw;Vv;A4F_;F_;F_;").
Proof.
  intros Ha Hw H k Hk. specialize (H k Hk). unfold byteview_of.
  replace ((0 <=? a + Z.of_nat k) && (a + Z.of_nat k <? 2 ^ 64) && true)%bool with true
    by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold wz in H. rewrite H. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma auxv_ok_of_init Ly r : ltac2:(tb__ "0|1|
S75S48S61VLy;Vr;A4S55S56S62VLy;A1Z8A2S71Q40M0S1eVr;PaA2A2A2S6cS61VLy;S65SbaS48S1cVr;A1A2S6fG0A1S6L_;A2A3F_;F_;").
Proof.
  intros (av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & DJ & A13) Hsp.
  pose proof (topL_range Ly) as TR.
  exists av, q, 8. unfold mc_auxv in *.
  split; [apply am_reads_holds; [cbn; lia | cbn; lia | exact R1]|].
  split; [apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact (R2 8%nat ltac:(lia))]|].
  split; [replace (av + 16 * 8 + 8) with (av + 136) by lia; apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact R4]|].
  split; [apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  split.
  { intros i Hi. destruct (R3 (Z.to_nat i) ltac:(lia)) as [v Rv]. rewrite Z2Nat.id in Rv by lia.
    exists (nth (Z.to_nat i) am_auxv_keys 0), v.
    pose proof (R2 (Z.to_nat i) ltac:(lia)) as Rk. rewrite Z2Nat.id in Rk by lia.
    destruct (auxv_keys_early (Z.to_nat i) ltac:(lia)) as [K0 K25]. change auxv_keys with am_auxv_keys in K0, K25.
    split; [apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact Rk]|].
    split; [exact K0|]. split; [apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact Rv]|].
    intros E. exfalso. exact (K25 E). }
  split.
  { exists 9. split; [lia|]. split; [apply am_reads_holds; [lia | change (Z.of_nat 8) with 8; lia | exact (R2 9%nat ltac:(lia))]|].
    intros i Hi. lia. }
  lia.
Qed.

Lemma toS64_add_small u c : ltac2:(tb__ "0|6|
S41S55Z0M0Vu;A2S57Vu;S58Z2M1Z40M2A2M3A2A2S41S55G0Vc;A2S57Vc;S58G1Z3fA2M4A2A2S57S56Sc4G2Vu;A2Vc;A2M5G4A2S40S47Sc4G2S5aS56Vu;Vc;A2G3A2A2G5A3F_;F_;F_;").
Proof.
  intros U C H. unfold toS in *. rewrite (Z.mod_small u) in H |- * by lia. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  rewrite Z.mod_mod by lia.
  destruct (u <? 2 ^ 63) eqn:C1; [apply Z.ltb_lt in C1|apply Z.ltb_ge in C1].
  - rewrite (Z.mod_small (u + c)) by lia. destruct (u + c <? 2 ^ 63) eqn:C2; [apply Z.ltb_lt in C2|apply Z.ltb_ge in C2]; lia.
  - assert (Hc : u + c < 2 ^ 64 \/ 2 ^ 64 <= u + c) by lia. destruct Hc as [Hc|Hc].
    + rewrite (Z.mod_small (u + c)) by lia. destruct (u + c <? 2 ^ 63) eqn:C2; [apply Z.ltb_lt in C2|apply Z.ltb_ge in C2]; lia.
    + replace ((u + c) mod 2 ^ 64) with (u + c - 2 ^ 64).
      2:{ symmetry. replace (u + c) with ((u + c - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      destruct (u + c - 2 ^ 64 <? 2 ^ 63) eqn:C2; [apply Z.ltb_lt in C2|apply Z.ltb_ge in C2]; lia.
Qed.

Lemma imp_VRES : ltac2:(tb__ "0|0|
S40S12S10cS130S8eS49Sd4S72A1P12cA4SbdA2S11P136A1A3").
Proof. vm_cast_no_check (@eq_refl sv (SVar 310)). Qed.

Definition contA_frame (rho0 rhoK : valuation) : Prop := ltac2:(tb__ "0|b|
S41S46S16fR1P12cA2S40S6fQ40M0A1S1eVrhoK;R2A2S1eVrho0;R2A2A3F_;Fj;S41S40S4S6fQ8M1A1M2A1M3S2bVrhoK;P1M4A2S105S47G2S70G1A1S6aA4A3S41S46S42S40S46R1G4A3A1S40G3S2bVrhoK;R2A2S2bVrho0;R2A2A3F_;Fl;S41S47S41S55Z0R1A2S57R1Za0A2A2S40S3G2A1M5S1cVrhoK;S70G0S56Z108ccR2A2A2A2S9G2A1A3F_;Fkk;S41SdSebR1U8M6A2M7S40G5SbaS48S1cVrhoK;A1M8S70G0S56S6eS61A1S59R2A1M9A2A2A3S7G2S70G1S10fS64S61A1MaG6R2A3A2A2A3F_;Fk;SdG7S40G5SbaS48G8S70G0S56GaG9A2A2A3S7G2S70G1S10fS71G0S1eVrho0;PaeA2A2G6R2A3A2A2A3F_;Fk;A2A2A2A2A2").

Definition contA_pure (rho0 : valuation) : Prop := ltac2:(tb__ "0|2|
S71Q40M0S1eVrho0;PcA2A2S47S71G0S1eVrho0;PdA2A2S47S41S41S55Z0M1R2A2S57R2Z30A2A2S41S55G1R1A2S41S55S56R1S83A2S84R2A1A2S41S55Sc4Z40S71G0S1eVrho0;Sc1A2A2A2S5dS7bS59S7dR2A1A1A1A1A2S41Sc3S61Vrho0;A2S40S6fG0A1S1eVrho0;PadA2S70G0S64S61A1A2A3A2A2A2A2A2Treq;Tsc;").

Definition contA_null (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 : valuation) : jpred := ltac2:(tb__ "0|3|
S28S4SadA1SaeS41S178Vrho0;R3A2S41VKc;R2R1A2S41S17bVrho0;A1S43S102S102S41S74S48S61VX;S9S5S7eS47A2A1VU;R1R4R2A8S41Sd6VX;VX;VA;R1A4S41S40S3S7eA1M0S110S101R1A1S71Q40S1eVrho0;PcA2A2A2S9S7eA1M1A3S41SbcS48S61VA;R1S1cVrho0;A1S1cR4A1A6S43S4S5S82S47A2A1M2G2S112S5G0S7fA2S81S101VA;A1A1R1S1G0S7fG1S101R2A1A4A4Lktr;A2A2A2A2A2LA1;A2A2A2A2LmdK;LtrK;LrhoK;").

Definition contA_ok (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) (rho0 : valuation) : jpred := ltac2:(tb__ "0|5|
S28S4SadA1SaeS41S178Vrho0;R3A2S41VKc;R2R1A2S41S17bVrho0;A1S43S102S102S43S7eS7eS41S40S47S6bS103R2A1R1A2S71Q40M0S1eR5P136A2A2A3S41S74S48S61S0S7eR1VX;A3M1S9S5S7eS47A2A1VU;R2R5R3A8S41Sd6VX;G1VA;R2A4S41S40S8S117R1VX;A2SaA3S41SecS7eR1S115S101R2A1M2A1A3S41S40S3S7eA1M3S110G2S71G0S1eVrho0;PcA2A2A2S9S7eA1A3S41SbcS48S61VA;R2S1cVrho0;A1S1cR5A1A6S43S4S5S82S47A2A1M4G4S112S5G3S7fA2S81S101VA;A1A1R1S1G3S7fS7S7eR2A2S101R3A1A4A4Lktr;A2A2A2A2A2A2A2A2Lm;A2LA1;A2A2A2A2LmdK;LtrK;LrhoK;").

Section A.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (L : layout) (Kc : list event -> Model -> Prop).
Variables (rho : valuation) (tr : list event) (ms : machine_state) (md : Model).
Let A : MA := mkMA s L.
Let sc : Z := bv_unsigned (rw rho 12%positive).
Let req : Z := bv_unsigned (rw rho 13%positive).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S25S48Vrho;S9aS1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4").
Hypothesis HJ : ltac2:(tb__ "0|0|
S76S48S61VX;VU;VA;VKc;Vrho;Vtr;Vmd;A9").
Hypothesis Hhd : ltac2:(tb__ "0|0|
S40S3S7eA1S110Vs;Vsc;A2S9S7eA1A3").
Hypothesis E173 : ltac2:(tb__ "0|1|
S40S6fQ40M0A1S1eVrho;PadA2S70G0S64S61A1A2A3").

Lemma A_MI : ltac2:(tb__ "0|0|
S74S48S61VX;S9S5S7eS47A2A1VU;VA;Vrho;Vmd;A8"). Proof using HJ. exact (proj1 HJ). Qed.
Lemma A_MI' : ltac2:(tb__ "0|1|
S168S61VX;S9S5S7eS47A2A1VU;S104Vs;VL;A2SbaS48S1cVrho;A1M0A2SbbS48G0A2SafVmd;A1A8").
Proof using HJ. exact A_MI. Qed.
Lemma A_xraw : xraw X s. Proof using HJ. exact (proj1 (proj2 HJ)). Qed.
Lemma A_Kc : Kc tr md. Proof using HJ. exact (proj1 (proj2 (proj2 HJ))). Qed.
Lemma A_sc : 0 <= sc < 48. Proof using HJ. exact (proj1 (proj1 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma A_tp : tp_ok C_U rho. Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma A_init : ltac2:(tb__ "0|1|
S40S8S80Vs;A1SaA3S41S75S48S61VL;Vrho;A4S40S4S5S7eS85A2M0A1S86Vs;A1S2G0A1A3A2F_;").
Proof using HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))). Qed.

Lemma A_top : top_high A rho.
Proof using HJ. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))). Qed.
Lemma A_pure : contA_pure rho.
Proof using E173 HJ.
  pose proof HJ as (_ & _ & _ & (B1 & B2 & B3 & B4) & Htp & _). unfold contA_pure. cbn zeta.
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact Htp | exact E173].
Qed.
Lemma A_ctx : ly_ctx L = 0x5a3d0. Proof using HJ. exact (mig_ctx A_MI'). Qed.
Lemma ctx_ownedA off : ltac2:(tb__ "0|0|
S41S55Z0Voff;A2S57Voff;S111A2A2S113VL;Vs;S56S116VL;A1Voff;A2A3F_;").
Proof using HJ req sc.
  intros Ho. pose proof (mig_I A_MI') as HI. pose proof (mig_layout A_MI') as HL. pose proof (mig_vm A_MI') as HV. pose proof (mig_ledger A_MI') as HLG.
  cbn [ma_s ma_L] in HI, HL, HV, HLG. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. lia.
  - intros (b & Hb & Hx). cbn [fst snd] in Hx.
    destruct (user_block_in_group X None U s L HI A_xraw b Hb) as (g & am & i & fr & Hg & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    destruct (group_range X None U s L HI HL C_U (m_vmmaps md) g am Hg HV HLG) as (_ & _ & _ & D).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hg)) as Sp. assert (0 <= stride_of am * i) by nia.
    rewrite Eb in Hx, B1, B2. cbn [fst snd] in Hx, B1, B2. unfold addr_of in *. unfold UNIT, IB, CTX_SIZE in *. lia.
Qed.

Definition RP : list sobj := ltac2:(tb__ "0|0|
S0S19S9dS0S19S9eS0S19S9cS2S19A1A3A3A3").
Definition SGr : sstate := ltac2:(tb__ "0|0|
S21S2cS9aA1S33S9aA1S31S9aA1S30S9aA1S34S9aA1S0S19S9bS2S19A1A3S27S9aA1S16eSaA9").
Lemma SGr_swf : swf SGr = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Definition mR : word -> option byte := ltac2:(tb__ "0|0|
S180Vrho;Sc9Vms;A3").
Definition rhoR : valuation := ltac2:(tb__ "0|0|
S3eS1eVrho;A1S2bVrho;A1Sc7A3").

Lemma release_R : ltac2:(tb__ "0|4|
S41S25S48ScaSccS1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4S41S6fQ40A1M0S42S10aVrho;Sc9R1A3M1A1S40S3S6fQ8A1A1M2Sc7R2A1M3S1cVrho;R2A2A3F_;Fa;S41G0G1S40G2G3S164Vms;R2A2A3F_;Fa;S106S19S39S48Vrho;Vms;A3Sc9A3A2A2A2").
Proof using Hsm. exact (smatch_release_suffix segsU rho SG tr ms md [oStkG] RP NXA Hsm eq_refl SGr_swf). Qed.

Lemma rng_got : ltac2:(tb__ "0|1|
S40S5S47S47A2S22Vrho;S9dA2S1S47S47Z28d50M0S56G0Z8A2A4A3").
Proof using . unfold obj_range, obj_lo_of, obj_hi_of, oGot. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.
Lemma rng_guard : ltac2:(tb__ "0|1|
S40S5S47S47A2S22Vrho;S9eA2S1S47S47S64S61A1M0S56G0Z8A2A4A3").
Proof using E173. unfold obj_range, obj_lo_of, obj_hi_of, oGuard. cbn [ob_base ob_lo ob_hi eval]. rewrite E173, !soff_lit_small, u64 by (cbn; lia). reflexivity. Qed.
Lemma rng_act0 : ltac2:(tb__ "0|2|
S40S5S47S47A2S22Vrho;S9cA2S1S47S47S56Z5a3c8M0S56Z58S5bZ8Vsc;A2M1A2A2S56G0S56Z60G1A2A2A4A3").
Proof using HJ.
  pose proof A_sc as SC. unfold obj_range, obj_lo_of, obj_hi_of, oAct0. cbn [ob_base ob_lo ob_hi].
  rewrite !soff_zeval by reflexivity. cbn [zeval zalu eval]. unfold zr_of. fold sc. rewrite u64 by lia.
  rewrite (Z.mod_small sc) by lia. change ((3 mod 2 ^ 64) mod 64) with 3. change (88 mod 2 ^ 64) with 88. change (96 mod 2 ^ 64) with 96.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  rewrite !Z.mod_small by lia. rewrite !toS_small by lia. f_equal; lia.
Qed.

Definition inRP (a : Z) : Prop := ltac2:(tb__ "0|5|
S44S41S55Z28d50M0Va;A2S57Va;S56G0Z8M1A2A2A2S44S41S55S64S61A1M2Va;A2S57Va;S56G2G1A2A2A2S41S55S56Z5a3c8M3S56Z58S5bG1Vsc;A2M4A2A2Va;A2S57Va;S56G3S56Z60G4A2A2A2A2A2A2").
Lemma in_RP a : ltac2:(tb__ "0|0|
S41S55Z0Va;A2S57Va;S58Z2Z40A2A2A2S45S10aVrho;Sc9S70Q40Va;A2A3SceVa;A1A2F_;").
Proof using E173 HJ.
  intros Ha. unfold in_ranges, RP, inRP. rewrite u64 by lia. split.
  - intros (o & Ho & R0). destruct Ho as [<-|[<-|[<-|[]]]]; [rewrite rng_got in R0 | rewrite rng_guard in R0 | rewrite rng_act0 in R0]; cbn [fst snd] in R0; lia.
  - intros [H|[H|H]]; [exists oGot | exists oGuard | exists oAct0]; (split; [cbn; tauto|]); [rewrite rng_got | rewrite rng_guard | rewrite rng_act0]; cbn [fst snd]; lia.
Qed.

Lemma rd_of_CG m : ltac2:(tb__ "0|0|
S40S6fQ40A1S3S6fQ8A1A1F_;SbaS48Vm;A2S165S48Vm;A2A3"). Proof using . reflexivity. Qed.
Lemma wok_of_CG m : ltac2:(tb__ "0|0|
S40S6fQ40A1S8F_;SbbS48Vm;A2S167S48Vm;A2A3"). Proof using . reflexivity. Qed.
Lemma A_rom : rom_ok segsU ms. Proof using Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Lemma RP_got k : ltac2:(tb__ "0|3|
SebVk;U8M0A2S40S3S6fQ8M1A1M2A1S36Vms;S70Q40S56Z28d50S59Vk;A1A2A2A2S7G2S70G1S10fS64S61A1G0Vk;A3A2A2A3F_;").
Proof using E173 Hsm req sc.
  intros Hk. pose proof (proj2 (proj2 (proj2 release_R))) as HO. apply Forall_cons_iff in HO as [HG _].
  pose proof (cell_bytes_sym segsU rho ms oGot (mkCell (SLit 0) 8 (SVar 173)) k HG ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
  cbn [ob_base oGot c_off c_val c_width eval] in B. rewrite E173, soff_lit_small, !u64 in B by (cbn; lia).
  rewrite Z.add_0_r in B. rewrite B. f_equal. change (Z.to_nat 8) with 8%nat. rewrite nth_enc_bytes by (cbn; lia). reflexivity.
Qed.
Lemma RP_act k : ltac2:(tb__ "0|2|
SebVk;U8A2S40S3S6fQ8M0A1M1A1S36Vms;S70Q40S56S56Z5a3c8S56Z58S5bZ8Vsc;A2A2A2S59Vk;A1A2A2A2S7G1S70G0Z0A2A2A3F_;").
Proof using HJ Hsm req.
  intros Hk. pose proof (proj2 (proj2 (proj2 release_R))) as HO. pose proof A_sc as SC.
  apply Forall_cons_iff in HO as [_ HO]. apply Forall_cons_iff in HO as [_ HO]. apply Forall_cons_iff in HO as [HA _].
  pose proof (cell_bytes_sym segsU rho ms oAct0 (mkCell (SAlu ALU_ADD (SAlu ALU_SLL (SVar 12) (SLit 3)) (SLit 88)) 8 (SLit 0)) k HA ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
  cbn [ob_base oAct0 c_off c_val c_width] in B.
  rewrite soff_zeval in B by reflexivity. cbn [zeval zalu eval] in B. unfold zr_of in B. fold sc in B.
  rewrite (Z.mod_small sc) in B by lia. change ((3 mod 2 ^ 64) mod 64) with 3 in B. change (88 mod 2 ^ 64) with 88 in B.
  rewrite Z.shiftl_mul_pow2 in B by lia. change (2 ^ 3) with 8 in B. rewrite !Z.mod_small, toS_small, !u64 in B by lia.
  replace (369608 + (sc * 8 + 88) + Z.of_nat k) with (369608 + (88 + 8 * sc) + Z.of_nat k) in B by lia. rewrite B.
  f_equal. change (Z.to_nat 8) with 8%nat. rewrite nth_enc_bytes by (cbn; lia). unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma RP_guardv k : ltac2:(tb__ "0|4|
SebVk;U8M0A2S40S3S6fQ8M1A1M2A1S36Vms;S70Q40M3S56S64S61A1S59Vk;A1A2A2A2S7G2S70G1S10fS71G3S1eVrho;PaeA2A2G0Vk;A3A2A2A3F_;").
Proof using E173 Hsm.
  intros Hk. pose proof (proj2 (proj2 (proj2 release_R))) as HO. apply Forall_cons_iff in HO as [_ HO]. apply Forall_cons_iff in HO as [HG _].
  pose proof (cell_bytes_sym segsU rho ms oGuard (mkCell (SLit 0) 8 (SVar 174)) k HG ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
  cbn [ob_base oGuard c_off c_val c_width eval] in B. rewrite E173, soff_lit_small, !u64 in B by (cbn; lia). rewrite Z.add_0_r in B.
  rewrite B. f_equal. change (Z.to_nat 8) with 8%nat. rewrite <- (Z_to_bv_bv_unsigned 64 (rw rho 174%positive)). rewrite nth_enc_bytes by (pose proof (bv_unsigned_in_range 64 (rw rho 174%positive)); cbn in *; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma RP_guard k : ltac2:(tb__ "0|1|
SebVk;U8A2S43S6fQ8A1M0G0S40S3G0A1S36Vms;S70Q40S56S64S61A1S59Vk;A1A2A2A2S7G0R1A2A3Lb;A2F_;").
Proof using E173 Hsm req sc. intros Hk. eexists. exact (RP_guardv k Hk). Qed.

Lemma img_act k : ltac2:(tb__ "0|4|
SebVk;U8A2S41S40S3S6fQ8M0A1M1A1SbaS48S1cVrho;A1M2S70Q40S56S56Z5a3c8S56Z58S5bZ8Vsc;A2A2A2S59Vk;A1A2A2M3A3S7G1S70G0Z0A2A2A3S40S8SbbS48G2G3A3S6A3A2F_;").
Proof using HJ Hhd.
  intros Hk. pose proof A_sc as SC. pose proof (mig_reprO A_MI') as [[_ [HCI _]] _]. cbn [ma_s ma_L] in HCI.
  set (c := MCell (LCtx (CTX_active + 8 * Z.of_nat (Z.to_nat sc))) 8 (optr (nth (Z.to_nat sc) (st_active s) None))).
  assert (Hin : In c (image s)).
  { unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (Z.to_nat sc). split; [reflexivity|]. apply in_seq. lia. }
  pose proof (proj1 (Forall_forall _ _) HCI c Hin) as CH.
  change (nth (Z.to_nat sc) (st_active s) None) with (active_hd s sc) in c. subst c. rewrite Hhd in CH.
  unfold cell_holds in CH. cbn [mc_val mc_loc mc_w optr sval_num loc_addr] in CH. specialize (CH k Hk).
  rewrite A_ctx, Z2Nat.id in CH by lia. unfold CTX_active in CH.
  replace (369616 + (80 + 8 * sc) + Z.of_nat k) with (369608 + (88 + 8 * sc) + Z.of_nat k) in CH by lia.
  destruct (bv_rd _ _ _ _ CH) as [R1 W1]. split; [|exact W1]. rewrite R1. f_equal.
  unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma img_got k : ltac2:(tb__ "0|3|
SebVk;U8M0A2S40S3S6fQ8M1A1M2A1SbaS48S1cVrho;A1S70Q40S56Z28d50S59Vk;A1A2A2A3S7G2S70G1S10fS64S61A1G0Vk;A3A2A2A3F_;").
Proof using HJ.
  intros Hk. pose proof (mig_statics A_MI') as ST. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & (gd & S9 & _)).
  exact (holds_rd _ _ _ _ k S9 Hk).
Qed.

Definition inG (a : Z) : Prop := ltac2:(tb__ "0|1|
S41S55S64S61A1M0Va;A2S57Va;S56G0Z8A2A2A2").

Lemma wok_true_of_wseg (m : word -> option byte) x : ltac2:(tb__ "0|0|
S40S8S166S48Vx;A2S6A3S40S8SbbS48Vm;Vx;A3S6A3F_;").
Proof using . intros H. unfold Contract.wok_of. destruct (m x); [reflexivity | exact H]. Qed.

Lemma AG_R a : ltac2:(tb__ "0|2|
S41S55Z0Va;A2S57Va;S58Z2Z40A2A2A2S42ScdVa;A1A1S41S40S3S6fQ8A1A1SbaS48Sc7S70Q40Va;A2M0A3SbaS48S1cVrho;A1M1G0A3A3S40S8SbbS48Sc7G0A3SbbS48G1G0A3A3A2F_;F_;").
Proof using E173 HJ Hhd Hsm.
  intros Ha NG. pose proof release_R as (_ & OUT & IN & _). pose proof A_sc as SC.
  destruct (in_ranges_dec rho RP (Z_to_bv 64 a)) as [I0|O0].
  2:{ rewrite !rd_of_CG, !wok_of_CG. pose proof (OUT (Z_to_bv 64 a) O0) as E.
      split; [apply rd_of_mem; exact E | apply wok_of_mem; exact E]. }
  pose proof (IN (Z_to_bv 64 a) I0) as E. apply (in_RP a Ha) in I0.
  rewrite rd_of_CG, (rd_of_at segsU mR ms _ A_rom E).
  destruct I0 as [G|[G|G]]; [| exfalso; exact (NG G) |].
  -   assert (W : wseg_addr segsU (Z_to_bv 64 a) = true) by (replace a with (0x28d50 + (a - 0x28d50)) by lia; apply got_wseg; lia).
    rewrite !(wok_true_of_wseg _ _ W). split; [|reflexivity].
    set (k := Z.to_nat (a - 0x28d50)). assert (Hk : (k < 8)%nat) by (subst k; lia).
    assert (Ea : a = 0x28d50 + Z.of_nat k) by (subst k; lia). clearbody k. subst a.
    rewrite (RP_got k Hk), (img_got k Hk). reflexivity.
  -   assert (W : wseg_addr segsU (Z_to_bv 64 a) = true) by (replace a with (0x5a3d0 + (a - 0x5a3d0)) by lia; apply ctx_wseg; unfold CTX_SIZE; lia).
    rewrite (wok_true_of_wseg mR _ W).
    set (k := Z.to_nat (a - (0x5a3c8 + (88 + 8 * sc)))). assert (Hk : (k < 8)%nat) by (subst k; lia).
    assert (Ea : a = 0x5a3c8 + (88 + 8 * sc) + Z.of_nat k) by (subst k; lia). clearbody k. subst a.
    destruct (img_act k Hk) as [R1 W1]. rewrite (RP_act k Hk), R1, W1. split; reflexivity.
Qed.

Lemma RD_R a : ltac2:(tb__ "0|1|
ScdVa;A1S43S6fQ8A1M0G0S40S3G0A1SbaS48Sc7S70Q40Va;A2A3S7G0R1A2A3Lb;A2F_;").
Proof using E173 HJ Hsm.
  intros G. pose proof release_R as (_ & _ & IN & _). unfold inG in G.
  assert (Ha : 0 <= a < 2 ^ 64) by (cbn in G; lia).
  pose proof (IN (Z_to_bv 64 a) (proj2 (in_RP a Ha) (or_intror (or_introl G)))) as E.
  rewrite rd_of_CG, (rd_of_at segsU mR ms _ A_rom E).
  destruct (RP_guard (Z.to_nat (a - mc_chk_guard C_U)) ltac:(lia)) as [b Hb]. exists b.
  rewrite Z2Nat.id in Hb by lia. replace (mc_chk_guard C_U + (a - mc_chk_guard C_U)) with a in Hb by lia. exact Hb.
Qed.

Lemma MI_R : ltac2:(tb__ "0|0|
S168S61VX;S9S5S7eS47A2A1VU;S104Vs;VL;A2SbaS48Sc7A2SbbS48Sc7A2SafVmd;A1A8").
Proof using E173 HJ Hhd Hsm.
  unfold MInvI. apply (minvG_frame C_U X None U s L _ _ _ _ (m_vmmaps md) inG A_MI' A_xraw).
  - exact AG_R.
  - intros a Ha _. exact (RD_R a Ha).
  - intros a. unfold inG. lia.
  -
    intros a G (e & He & Hx). unfold inG in G. cbn [mc_chk_guard C_U] in G.
    destruct e as [l n]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s l n He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. rewrite A_ctx in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L s (m_vmmaps md) p n (mig_vm A_MI') (mig_ledger A_MI') He ltac:(lia)) as (_ & _ & G3).
      unfold addr_of in G3. cbn [mc_img_lo mc_img_hi C_U loc_addr] in G3, Hx. destruct p as [pr po]. cbn [loc_addr] in Hx. lia.
  - intros a G Hs. unfold inG, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in G, Hs. lia.
  - intros a G. unfold inG in G. cbn in G. top_ranges. lia.
  - exact RD_R.
Qed.

Lemma auxv_init_ext rho1 rho2 Ly : ltac2:(tb__ "0|5|
S55S71Q40M0S1eVrho2;PaM1A2A2S71G0S1eVrho1;G1A2A2M2A2S6fG0A1S55G2S71G0R1A2A2S40S3S6fQ8A1A1M3S1cVrho2;R2A2S1cVrho1;R2A2A3F_;Fa;S47S41S55Z0R1A2S57R1Z8A2A2S40G3S1cVrho2;S70G0S56S6dS61A1R2A2A2M4A2S1cVrho1;G4A2A3F_;Fk;S75S48S61VLy;Vrho1;A4S75S48S61VLy;Vrho2;A4F_;F_;F_;F_;").
Proof using req sc.
  intros E10 Ehi Eav (av & q & R1 & R2 & R3 & R4 & R5 & M1 & M2 & S1 & S2 & S3 & S4 & DJ & A13).
  unfold auxv_init. exists av, q.
  assert (RD : forall a w vv, (forall k, (k < w)%nat -> rm rho2 (wz (a + Z.of_nat k)) = rm rho1 (wz (a + Z.of_nat k))) ->
               am_reads segsU (rm rho1) a w vv -> am_reads segsU (rm rho2) a w vv).
  { intros a w vv E H k Hk. unfold Contract.rd_of in *. rewrite (E k Hk). exact (H k Hk). }
  assert (HI : forall a w vv, bv_unsigned (rw rho1 10%positive) <= a -> a + Z.of_nat w <= 2 ^ 64 -> am_reads segsU (rm rho1) a w vv -> am_reads segsU (rm rho2) a w vv).
  { intros a w vv Ha Hw. apply RD. intros k Hk. apply Ehi. unfold wz. rewrite u64 by (pose proof (bv_unsigned_in_range 64 (rw rho1 10%positive)); lia). lia. }
  top_ranges.
  split; [apply RD; [intros k Hk; unfold wz; apply Eav; lia | exact R1]|].
  split; [intros j Hj; apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact (R2 j Hj)]|].
  split; [intros j Hj; destruct (R3 j Hj) as [vv Hv]; exists vv; apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact Hv]|].
  split; [apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact R4]|].
  split; [apply HI; [lia | change (Z.of_nat 8) with 8; lia | exact R5]|].
  cbn zeta in *. repeat split; try assumption; lia.
Qed.

Let u10 : Z := bv_unsigned (rw rho 10%positive).
Let u15 : Z := bv_unsigned (rw rho 15%positive).
Lemma A_facts : ltac2:(tb__ "0|1|
S106S14S3dVrho;A1SbS14SbS14S0S14SbfS0S14Sc0S73A1S2S14A1M0A3A3SbeS73A1A3S0S14S17S11PcA1S13Z2fA1A2G0A3A3A3").
Proof using Hsm. exact (smatch_facts_hold segsU _ _ _ Hsm). Qed.
Lemma A_depth0 : ltac2:(tb__ "0|1|
S41S55Sc4Z40Vu15;A2M0S5dS73A1A2S55S5dS58Z2Z28A2A1G0A2A2").
Proof using Hsm req sc u10.
  pose proof A_facts as F.
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- AS_D)) (SVar V_DEPTH))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  assert (H2 : SymState.holds rho (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) F); cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. rewrite (holds_zholds rho) in H2 by reflexivity.
  cbn [zholds zcond zeval] in H1, H2. unfold V_DEPTH, zr_of in H1, H2. fold u15 in H1, H2.
  rewrite (toS_mod 64 u15) in H1, H2 by lia.
  replace (toS 64 ((- AS_D) mod 2 ^ 64)) with (- AS_D) in H1 by reflexivity.
  replace (toS 64 ((- 2 ^ 40) mod 2 ^ 64)) with (- 2 ^ 40) in H2 by reflexivity.
  apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1. apply Bool.negb_true_iff in H2. apply Z.ltb_ge in H2. lia.
Qed.
Lemma A_align : u10 mod 16 = 0.
Proof using Hsm. pose proof (proj1 (Forall_forall _ _) A_facts F_sp_aligned ltac:(left; reflexivity)) as H. cbn in H. exact (proj2 H). Qed.
Lemma A_stack_lo : ltac2:(tb__ "0|0|
S55Z0S56Vu10;Sc4Z40Vu15;A2A2A2").
Proof using Hsm req sc.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [ss_objs SG] in Hall.
  pose proof (proj1 (Forall_forall _ _) Hall oStkG ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, oStkG in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb. fold u10 u15 in Hb. lia.
Qed.
Lemma A_sp_lo_lit : ltac2:(tb__ "0|0|
S55Z7fff7f800000S56Vu10;Sc4Z40Vu15;A2A2A2").
Proof using Hsm req sc.
  pose proof A_depth0 as [D1 D2]. pose proof A_stack_lo as SL. pose proof (urange (rw rho 10%positive)) as U10. fold u10 in U10.
  pose proof (urange (rw rho 15%positive)) as U15. fold u15 in U15. unfold AS_D in D1.
  pose proof (proj1 (Forall_forall _ _) A_facts (F_sp_high AS_D) ltac:(right; left; reflexivity)) as H.
  rewrite (holds_zholds rho) in H by reflexivity. unfold F_sp_high in H. cbn [zholds zeval zalu] in H. unfold zr_of, V_DEPTH in H. fold u10 u15 in H.
  rewrite (Z.mod_small u10), (Z.mod_small u15) in H by lia.
  rewrite (Z.mod_small aceil_lo) in H by lia.
  assert (E : u15 = toS 64 u15 + 2 ^ 64).
  { unfold toS. rewrite Z.mod_small by lia. change (2 ^ (64 - 1)) with (2 ^ 63).
    destruct (u15 <? 2 ^ 63) eqn:C; [|lia]. apply Z.ltb_lt in C. exfalso. unfold toS in D1. rewrite Z.mod_small in D1 by lia.
    change (2 ^ (64 - 1)) with (2 ^ 63) in D1. rewrite (proj2 (Z.ltb_lt _ _) C) in D1. lia. }
  rewrite E in H. replace (u10 + (toS 64 u15 + 2 ^ 64)) with ((u10 + toS 64 u15) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. first [exact H | apply Z.leb_le in H; exact H].
Qed.
Lemma A_sp_high : ltac2:(tb__ "0|0|
S55S62VL;A1S56Vu10;Sc4Z40Vu15;A2A2A2").
Proof using HJ. pose proof A_top as H. unfold top_high, V_DEPTH in H. exact H. Qed.
Lemma A_sp : ltac2:(tb__ "0|0|
S41S55Z7fff7f800000Vu10;A2S41S55Z1000Vu10;A2S40S47S5aVu10;Z10A2Z0A3A2A2").
Proof using Hsm req sc u15. pose proof A_sp_lo_lit. pose proof A_depth0. pose proof A_align. unfold AS_D in *. lia. Qed.
Lemma A_sp_top : ltac2:(tb__ "0|0|
S55S62VL;A1Vu10;A2").
Proof using HJ Hsm req sc u15. pose proof A_sp_high. pose proof A_depth0. unfold AS_D in *. lia. Qed.

Lemma A_JR : ltac2:(tb__ "0|0|
S76S48S61VX;VU;VA;VKc;ScaVtr;Vmd;A9").
Proof using E173 HJ Hhd Hsm.
  pose proof HJ as (_ & HX & HK & Hb & Htp & Hinit & Htop).
  split; [exact MI_R|].
  split; [exact HX|]. split; [exact HK|]. split; [exact Hb|]. split; [exact Htp|].
  split; [|exact Htop].
  intros Hf. destruct (Hinit Hf) as [HA HM]. split; [|exact HM].
  apply (auxv_init_ext rho rhoR); [apply Z.le_refl| | |exact HA].
  - intros a Ha. unfold rhoR. cbn [rm]. apply (proj1 (proj2 release_R)). intros IN0.
    pose proof (proj1 (in_RP (bv_unsigned a) (bv_unsigned_in_range 64 a)) ltac:(rewrite Z_to_bv_bv_unsigned; exact IN0)) as I0.
    pose proof A_sp as (SP & _). pose proof A_sc. unfold inRP in I0. cbn [mc_chk_guard C_U] in I0. fold u10 in Ha. top_ranges. lia.
  - intros k Hk. unfold rhoR. cbn [rm]. apply (proj1 (proj2 release_R)). intros IN0.
    pose proof (proj1 (in_RP (mc_auxv C_U + k) ltac:(unfold mc_auxv; cbn [mc_libc C_U]; lia)) IN0) as I0. pose proof A_sc.
    unfold inRP, mc_auxv in I0. cbn [mc_chk_guard mc_libc C_U] in I0. lia.
Qed.

Definition rhoT : valuation := ltac2:(tb__ "0|1|
S17cScaP1S105S47S6fQ8M0A1S70G0A1S6aA4A3").
Lemma rhoT_rw j : ltac2:(tb__ "0|0|
S40S6fQ40A1S1eSc8Vj;A2S1eVrho;Vj;A2A3"). Proof using . reflexivity. Qed.
Lemma rhoT_rm : rm rhoT = mR. Proof using . reflexivity. Qed.
Lemma SGr_nolist1 : state_has_rl 1%positive SGr = false. Proof using . vm_compute. reflexivity. Qed.
Lemma smatch_SGr_T : ltac2:(tb__ "0|0|
S25S48Sc8SccS1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4").
Proof using Hsm. unfold rhoT. apply SymCall.smatch_set_rl; [apply SGr_nolist1 | exact (proj1 release_R)]. Qed.

Lemma sctab_imageT kk : ltac2:(tb__ "0|3|
S41S55Z0M0Vkk;A2S57Vkk;Z60A2A2S40S3S6fQ8M1A1M2A1S3aS48S70Q40S56Z108ecVkk;A2A2A2S7G2S107G2S60Vkk;A1S2bSc8P1A2S70G1G0A2A4A2A3F_;").
Proof using .
  intros Hk.
  pose proof (forall_range_dec (fun kk => match image_byte segsU (Z_to_bv 64 (0x108ec + kk)) with
                                         | Some b => bv_eqb b (nth (Z.to_nat kk) (map (Z_to_bv 8) size_classes_bytes) (Z_to_bv 8 0))
                                         | None => false end) 0 96 ltac:(vm_compute; reflexivity) kk ltac:(lia)) as H.
  cbn beta in H. unfold rhoT, rho_set_rl. cbn [rl]. rewrite Pos.eqb_refl.
  destruct (image_byte segsU (Z_to_bv 64 (67820 + kk))) as [b|]; [|discriminate].
  f_equal. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma rng_stk : ltac2:(tb__ "0|0|
S40S5S47S47A2S22Vrho;S9bA2S1S47S47S56Vu10;Sc4Z40Vu15;A2A2S56Vu10;Z0A2A4A3").
Proof using .
  unfold obj_range, obj_lo_of, obj_hi_of, oStkG. cbn [ob_base ob_lo ob_hi eval]. rewrite soff_lit_small by lia.
  unfold soff. rewrite bv_signed_toS by (cbn; lia). reflexivity.
Qed.

Lemma mR_rom kk : ltac2:(tb__ "0|1|
S41S55Z0Vkk;A2S57Vkk;Za0A2A2S40S3S6fQ8A1M0A1Sc7S70Q40S56Z108ccVkk;A2A2A1S9G0A1A3F_;").
Proof using E173 HJ Hsm.
  intros Hk. pose proof release_R as (_ & OUT & _).
  rewrite OUT.
  2:{ intros IN0. pose proof (proj1 (in_RP (0x108cc + kk) ltac:(lia)) IN0) as I0. pose proof A_sc. unfold inRP in I0. cbn [mc_chk_guard C_U] in I0. lia. }
  destruct Hsm as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr; [apply Hro; apply ro_tabs_P; exact Hk|].
  pose proof A_sp as (SP & _ & _). pose proof A_sc as SC. pose proof A_sp_high as SL. top_ranges.
  unfold SG. cbn [ss_objs]. unfold outside_all.
  rewrite u64 by lia.
  constructor; [rewrite rng_stk; cbn [fst snd]; lia|].
  constructor; [rewrite rng_got; cbn [fst snd]; lia|].
  constructor; [rewrite rng_guard; cbn [fst snd mc_chk_guard C_U]; lia|].
  constructor; [rewrite rng_act0; cbn [fst snd]; lia|]. constructor.
Qed.

Definition SGT' : sstate := ltac2:(tb__ "0|0|
S21S2cS9aA1S33S9aA1S31S9aA1S30S9aA1S34S9aA1S0S19S9bS0S19S162S2S19A1A3A3S27S9aA1S16eSaA9").
Lemma SGT'_swf : swf SGT' = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma smatch_SGT' : ltac2:(tb__ "0|0|
S25S48Sc8ScbS1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4").
Proof using E173 HJ Hsm.
  apply (smatch_extend_objs segsU rhoT SGr tr ms md [O_sct] NXA smatch_SGr_T SGT'_swf).
  - constructor; [|constructor]. rewrite rhoT_rm. unfold O_sct. apply obj_holds_frame_rom; try lia.
    + exact A_rom.
    + unfold rhoT, rho_set_rl. cbn [rl]. rewrite Pos.eqb_refl. reflexivity.
    + intros k Hk. split; [replace (67820 + k) with (0x108cc + (32 + k)) by lia; apply mR_rom; lia | apply sctab_imageT; exact Hk].
  - constructor; [|constructor]. unfold SGr. cbn [ss_objs]. constructor; [|constructor].
    unfold SymState.ranges_disjoint. replace (obj_range rhoT oStkG) with (obj_range rho oStkG) by reflexivity. rewrite rng_stk.
    unfold obj_range, obj_lo_of, obj_hi_of, O_sct. cbn [ob_base ob_lo ob_hi fst snd eval]. rewrite !soff_lit_small, u64 by lia.
    pose proof A_sp_high as SL. top_ranges. lia.
  - constructor; [constructor | constructor].
Qed.

Lemma sd_SGT : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108ScbS92A2S7G3S1G1G2S2G0A1S0S14S17S13Z1000A1S11PaA1A2S2S14A1A3A4A2A3").
Proof using . vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some ([], [SPUle (SLit 4096) (SVar 10)]))). Qed.
Lemma SGT_swf : swf SGT = true. Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma smatch_SGT : ltac2:(tb__ "0|0|
S25S48Sc8S92S1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4").
Proof using E173 HJ Hsm.
  apply (smatch_restate segsU rhoT SGT' SGT _ [] _ smatch_SGT' SGT_swf sd_SGT); [constructor|].
  constructor; [|constructor]. cbn [SymState.holds eval]. rewrite rhoT_rw, u64 by lia. pose proof A_sp as (_ & SP & _). exact SP.
Qed.
Lemma smatch_SGS : ltac2:(tb__ "0|0|
S25S48Sc8S90S1S4SadA1Sd1Vtr;Sd2Vms;Vmd;A2A4A4").
Proof using E173 HJ Hsm. exact (smatch_xforms segsU _ rhoT SGT SGS _ SGS_ok smatch_SGT). Qed.

Lemma segs_topU : segs_top segsU = 0x5b000. Proof using . vm_compute. reflexivity. Qed.
Lemma image_byte_none_high (a : word) : ltac2:(tb__ "0|1|
S55S17eS48A1S71Q40Va;A2A2S40S3S6fQ8A1M0A1S3aS48Va;A2S9G0A1A3F_;").
Proof using req sc u10 u15.
  intros Ha. unfold image_byte, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment segsU (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (find_segment_top segsU (bv_unsigned a) 1 seg ltac:(lia) E). lia.
Qed.

Section Call.
Variables (rho' : valuation) (ms1 : machine_state).
Hypothesis Hag : agree_below 300%positive rhoT rho'.
Hypothesis HsmC : ltac2:(tb__ "0|0|
S25S48Vrho';S8fS1S4SadA1Sd1Vtr;Sd2Vms1;Vmd;A2A4A4").
Definition rho1 : valuation := ltac2:(tb__ "0|0|
S10eS10dVrho';S8dVms1;A3S8eA2").

Lemma rm_rho' a : ltac2:(tb__ "0|0|
S40S3S6fQ8A1A1S1cVrho';Va;A2Sc7Va;A1A3"). Proof using Hag. symmetry. exact (proj2 (proj2 Hag) a). Qed.
Lemma rw_rho' j : ltac2:(tb__ "0|0|
S16fVj;P12cA2S40S6fQ40A1S1eVrho';Vj;A2S1eVrho;Vj;A2A3F_;"). Proof using Hag. intros Hj. symmetry. rewrite <- rhoT_rw. exact (proj1 Hag j Hj). Qed.
Lemma C_rom : rom_ok segsU ms1. Proof using HsmC. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmC))))). Qed.
Lemma C_ro : ro_clear segsU ms1. Proof using HsmC. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmC)))))). Qed.

Definition oFrm : sobj := nth 1 (ss_objs EvA) oStkG.
Lemma RcA_eq : ltac2:(tb__ "0|0|
S40S4S19A1S8dS0S19SaaS0S19S162S2S19A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma rng_frm : ltac2:(tb__ "0|0|
S40S5S47S47A2S22Vrho';SaaA2S1S47S47S56Vu10;N90A2S56Vu10;Z0A2A4A3").
Proof using Hag req sc u15.
  unfold obj_range, obj_lo_of, obj_hi_of, oFrm. cbn [nth ss_objs EvA ob_base ob_lo ob_hi eval].
  rewrite (rw_rho' 10) by (cbv; reflexivity). rewrite !soff_lit_small by lia. reflexivity.
Qed.
Lemma rng_sctC : ltac2:(tb__ "0|1|
S40S5S47S47A2S22Vrho';S162A2S1S47S47S56Z108ecM0Z0A2S56G0Z60A2A4A3").
Proof using req sc u10 u15. unfold obj_range, obj_lo_of, obj_hi_of, O_sct. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.
Definition inFrm (a : Z) : Prop := ltac2:(tb__ "0|0|
S41S55S5cVu10;Z90A2Va;A2S57Va;Vu10;A2A2").
Lemma in_RcA a : ltac2:(tb__ "0|1|
S41S55Z0Va;A2S57Va;S58Z2Z40A2A2A2S45S10aVrho';S8dS70Q40Va;A2A3S44SabVa;A1S41S55Z108ecM0Va;A2S57Va;S56G0Z60A2A2A2A2A2F_;").
Proof using Hag.
  intros Ha. unfold in_ranges, inFrm. rewrite RcA_eq, u64 by lia. split.
  - intros (o & Ho & R0). destruct Ho as [<-|[<-|[]]]; [rewrite rng_frm in R0 | rewrite rng_sctC in R0]; cbn [fst snd] in R0; lia.
  - intros [H|H]; [exists oFrm | exists O_sct]; (split; [cbn; tauto|]); [rewrite rng_frm | rewrite rng_sctC]; cbn [fst snd]; lia.
Qed.

Lemma rm1_at a : ltac2:(tb__ "0|3|
S40S3S6fQ8A1A1M0S1cSa9Va;A2S124S10aVrho';S8dVa;A3M1S42G1A1M2A2G0L_;S10bVrho';S8dVa;A3G1S164Vms1;Va;A2L_;G2Sc7Va;A1L_;X124x2A3").
Proof using Hag. unfold rho1, rho_sub, rho_absorb. cbn [rm]. destruct (in_ranges_dec rho' RcA a); [reflexivity | apply rm_rho']. Qed.

Lemma frm_holds : ltac2:(tb__ "0|0|
S39S48Vrho';Vms1;SaaA4").
Proof using HsmC.
  destruct HsmC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [snd cfg_ms] in Hall.
  exact (proj1 (Forall_forall _ _) Hall oFrm ltac:(cbn; tauto)).
Qed.
Lemma frm_byte a : ltac2:(tb__ "0|1|
SabVa;A1S43S6fQ8A1M0G0S40S3G0A1S164Vms1;S70Q40Va;A2A2S7G0R1A2A3Lb;A2F_;").
Proof using Hag Hsm HsmC.
  intros Ha. pose proof A_sp as (SP & _ & _). top_ranges. unfold inFrm in Ha.
  pose proof (bv_unsigned_in_range 64 (rw rho 10%positive)) as U10. change (bv_modulus 64%N) with (2 ^ 64) in U10. fold u10 in U10.
  destruct (dunk_byte segsU rho' ms1 oFrm a frm_holds eq_refl ltac:(rewrite rng_frm; cbn [fst snd]; lia)) as [[b Hb] _].
  unfold rd, ms_read_byte in Hb. destruct (ms_mem ms1 (Z_to_bv 64 a)) as [b0|] eqn:E; [exists b0; reflexivity|].
  exfalso. rewrite (C_rom (Z_to_bv 64 a)) in Hb. rewrite image_byte_none_high in Hb; [discriminate|]. rewrite segs_topU, u64 by lia. lia.
Qed.

Lemma E_sp1 : ltac2:(tb__ "0|0|
S40S47S71Q40S1eSa9PaA2A2S5cVu10;Z90A2A3").
Proof using Hag Hsm req sc u15.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sA 10%positive) with (SAlu ALU_ADD (SVar 10) (SLit (-144))).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. rewrite (rw_rho' 10) by (cbv; reflexivity). fold u10.
  pose proof A_sp as (SP & _). top_ranges.
  pose proof (bv_unsigned_in_range 64 (rw rho 10%positive)) as U10. change (bv_modulus 64%N) with (2 ^ 64) in U10. fold u10 in U10.
  rewrite (Z.mod_small u10) by lia. change ((-144) mod 2 ^ 64) with (2 ^ 64 - 144).
  replace (u10 + (2 ^ 64 - 144)) with ((u10 - 144) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma E_d1 : ltac2:(tb__ "0|1|
S40S47Sc4Z40M0S71Q40S1eSa9PfA2A2A2S56Sc4G0Vu15;A2Z90A2A3").
Proof using Hag Hsm req sc u10.
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sA 15%positive) with (SAlu ALU_ADD (SVar 15) (SLit 144)).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. rewrite (rw_rho' 15) by (cbv; reflexivity). fold u15.
  pose proof A_depth0 as [D1 D2]. unfold AS_D in D1.
  pose proof (bv_unsigned_in_range 64 (rw rho 15%positive)) as U15. change (bv_modulus 64%N) with (2 ^ 64) in U15. fold u15 in U15.
  rewrite (Z.mod_small u15) by lia. change (144 mod 2 ^ 64) with 144.
  apply toS64_add_small; lia.
Qed.

Lemma auxv_init_call : ltac2:(tb__ "0|0|
S40S8S80Vs;A1SaA3S75S48S61VL;Sa9A4F_;").
Proof using E173 HJ Hag Hsm req sc u10 u15.
  intros Hf. destruct (A_init Hf) as [HA _].
  apply (auxv_init_ext rho rho1 L); [ | | | exact HA].
  - rewrite E_sp1. fold u10. lia.
  - intros a Ha. rewrite rm1_at. fold u10 in Ha. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64%N) with (2 ^ 64) in Ra.
    pose proof A_sp as (SP1 & _). top_ranges.
    destruct (in_ranges_dec rho' RcA a) as [I0|O0].
    { exfalso. rewrite <- (Z_to_bv_bv_unsigned 64 a) in I0. apply (in_RcA (bv_unsigned a) Ra) in I0 as [I0|I0]; unfold inFrm in I0; lia. }
    apply (proj1 (proj2 release_R)). intros I1. rewrite <- (Z_to_bv_bv_unsigned 64 a) in I1.
    apply (in_RP (bv_unsigned a) Ra) in I1. unfold inRP in I1. cbn [mc_chk_guard C_U] in I1. pose proof A_sc. lia.
  - intros k Hk. rewrite rm1_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 (mc_auxv C_U + k))) as [I0|O0].
    { exfalso. apply (in_RcA (mc_auxv C_U + k) ltac:(unfold mc_auxv; cbn [mc_libc C_U]; lia)) in I0 as [I0|I0]; unfold inFrm, mc_auxv in I0; cbn [mc_libc C_U] in I0; [pose proof A_sp as (SP1 & _); top_ranges; lia | lia]. }
    apply (proj1 (proj2 release_R)). intros I1.
    apply (in_RP (mc_auxv C_U + k) ltac:(unfold mc_auxv; cbn [mc_libc C_U]; lia)) in I1. unfold inRP, mc_auxv in I1. cbn [mc_chk_guard mc_libc C_U] in I1. pose proof A_sc. lia.
Qed.

Lemma MI_call : ltac2:(tb__ "0|1|
S168S61VX;S9S5S7eS47A2A1VU;S104Vs;VL;A2SbaS48S1cSa9A1M0A2SbbS48G0A2SafVmd;A1A8").
Proof using E173 HJ Hag Hhd Hsm HsmC req u10 u15.
  pose proof A_sp as (SP & SP2 & _). top_ranges. pose proof A_sc as SC.
  unfold MInvI. apply (minvG_frame_core C_U X None U s L _ _ _ _ (m_vmmaps md) inFrm MI_R A_xraw).
  -
    intros a Ha NF. rewrite !rd_of_CG, !wok_of_CG.
    assert (E : rm rho1 (Z_to_bv 64 a) = mR (Z_to_bv 64 a)).
    { rewrite rm1_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcA a Ha) in I0 as [I0|I0]; [exfalso; exact (NF I0)|].
      rewrite (C_ro (Z_to_bv 64 a)) by (replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia).
      symmetry. replace a with (0x108cc + (a - 0x108cc)) by lia. apply mR_rom. lia. }
    split; [apply rd_of_mem; exact E | apply wok_of_mem; exact E].
  -
    intros a Ha _. pose proof Ha as Ha'. unfold inFrm in Ha'.
    unfold Contract.rd_of. rewrite rm1_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 a)) as [I0|O0].
    + destruct (frm_byte a Ha) as [b Hb]. exists b. rewrite Hb. reflexivity.
    + exfalso. apply O0. pose proof (bv_unsigned_in_range 64 (rw rho 10%positive)) as U10. change (bv_modulus 64%N) with (2 ^ 64) in U10. fold u10 in U10.
      apply (in_RcA a ltac:(lia)). left. exact Ha.
  - intros a. unfold inFrm. lia.
  -
    intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n]. cbn [fst snd] in Hx.
    pose proof A_sp_high as SP0. pose proof A_depth0 as [DP _]. unfold AS_D in DP. top_ranges.
    destruct (footprint_entry_cases' s l n He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. rewrite A_ctx in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L s (m_vmmaps md) p n (mig_vm A_MI') (mig_ledger A_MI') He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. lia.
  - intros a Ha Hs. pose proof A_sp as (SP0 & _). top_ranges. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  -
    intros Hf. apply auxv_ok_of_init; [exact (auxv_init_call Hf)|].
    rewrite E_sp1. pose proof A_sp_high as SP0. pose proof A_depth0 as [DP _]. unfold AS_D in DP. lia.
Qed.

Lemma IN_ok : ltac2:(tb__ "0|0|
Sd9S48S61VX;S9S5S7eS47A2A1VU;VA;VKc;Sa9Vtr;Vmd;Aa").
Proof using E173 HJ Hag Hhd Hsm HsmC req u10 u15.
  split; [exact MI_call|]. split; [exact A_xraw|]. split; [exact A_Kc|]. split; [exact auxv_init_call|].
  split.
  { unfold tp_ok. unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sA 24%positive) with (SVar 24). cbn [eval].
    rewrite (rw_rho' 24) by (cbv; reflexivity). exact A_tp. }

  unfold top_high, V_DEPTH, A. cbn [ma_L]. rewrite E_sp1, E_d1. pose proof A_sp_high. lia.
Qed.

Lemma top_of_common X0 X1 (A1 : MA) : ltac2:(tb__ "0|0|
Sd6VX0;VX1;VA;VA1;A4S40S47S62S103VA1;A1A1S62VL;A1A3F_;").
Proof using . intros HC. exact (layout_extends_top _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HC)))))))). Qed.

Section Out.
Variables (L1 : sstate) (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S25S48VrhoL;VL1;S1S4SadA1Sd1Vtr';Sd2Vms';Vmd';A2A4A4").

Hypothesis HL1_rom : ltac2:(tb__ "0|2|
S19S47SecS19R2S32VL1;A1A3S41S55Z108ccM0R2A2S57R2S56G0Za0A2A2A2S42S41S55ScS47S47S22VrhoL;R4A2M1A3R3A2S57R3SeS47S47G1A3A2A2A1F_;F_;Fa;Fo;").
Variable A1 : MA.
Hypothesis Hkept : ltac2:(tb__ "0|0|
SbcS48S61VA;VA1;S1cSa9A1S1cVrhoL;A1A6").

Hypothesis Htop1 : ltac2:(tb__ "0|0|
S40S47S62S103VA1;A1A1S62VL;A1A3").

Lemma rhoL_rom a : ltac2:(tb__ "0|2|
S41S55Z108ccM0Va;A2S57Va;S56G0Za0A2A2A2S40S3S6fQ8A1M1A1S1cVrhoL;S70Q40Va;A2A2S9G1A1A3F_;").
Proof using HL1_rom HsmL req sc u10 u15. try clear Htop1.
  intros Ha. destruct HsmL as (_ & _ & _ & _ & _ & Hro & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hro, Hfr.
  rewrite <- Hfr; [apply Hro; replace a with (0x108cc + (a - 0x108cc)) by lia; apply ro_tabs_P; lia|].
  unfold outside_all. apply Forall_forall. intros o Ho. cbn zeta. rewrite u64 by lia. exact (HL1_rom o a Ho Ha).
Qed.

Lemma kept_RcA a : ltac2:(tb__ "0|0|
S10aVrho';S8dVa;A3S40S3S6fQ8A1A1S1cVrhoL;Va;A2S1cSa9Va;A2A3F_;").
Proof using HJ HL1_rom Hag Hkept Htop1 Hsm HsmC HsmL req sc u10 u15.
  intros IN0. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64%N) with (2 ^ 64) in Ra.
  rewrite <- (Z_to_bv_bv_unsigned 64 a) in IN0 |- *.
  pose proof A_sp_high as SP. pose proof A_depth0 as [DP _]. unfold AS_D in DP. top_ranges.
  destruct (proj1 (in_RcA (bv_unsigned a) Ra) IN0) as [F|T].
  - unfold inFrm in F. apply (Hkept (bv_unsigned a) Ra).
    + left. unfold A. cbn [ma_L]. lia.
    + left. rewrite Htop1. lia.
    + unfold errno_range, mc_errno. cbn [mc_tp C_U]. lia.
    + unfold alloc_static. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]. lia.
  - rewrite (rhoL_rom (bv_unsigned a)) by lia. rewrite rm1_at.
    destruct (in_ranges_dec rho' RcA (Z_to_bv 64 (bv_unsigned a))) as [_|O0]; [|exfalso; exact (O0 IN0)].
    symmetry. apply C_ro. replace (bv_unsigned a) with (0x108cc + (bv_unsigned a - 0x108cc)) by lia. apply ro_tabs_P. lia.
Qed.

Lemma disj_RcA (o' : sobj) mz : ltac2:(tb__ "0|2|
S40S5S47S47A2S22VrhoL;Vo';A2M0S1S47S47Vmz;S56Vmz;Z28A2M1A4A3S55G1S62VL;A1A2S44S55G1Z10000A2S55Z5b000Vmz;A2A2S19SecS19R1S8dA3S3bG0S22Vrho';R2A2A2F_;FoR;F_;F_;F_;").
Proof using HJ Hag Hsm req sc u10 u15. try clear Htop1.
  intros E Hc Hi oR HoR. rewrite E. pose proof A_sp_high as SP. pose proof A_depth0 as [DP _]. unfold AS_D in DP. top_ranges.
  rewrite RcA_eq in HoR. destruct HoR as [<-|[<-|[]]]; [rewrite rng_frm | rewrite rng_sctC]; unfold SymState.ranges_disjoint; cbn [fst snd]; lia.
Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S12bVrho';Vms1;S8dS8eSd3S72A1S8fVL1;Vrho'';VrhoL;A9").
Definition rhoP : valuation := ltac2:(tb__ "0|0|
S137Vrho'';S136Vrho';Vrho'';S8dA3A2").

Lemma rmP_at a : ltac2:(tb__ "0|3|
S40S3S6fQ8A1A1M0S1cS123Va;A2S124S10aVrho';S8dVa;A3M1S42G1A1M2A2G0L_;S10bVrho';S8dVa;A3G1Sc7Va;A1L_;G2S1cVrhoL;Va;A2L_;X124x2A3").
Proof using Hag Hlink. try clear Htop1.
  unfold rhoP, rho_patch, patchf. cbn [rm]. destruct (in_ranges_dec rho' RcA a); [apply rm_rho' | apply (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink)].
Qed.
Lemma rwP j : ltac2:(tb__ "0|0|
S16fVj;P12cA2S40S6fQ40A1S1eS123Vj;A2S1eVrho;Vj;A2A3F_;").
Proof using Hag Hlink. try clear Htop1.
  intros Hj. unfold rhoP, rho_patch. cbn [rw]. rewrite (call_linkP_rw _ _ _ _ _ _ _ _ _ j Hlink) by (change (ss_next EvA) with 300%positive; exact Hj).
  apply rw_rho'. exact Hj.
Qed.
Lemma rlP l : ltac2:(tb__ "0|0|
S40S4S6fQ8A1A1S2bS123Vl;A2S2bSc8Vl;A2A3").
Proof using Hag Hlink. try clear Htop1. unfold rhoP, rho_patch. cbn [rl]. rewrite (call_linkP_rl _ _ _ _ _ _ _ _ _ l Hlink). symmetry. exact (proj1 (proj2 Hag) l). Qed.

Hypothesis Hcan : ltac2:(tb__ "0|0|
S7cS48S61S1cSa9A1S1cVrhoL;A1A4").

Lemma contA_frame_P : contA_frame rho rhoP.
Proof using E173 HJ HL1_rom Hag Hcan Hlink Hsm HsmL. try clear Htop1.
  split; [exact rwP|].
  split; [rewrite rlP; unfold rhoT, rho_set_rl; cbn [rl]; rewrite Pos.eqb_refl; reflexivity|].
  split; [intros l Hl; rewrite rlP; unfold rhoT, rho_set_rl; cbn [rl]; replace (Pos.eqb l 1) with false by (symmetry; apply Pos.eqb_neq; exact Hl); reflexivity|].
  split.
  - intros kk Hk. rewrite rmP_at. destruct (in_ranges_dec rho' RcA _); [apply mR_rom; exact Hk | apply rhoL_rom; lia].
  - pose proof A_sc as SC. pose proof A_sp as (SP & _). top_ranges.
    assert (GEN : forall a v, (0x28d50 <= a < 0x28d50 + 8 \/ mc_chk_guard C_U <= a < mc_chk_guard C_U + 8) ->
              rd ms (Z_to_bv 64 a) = Some v -> Contract.rd_of segsU (rm rhoP) (Z_to_bv 64 a) = Some v).
    { intros a v Ha Hv. cbn [mc_chk_guard C_U] in Ha.
      assert (Ra : 0 <= a < 2 ^ 64) by lia.
      assert (NR : ~ in_ranges rho' RcA (Z_to_bv 64 a)).
      { intros I0. apply (in_RcA a Ra) in I0 as [I0|I0]; unfold inFrm in I0; lia. }
      unfold Contract.rd_of. rewrite rmP_at. destruct (in_ranges_dec rho' RcA _) as [I0|_]; [exfalso; exact (NR I0)|].
      pose proof (Hcan a ltac:(cbn [mc_chk_guard_got mc_chk_guard C_U]; lia)) as CK. unfold Contract.rd_of in CK. rewrite CK.
      rewrite rm1_at. destruct (in_ranges_dec rho' RcA _) as [I0|_]; [exfalso; exact (NR I0)|].
      assert (GI : inRP a) by (unfold inRP; cbn [mc_chk_guard C_U]; lia).
      rewrite (proj1 (proj2 (proj2 release_R)) _ (proj2 (in_RP a Ra) GI)).
      unfold rd, ms_read_byte in Hv. destruct (ms_mem ms (Z_to_bv 64 a)) as [b|]; [exact Hv|]. rewrite (A_rom (Z_to_bv 64 _)) in Hv. exact Hv. }
    split; intros k Hk.
    + apply GEN; [cbn [mc_chk_guard_got C_U]; lia|]. exact (RP_got k Hk).
    + apply GEN; [lia|]. exact (RP_guardv k Hk).
Qed.

Lemma MI_patch X1 (A2 : MA) md2 : ltac2:(tb__ "0|2|
S74S48S61VX1;S9S5S7eS47A2A1M0VU;VA2;VrhoL;Vmd2;A8S182VX1;S101VA2;A1M1A2S40S8S80G1A1S6A3S40S47S62S103VA2;A1A1S62VL;A1A3S74S48S61VX1;G0VU;VA2;S123Vmd2;A8F_;F_;F_;F_;").
Proof using E173 HJ HL1_rom Hag Hlink Hsm HsmL req sc u10 u15. try clear Htop1.
  destruct A2 as [s1 L1y]. cbn [ma_s]. intros HM HX1 Hinit1 ET. unfold MInvIR, MInvI in *. cbn [ma_s ma_L] in *.
  pose proof A_sp_high as SP0. pose proof A_depth0 as [DP _]. unfold AS_D in DP. top_ranges.
  pose proof (bv_unsigned_in_range 64 (rw rho 10%positive)) as U10. change (bv_modulus 64%N) with (2 ^ 64) in U10. fold u10 in U10.
  apply (minvG_frame_core C_U X1 None U s1 L1y _ _ _ _ (m_vmmaps md2) inFrm HM HX1).
  - intros a Ha NF. rewrite !rd_of_CG, !wok_of_CG.
    assert (E : rm rhoP (Z_to_bv 64 a) = rm rhoL (Z_to_bv 64 a)).
    { rewrite rmP_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 a)) as [I0|O0]; [|reflexivity].
      apply (in_RcA a Ha) in I0 as [I0|I0]; [exfalso; exact (NF I0)|].
      rewrite (rhoL_rom a) by lia. replace a with (0x108cc + (a - 0x108cc)) by lia. apply mR_rom. lia. }
    split; [apply rd_of_mem; exact E | apply wok_of_mem; exact E].
  - intros a Ha Hg. exfalso. unfold inFrm in Ha. cbn [mc_chk_guard C_U] in Hg. lia.
  - intros a. unfold inFrm. lia.
  - intros a Ha (e & He & Hx). unfold inFrm in Ha. destruct e as [l n]. cbn [fst snd] in Hx.
    destruct (footprint_entry_cases' s1 l n He) as [[-> ->] | [p ->]].
    + unfold loc_addr in Hx. pose proof (mig_ctx HM) as CX. cbn [ma_L mc_ctx C_U] in CX. rewrite CX in Hx. unfold CTX_SIZE in Hx. lia.
    + pose proof (fp_mem_range C_U L1y s1 (m_vmmaps md2) p n (mig_vm HM) (mig_ledger HM) He ltac:(lia)) as (_ & G2 & _).
      unfold addr_of in G2. top_ranges. destruct p as [pr po]. cbn [loc_addr prid poff] in Hx, G2. lia.
  - intros a Ha Hs. unfold inFrm, static_ng in *. cbn [mc_chk_guard mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock C_U] in Hs. lia.
  - intros Hf. rewrite Hinit1 in Hf. discriminate Hf.
Qed.

Lemma kept_patch A2 : ltac2:(tb__ "0|0|
SbcS48S61VA;VA2;S1cSa9A1S1cVrhoL;A1A6SbcS48S61VA;VA2;S1cVrho;A1S1cS123A1A6F_;").
Proof using E173 HJ Hag Hlink Hsm. try clear Htop1.
  intros HK a Ha HcA HcA1 Hne Hns. pose proof A_sc as SC.
  rewrite rmP_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 a)) as [I0|O0].
  -
    apply (proj1 (proj2 release_R)). intros I1. apply (in_RP a Ha) in I1. apply (in_RcA a Ha) in I0.
    unfold inRP, inFrm in *. cbn [mc_chk_guard C_U] in I1. pose proof A_sp as (SP & _). top_ranges. lia.
  - rewrite (HK a Ha HcA HcA1 Hne Hns). rewrite rm1_at. destruct (in_ranges_dec rho' RcA (Z_to_bv 64 a)) as [I0|_]; [exfalso; exact (O0 I0)|].
    apply (proj1 (proj2 release_R)). intros I1. apply (in_RP a Ha) in I1 as [G|[G|G]].
    + apply Hns. unfold alloc_static. cbn [mc_chk_guard_got C_U]. lia.
    + apply Hns. unfold alloc_static. lia.
    +
      apply (client_addr_not_ownedG_U X None U A _ _ (m_vmmaps md) a A_MI' A_xraw HcA).
      left. replace a with (ly_ctx L + (a - ly_ctx L)) by lia. apply ctx_ownedA. rewrite A_ctx. unfold CTX_SIZE. lia.
Qed.

Hypothesis HagL : ltac2:(tb__ "0|0|
S12aS49Sa9VrhoL;A3").
Lemma rhoL_10 : ltac2:(tb__ "0|0|
S40S47S71Q40S1eVrhoL;PaA2A2S5cVu10;Z90A2A3").
Proof using Hag HagL Hsm req sc u15. try clear Htop1. rewrite <- (proj1 HagL 10%positive) by (cbv; reflexivity). exact E_sp1. Qed.
Lemma rhoL_15 : ltac2:(tb__ "0|1|
S40S47Sc4Z40M0S71Q40S1eVrhoL;PfA2A2A2S56Sc4G0Vu15;A2Z90A2A3").
Proof using Hag HagL Hsm req sc u10. try clear Htop1.
  rewrite <- (proj1 HagL 15%positive) by (cbv; reflexivity).
  unfold rho1. cbn [rho_sub rw]. rewrite eval_absorb. change (wsub_get sA 15%positive) with (SAlu ALU_ADD (SVar 15) (SLit 144)).
  rewrite eval_zeval by reflexivity. cbn [zeval zalu]. unfold zr_of. rewrite (rw_rho' 15) by (cbv; reflexivity). fold u15.
  pose proof A_depth0 as [D1 D2]. unfold AS_D in D1.
  pose proof (bv_unsigned_in_range 64 (rw rho 15%positive)) as U15. change (bv_modulus 64%N) with (2 ^ 64) in U15. fold u15 in U15.
  rewrite (Z.mod_small u15) by lia. change (144 mod 2 ^ 64) with 144.
  apply toS64_add_small; lia.
Qed.
Lemma stkL_rom a : ltac2:(tb__ "0|2|
S41S55Z108ccM0Va;A2S57Va;S56G0Za0A2A2A2S42S41S55ScS47S47S22VrhoL;Sc2SdbA1A2M1A3Va;A2S57Va;SeS47S47G1A3A2A2A1F_;").
Proof using Hag HagL Hsm req sc u10 u15. try clear Htop1.
  intros Ha. unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd eval].
  rewrite soff_lit_small by lia. unfold soff, V_DEPTH. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64.
  cbn [eval]. rewrite rhoL_10, rhoL_15. pose proof A_sp_lo_lit as SP. lia.
Qed.
End Out.

Section OutNull.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S25S48VrhoL;Sd5S72A1S1S4SadA1Sd1Vtr';Sd2Vms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
S12aS49Sa9VrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
Sd7S48S61VX;S9S5S7eS47A2A1VU;VA;VKc;Sa9VrhoL;Vtr';Vmd';Ab").

Lemma null_rom : ltac2:(tb__ "0|2|
S19S47SecS19R2S32Sd5S72A1A1A3S41S55Z108ccM0R2A2S57R2S56G0Za0A2A2A2S42S41S55ScS47S47S22VrhoL;R4A2M1A3R3A2S57R3SeS47S47G1A3A2A2A1F_;F_;Fa;Fo;").
Proof using Hag HagL Hsm req sc u10 u15. intros o a Ho Ha. cbn [ss_objs L_am_null] in Ho. destruct Ho as [<-|[]]. exact (stkL_rom rhoL HagL a Ha). Qed.

Lemma iok_null : ltac2:(tb__ "0|0|
S12eVrho';Vms1;S8dS8eSd3S72A1Sd5S72A1VrhoL;A7").
Proof using HJ HJL Hag HagL Hsm HsmC HsmL req sc u10 u15.
  destruct HJL as (A1 & HM1 & HC1 & Hkept & _).
  split.
  - intros a Ha. exact (kept_RcA (L_am_null IEC_U) rhoL tr' ms' md' HsmL null_rom A1 Hkept (top_of_common _ _ _ HC1) a Ha).
  - intros o' oR Hin' _. exfalso. cbn in Hin'. exact Hin'.
Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S12bVrho';Vms1;S8dS8eSd3S72A1S8fSd5S72A1Vrho'';VrhoL;A9").

Lemma cont_null w : ltac2:(tb__ "0|0|
SefS48S12cSd7S48S61VX;S9S5S7eS47A2A1VU;VA;VKc;A7Sa9VrhoL;A3S12fS8eS23Sd3S72A1A1Sd5S72A1S23S8fA1S8dA5Vrho'';Vw;A5SefS48S179VX;VU;VA;VKc;Vrho;A5S93SacVrho'';A1Vw;A5F_;").
Proof using E173 HJ Hag HagL Hhd Hlink Hsm HsmC HsmL.
  intros [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ'.
  destruct HJ' as (A2 & HM2 & HC2 & Hkept2 & Hmaps2 & Hcan2 & Hy2 & HKc2).
  assert (Hag'' : agree_vals (ss_next EvA) rho' rho'') by exact (proj1 Hlink).
  split.
  - apply (smatch_xforms segsU _ _ TnullA SnullA _ SnullA_ok). rewrite <- TnullA_eq.
    exact (cont_smatch segsU EvA (Pre_am IEC_U) (L_am_null IEC_U) sA RcA rho' rho'' tr ms1 md _ entA HsmC eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model].
    split; [exact (contA_frame_P (L_am_null IEC_U) rhoL tr' ms' md' HsmL null_rom rho'' Hlink Hcan2)|].
    split; [exact HKc2|]. split; [exact A_pure|].
    exists A2.
    split; [exact (MI_patch (L_am_null IEC_U) rhoL tr' ms' md' HsmL null_rom rho'' Hlink X A2 mdw HM2 (proj1 HC2) (proj1 (proj2 HC2)) (top_of_common _ _ _ HC2))|].
    split; [exact HC2|].
    split. { destruct HC2 as (_ & _ & _ & (EA & _) & _). unfold active_hd. rewrite EA. exact Hhd. }
    split; [exact (kept_patch (L_am_null IEC_U) rhoL rho'' Hlink A2 Hkept2)|].
    exact Hy2.
Qed.
End OutNull.

Section OutOk.
Variables (rhoL : valuation) (tr' : list event) (ms' : machine_state) (md' : Model).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S25S48VrhoL;Sd4S72A1S1S4SadA1Sd1Vtr';Sd2Vms';Vmd';A2A4A4").
Hypothesis HagL : ltac2:(tb__ "0|0|
S12aS49Sa9VrhoL;A3").
Hypothesis HJL : ltac2:(tb__ "0|0|
Sd8S48S61VX;S9S5S7eS47A2A1VU;VA;VKc;Sa9VrhoL;Vtr';Vmd';Ab").

Lemma meta_rng : ltac2:(tb__ "0|1|
S40S5S47S47A2S22VrhoL;SdaA2S1S47S47S71Q40S1eVrhoL;SbdA2A2M0S56G0Z28A2A4A3").
Proof using req sc u10 u15.
  unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi eval]. unfold META_SIZE.
  rewrite !soff_lit_small by lia. f_equal. lia.
Qed.

Lemma ok_meta_where : ltac2:(tb__ "0|1|
S43S47S47S41S40S5S47S47A2S22VrhoL;SdaA2S1S47S47R1S56R1Z28A2M0A4A3S41S55Z1000R1A2S41S55G0S62VL;A1A2S44S55G0Z10000A2S55Z5b000R1A2A2A2A2A2Lmz;A2").
Proof using HJL req sc u10 u15.
  destruct HJL as (A1 & m & Em & HM1 & HC1 & Hmemb & Hkey & _).
  exists (bv_unsigned (rw rhoL V_RES)). split; [exact meta_rng|].
  pose proof HM1 as HMI. unfold MInvIR, MInvI in HMI.
  pose proof (key_range (m :: X) None U (ma_s A1) (ma_L A1) (mig_I HMI) (mig_layout HMI) C_U (m_vmmaps md') m Hkey (mig_vm HMI) (mig_ledger HMI)) as (K1 & K2 & K3 & _).
  pose proof (top_of_common _ _ _ HC1) as ET.
  rewrite Em in K1, K2, K3. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold META_SIZE, PGSZ in *. lia.
Qed.

Lemma ok_rom : ltac2:(tb__ "0|2|
S19S47SecS19R2S32Sd4S72A1A1A3S41S55Z108ccM0R2A2S57R2S56G0Za0A2A2A2S42S41S55ScS47S47S22VrhoL;R4A2M1A3R3A2S57R3SeS47S47G1A3A2A2A1F_;F_;Fa;Fo;").
Proof using HJL Hag HagL Hsm req sc u10 u15.
  intros o a Ho Ha. cbn [ss_objs L_am_ok] in Ho. destruct Ho as [<-|[<-|[]]]; [exact (stkL_rom rhoL HagL a Ha)|].
  destruct ok_meta_where as (mz & E & _ & _ & D). rewrite E. cbn [fst snd]. lia.
Qed.

Lemma iok_ok : ltac2:(tb__ "0|0|
S12eVrho';Vms1;S8dS8eSd3S72A1Sd4S72A1VrhoL;A7").
Proof using HJ HJL Hag HagL Hsm HsmC HsmL req sc u10 u15.
  pose proof ok_meta_where as (mz & E & _ & C2 & D).
  destruct HJL as (A1 & m & Em & HM1 & HC1 & Hmemb & Hkey & Hkept & _).
  split.
  - intros a Ha. exact (kept_RcA (L_am_ok IEC_U) rhoL tr' ms' md' HsmL ok_rom A1 Hkept (top_of_common _ _ _ HC1) a Ha).
  - intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]]. exact (disj_RcA rhoL _ mz E C2 D oR HinR).
Qed.

Variable rho'' : valuation.
Hypothesis Hlink : ltac2:(tb__ "0|0|
S12bVrho';Vms1;S8dS8eSd3S72A1S8fSd4S72A1Vrho'';VrhoL;A9").

Lemma cont_ok w : ltac2:(tb__ "0|0|
SefS48S12cSd8S48S61VX;S9S5S7eS47A2A1VU;VA;VKc;A7Sa9VrhoL;A3S12fS8eS23Sd3S72A1A1Sd4S72A1S23S8fA1S8dA5Vrho'';Vw;A5SefS48S17aVX;VU;VA;VKc;Vrho;A5S94SacVrho'';A1Vw;A5F_;").
Proof using E173 HJ HJL Hag HagL Hhd Hlink Hsm HsmC HsmL.
  intros [Hsm' HJ']. destruct w as [trw [msw mdw]]. cbn [J_ofP w_tr w_cfg cfg_model] in HJ'.
  destruct HJ' as (A2 & m & Em & HM2 & HC2 & Hmemb & Hkey & Hkept2 & Hmaps2 & Hcan2 & Hy2 & HKc2).
  assert (Hag'' : agree_vals (ss_next EvA) rho' rho'') by exact (proj1 Hlink).
  split.
  - apply (smatch_xforms segsU _ _ TokA SokA _ SokA_ok). rewrite <- TokA_eq.
    exact (cont_smatch segsU EvA (Pre_am IEC_U) (L_am_ok IEC_U) sA RcA rho' rho'' tr ms1 md _ entA HsmC eq_refl Hag'' Hsm').
  - cbn [w_tr w_cfg cfg_model].
    split; [exact (contA_frame_P (L_am_ok IEC_U) rhoL tr' ms' md' HsmL ok_rom rho'' Hlink Hcan2)|].
    split; [exact HKc2|]. split; [exact A_pure|].
    exists A2, m. split.
    { rewrite Em. f_equal. unfold rhoP. cbn [rho_patch rw]. destruct Hlink as (_ & _ & _ & L4).
      rewrite (L4 V_RES eq_refl ltac:(cbv; lia)).
      change (ss_next (Pre_am IEC_U)) with NF. change (ss_next EvA) with 300%positive. rewrite imp_VRES. reflexivity. }
    split; [exact (MI_patch (L_am_ok IEC_U) rhoL tr' ms' md' HsmL ok_rom rho'' Hlink (m :: X) A2 mdw HM2 (proj1 HC2) (proj1 (proj2 HC2)) (top_of_common _ _ _ HC2))|].
    split; [exact HC2|]. split; [exact Hmemb|]. split; [exact Hkey|].
    split. { destruct HC2 as (_ & _ & _ & (EA & _) & _). unfold active_hd. rewrite EA. exact Hhd. }
    split; [exact (kept_patch (L_am_ok IEC_U) rhoL rho'' Hlink A2 Hkept2)|].
    exact Hy2.
Qed.
End OutOk.
End Call.
End A.

Section TRA.
Variables (X : list sptr) (U : Z -> Z) (s : astate) (L : layout) (Kc : list event -> Model -> Prop) (rho0 : valuation).
Variables (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S169S48VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Let A : MA := mkMA s L.
Let sc : Z := bv_unsigned (rw rho0 12%positive).

Variable kam : Z.
Hypothesis Hkam : 0 <= kam.
Variables NG OG : Prop.
Hypothesis AM : ltac2:(tb__ "0|1|
S28VTR;Vkam;SefS48Sd9S48S61VX;S9S5S7eS47A2A1M0VU;VA;VKc;A7Sd3S72A1R1A4S131S48S49R1S17fS48S61S72VNG;VOG;VX;G0VU;VA;VKc;AaA4A3Frho1;").
Hypothesis Hhd : ltac2:(tb__ "0|0|
S40S3S7eA1S110Vs;Vsc;A2S9S7eA1A3").
Hypothesis E173 : ltac2:(tb__ "0|1|
S40S6fQ40M0A1S1eVrho0;PadA2S70G0S64S61A1A2A3").
Variable Q : assn.

Hypothesis CONT_null : ltac2:(tb__ "0|0|
VNG;S28VTR;VkB;SefS48S179VX;VU;VA;VKc;Vrho0;A5S93R1A4VQ;A3FrhoK;F_;").
Hypothesis CONT_ok : ltac2:(tb__ "0|0|
VOG;S28VTR;VkB;SefS48S17aVX;VU;VA;VKc;Vrho0;A5S94R1A4VQ;A3FrhoK;F_;").

Theorem step_A : ltac2:(tb__ "0|0|
VTR;S56Vkam;VkB;A2SefS48S76S48S61VX;VU;VA;VKc;A6S9aVrho0;A4VQ;A3").
Proof using AM CONT_null CONT_ok E173 Hhd HkB Hkam RR.
  (apply (trr_inhP RR); [lia|]). intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg cfg_model] in HJ.
  set (K0 := fun tr' md' => Kc tr' md' /\ tr' = tr /\ md' = md).
  exists (SymSoundR.SP segsU K0 SGS (rhoT rho0 ms)). split.
  { split; [exact (smatch_SGS X U s L Kc rho0 tr ms md Hsm HJ E173)|]. cbn. split; [exact (A_Kc X U s L Kc rho0 tr md HJ) | split; reflexivity]. }
  apply ((trr_run RR) (kam + kB) 200%nat CUTS_A K0 SGS _ (rhoT rho0 ms) Q ltac:(lia) runA eq_refl ltac:(intros t m [H _]; exact H)).
  intros Lf rho' HinL Hag. destruct HinL as [<-|[]]. cbn [lf_state].
  eapply (trr_pre RR) with (P := SPJ segsU (liftK K0) EvA rho').
  { intros w HSP. exact (SPJ_unbase segsU (liftK K0) rho' ClA 0 (-144) EvA w EvA_ok HSP). }
  apply ((trr_callP RR) kam kB (liftK K0) (J_am_pre segsU C_U X None U A Kc) EvA (Pre_am IEC_U) sA RcA (Posts_amG segsU C_U IEC_U NG OG X None U A Kc) Q rho' HkB entA chkA AM).
  -
    intros tr1 ms1 md1 HsmE [HK [-> ->]].
    exact (IN_ok X U s L Kc rho0 tr ms md Hsm HJ Hhd E173 rho' ms1 Hag HsmE).
  -
    intros L1 JL tr1 ms1 md1 rhoL tr' ms' md' HinL HsmE [HK [-> ->]] HagL HsmL HJL.
    cbn [Posts_amG In] in HinL. destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L1 JL; [destruct HJL as [HNG HJL] | destruct HJL as [HOG HJL]].
    +
      split; [exact (iok_null X U s L Kc rho0 tr ms md Hsm HJ rho' ms1 Hag HsmE rhoL tr' ms' md' HsmL HagL HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU (contA_null X U A Kc rho0) SnullA (rhoP rho' rho'')) _ Q); [|apply (CONT_null HNG)].
      intros w [HsmW [_ HJW]]. exact (cont_null X U s L Kc rho0 tr ms md Hsm HJ Hhd E173 rho' ms1 Hag HsmE rhoL tr' ms' md' HsmL HagL rho'' Hlink w (conj HsmW HJW)).
    +
      split; [exact (iok_ok X U s L Kc rho0 tr ms md Hsm HJ rho' ms1 Hag HsmE rhoL tr' ms' md' HsmL HagL HJL)|].
      intros rho'' Hlink.
      apply ((trr_pre RR) (SPJ segsU (contA_ok X U A Kc rho0) SokA (rhoP rho' rho'')) _ Q); [|apply (CONT_ok HOG)].
      intros w [HsmW [_ HJW]]. exact (cont_ok X U s L Kc rho0 tr ms md Hsm HJ Hhd E173 rho' ms1 Hag HsmE rhoL tr' ms' md' HsmL HagL HJL rho'' Hlink w (conj HsmW HJW)).
Qed.
End TRA.
End Mal_agrp_A.

Module Mal_agrp_T.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition STx (x : m1v) : sstate := ltac2:(tb__ "0|0|
S9fS1bLx;Vx;S156S157S158S159X9fx4").
Definition LT (x : m1v) : list leaf := ltac2:(tb__ "0|0|
S9fS4S87A1Lx;Vx;S146S147S148S149X9fx4").
Lemma STx_eq x : ltac2:(tb__ "0|0|
S40S1bS13dSb3Vx;A1A1Sf5Vx;A1A3"). Proof. destruct x; [exact ST_a_eq | exact ST_b_eq | exact ST_c_eq | exact ST_d_eq]. Qed.
Lemma runT x : ltac2:(tb__ "0|1|
S40S3S4S87A1M0A1S88S48U1f4S140Sf5Vx;A1S6A5S7G0SfaVx;A1A2A3").
Proof. destruct x; [exact (eq_trans runT_a eq_refl) | exact (eq_trans runT_b eq_refl) | exact (eq_trans runT_c eq_refl) | exact (eq_trans runT_d eq_refl)]. Qed.
Lemma STx_lenient x : ltac2:(tb__ "0|0|
S40S8S35Sf5Vx;A1A1SaA3"). Proof. destruct x; reflexivity. Qed.
Lemma STx_next x : ltac2:(tb__ "0|1|
S41S40S46S23Sf5Vx;A1A1S23Sb3Vx;A1A1M0A3S171Pc8G0A2A2"). Proof. destruct x; split; vm_compute; try reflexivity; discriminate. Qed.

Definition SVx (x : m1v) : sstate := ltac2:(tb__ "0|0|
S9fS1bLx;Vx;S15aS15bS15cS15dX9fx4").
Definition LV (x : m1v) : list leaf := ltac2:(tb__ "0|0|
S9fS4S87A1Lx;Vx;S14aS14bS14cS14dX9fx4").
Definition LTc (x : m1v) : sstate := ltac2:(tb__ "0|0|
S141SfaVx;A1U0Sf5Vx;A1A3").
Lemma LT_single x : ltac2:(tb__ "0|0|
S40S4S87A1SfaVx;A1S0S87S8aSf8Vx;A1S89A2S2S87A1A3A3"). Proof. destruct x; reflexivity. Qed.
Lemma SVx_eq x : ltac2:(tb__ "0|0|
S40S1bS13eSf8Vx;A1A1Sf6Vx;A1A3"). Proof. destruct x; [exact SV_a_eq | exact SV_b_eq | exact SV_c_eq | exact SV_d_eq]. Qed.
Lemma runV x : ltac2:(tb__ "0|1|
S40S3S4S87A1M0A1S88S48U1f4S140Sf6Vx;A1S6A5S7G0SfbVx;A1A2A3").
Proof. destruct x; [exact (eq_trans runV_a eq_refl) | exact (eq_trans runV_b eq_refl) | exact (eq_trans runV_c eq_refl) | exact (eq_trans runV_d eq_refl)]. Qed.
Lemma SVx_lenient x : ltac2:(tb__ "0|0|
S40S8S35Sf6Vx;A1A1SaA3"). Proof. destruct x; reflexivity. Qed.
Lemma SVx_swf x : ltac2:(tb__ "0|0|
S40S8S38Sf6Vx;A1A1S6A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SVx_next x : ltac2:(tb__ "0|0|
S40S46S23Sf6Vx;A1A1S23Sb3Vx;A1A1A3"). Proof. destruct x; reflexivity. Qed.
Definition e_divu : sv := SMd M_DIVU (SLit 4080) (SVar 191).
Lemma sdV x : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108Sf8Vx;A1Sf6Vx;A1A2S7G3S1G1G2S0G0S1S12S12S100S11Pa2A1A4S2G0A1A3S2S14A1A4A2A3").
Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma LTc_vars x : ltac2:(tb__ "0|1|
S40S8S129S46SfSf2S105S5S46S12A2M0S46ScS46S12A2S2G0A1A4R1A2A1Lu;Sf8Vx;A1A2S6A3").
Proof. destruct x; vm_compute; reflexivity. Qed.

Definition SWx (x : m1v) : sstate := ltac2:(tb__ "0|0|
S9fS1bLx;Vx;S15eS15fS160S161X9fx4").
Definition LW (x : m1v) : list leaf := ltac2:(tb__ "0|0|
S9fS4S87A1Lx;Vx;S14eS14fS150S151X9fx4").
Definition LVc (x : m1v) (i : nat) : sstate := ltac2:(tb__ "0|0|
S141SfbVx;A1Vi;Sf6Vx;A1A3").
Lemma LV_pair x : ltac2:(tb__ "0|0|
S40S4S87A1SfbVx;A1S0S87S8aSf4Vx;U0A2S89A2S0S87S8aSf4Vx;U1A2S89A2S2S87A1A3A3A3"). Proof. destruct x; reflexivity. Qed.
Lemma SWx_eq x : ltac2:(tb__ "0|0|
S40S1bS13fSf4Vx;U0A2A1Sf7Vx;A1A3"). Proof. destruct x; [exact SW_a_eq | exact SW_b_eq | exact SW_c_eq | exact SW_d_eq]. Qed.
Lemma runW x : ltac2:(tb__ "0|1|
S40S3S4S87A1M0A1S88S48U1f4S140Sf7Vx;A1S6A5S7G0SfdVx;A1A2A3").
Proof. destruct x; [exact (eq_trans runW_a eq_refl) | exact (eq_trans runW_b eq_refl) | exact (eq_trans runW_c eq_refl) | exact (eq_trans runW_d eq_refl)]. Qed.
Lemma SWx_lenient x : ltac2:(tb__ "0|0|
S40S8S35Sf7Vx;A1A1SaA3"). Proof. destruct x; reflexivity. Qed.
Lemma SWx_swf x : ltac2:(tb__ "0|0|
S40S8S38Sf7Vx;A1A1S6A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SWx_next x : ltac2:(tb__ "0|0|
S40S46S23Sf7Vx;A1A1S23Sb3Vx;A1A1A3"). Proof. destruct x; reflexivity. Qed.
Definition e_aiT : sv := SAlu ALU_ADD (SVar 176%positive) (SLit (-1)).
Definition e_aiF : sv := ltac2:(tb__ "0|3|
S18S51S18S4cS18S52S11Pa2A1M0S18S4cG0S13N1A1M1A3M2A3G1A3G2A3").
Definition f_lt : sprop := ltac2:(tb__ "0|0|
S1aS53S11Pb0A1S11Pa2A1A3").
Lemma sdW0 x : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108Sf4Vx;U0A2Sf7Vx;A1A2S7G3S1G1G2S0G0S1S12S12SffS11Pa1A1A4S2G0A1A3S2S14A1A4A2A3"). Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma sdW1 x : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108Sf4Vx;U1A2Sf7Vx;A1A2S7G3S1G1G2S0G0S1S12S12SfeS11Pa1A1A4S2G0A1A3S2S14A1A4A2A3"). Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma LV0_fact x : ltac2:(tb__ "0|0|
S40S8SeeS14S37Sf9A1S27Sf4Vx;U0A2A1A3S6A3"). Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma LV1_fact x : ltac2:(tb__ "0|0|
S40S8SeeS14S37S26Sf9A1A1S27Sf4Vx;U1A2A1A3S6A3"). Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma LVc_vars x i : ltac2:(tb__ "0|1|
SebVi;U2A2S40S8S129S46SfSf2S105S5S46S12A2M0S46ScS46S12A2S2G0A1A4R1A2A1Lu;Sf4Vx;Vi;A2A2S6A3F_;").
Proof. intros Hi. destruct i as [|[|i]]; [| |lia]; destruct x; vm_compute; reflexivity. Qed.
Lemma existsb_In p l : ltac2:(tb__ "0|0|
S40S8SeeS14S37Vp;A1Vl;A3S6A3SecS14Vp;Vl;A3F_;").
Proof. intros H. apply existsb_exists in H as (q & Hq & E). apply sprop_eqb_sound in E. subst q. exact Hq. Qed.

Definition SKTo (x : m1v) : sstate := ltac2:(tb__ "0|0|
S128Sb3Vx;A1A1S1bS21S2cR1A1S33R1A1S31R1A1S30R1A1S34R1A1SbS19S32R1A1S0S19S139S2S19A1A3A3S27R1A1S23R1A1S35R1A1A9TE;").
Lemma SKTo_swf x : ltac2:(tb__ "0|0|
S40S8S38SfcVx;A1A1S6A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma STx_swf x : ltac2:(tb__ "0|0|
S40S8S38Sf5Vx;A1A1S6A3"). Proof. destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sdT x : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108SfcVx;A1Sf5Vx;A1A2S7G3S1G1G2S0G0S1S12S12S11S23Sb3Vx;A1A1A1S163PbbA1A4S2G0A1A3S138A4A2A3").
Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma SKTo_vars x : ltac2:(tb__ "0|1|
S40S8S129S46SfSf2S105S5S46S12A2M0S46ScS46S12A2S2G0A1A4R1A2A1Lu;SfcVx;A1A2S6A3").
Proof. destruct x; vm_compute; reflexivity. Qed.
Lemma FT_vars : ltac2:(tb__ "0|0|
S40S8SedS14S133Sf3A1S138A3S6A3"). Proof. reflexivity. Qed.
Lemma FT_sup : ltac2:(tb__ "0|0|
S40S8SedS14Sc6S138A3S6A3"). Proof. reflexivity. Qed.

Lemma set_R_ok ia za : ltac2:(tb__ "0|0|
Se5Via;A1Se5Se0Via;Vza;A2A1F_;").
Proof. intros H. destruct H. constructor; assumption. Qed.
Lemma set_R_live ia za cur Lc mWc vmc : ltac2:(tb__ "0|0|
SdeVia;Vcur;VLc;VmWc;Vvmc;A5SdeSe0Via;Vza;A2Vcur;VLc;VmWc;Vvmc;A5F_;").
Proof. intros H. destruct H. constructor; assumption. Qed.

Section T.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S169S48VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variable za : Z.
Let ia' : instA := set_R ia za.
Let L : layout := ia_L ia. Let vm : VmMaps := ia_vm ia. Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia.
Variables (cur : astate) (mWc : word -> option byte).
Hypothesis HLV : ltac2:(tb__ "0|0|
SdeVia;Vcur;VL;VmWc;Vvm;A5").
Hypothesis Hgr : grant_ok ia za.
Hypothesis HE : ltac2:(tb__ "0|0|
S66S65S165S48VmWc;A2S6fQ40A1S6L_;A2S69S61A1U4Se3Via;A1A4").
Let len : Z := ineeded ia.
Definition m1 : word -> option byte := ltac2:(tb__ "0|0|
S175VmWc;S63Vza;A1S125S63Vlen;A1A1A3").
Definition vm1 : VmMaps := ltac2:(tb__ "0|0|
S126Vvm;S63Vlen;A1S63Vza;A1A3").
Definition K1 : list event -> Model -> Prop := K_v Kc vm1.

Lemma Hi' : instA_ok ia'. Proof using Hi za. exact (set_R_ok ia za Hi). Qed.
Lemma a_facts : ltac2:(tb__ "0|4|
S41S55Z1000M0Vza;A2S41S55S56Vza;Vlen;A2S62VL;A1M1A2S41S40S47S5aVza;G0A2Z0M2A3S41S55G1Z7fffff800000A2S41S41S55G0Vlen;A2S55Vlen;S58Z2Z17A2A2A2S41S40S47S5aVlen;G0A2G2A3S41S40S47S71Q40M3S63Vza;A1A2Vza;A3S40S47S71G3S125S63Vlen;A1A1A2Vlen;A3A2A2A2A2A2A2A2").
Proof using Hgr Hi sc.
  pose proof Hgr as (Hal & Hpos & Hceil & _). pose proof (len_facts ia Hi) as (LR & LA & LU & LN & LM). top_ranges.
  unfold len, L. assert (4096 <= za) by (Z.to_euclidean_division_equations; lia).
  repeat split; try lia. unfold wz. apply u64. lia.
Qed.

Lemma m1_out a : ltac2:(tb__ "0|1|
S41S55Z0Va;A2S57Va;S58Z2Z40A2A2A2S42S41S55Vza;Va;A2S57Va;S56Vza;Vlen;A2A2A2A1S40S3S6fQ8A1A1ScfS70Q40Va;A2M0A1VmWc;G0A1A3F_;F_;").
Proof using Hgr Hi.
  intros Ha Hn. pose proof a_facts as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un). unfold m1. rewrite zero_range_at.
  destruct (SysStep.in_range (wz za) (mmap_n (wz len)) (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  apply in_range_spec in E. rewrite Ua, Un, u64 in E by lia. exfalso. exact (Hn E).
Qed.
Lemma m1_in a : ltac2:(tb__ "0|2|
S41S55Vza;Va;A2S57Va;S56Vza;Vlen;A2A2A2S40S3S6fQ8M0A1M1A1ScfS70Q40Va;A2A1S7G1S70G0Z0A2A2A3F_;").
Proof using Hgr Hi.
  intros Ha. pose proof a_facts as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un). unfold m1. rewrite zero_range_at.
  destruct (SysStep.in_range (wz za) (mmap_n (wz len)) (Z_to_bv 64 a)) eqn:E; [reflexivity|]. exfalso.
  assert (E' : SysStep.in_range (wz za) (mmap_n (wz len)) (Z_to_bv 64 a) = true); [|congruence]. apply in_range_spec. rewrite Ua, Un, u64 by lia. exact Ha.
Qed.

Lemma FREE e y : ltac2:(tb__ "0|4|
SecS5S6fQ40M0A1M1G1A2M2Ve;SbG2Sb1Vvm;A1Sb0Vvm;A1A3A3S41S55S71G0ScG1G1Ve;A3A2M3Vy;A2S57Vy;S56G3S71G0SeG1G1Ve;A3A2A2A2A2S42S41S55Vza;Vy;A2S57Vy;S56Vza;Vlen;A2A2A2A1F_;F_;").
Proof using Hgr. intros He Hy. exact (proj2 (proj2 (proj2 Hgr)) e He y Hy). Qed.
Lemma IMG y : ltac2:(tb__ "0|0|
S41S55S68S61A1Vy;A2S57Vy;S67S61A1A2A2S42S41S55Vza;Vy;A2S57Vy;S56Vza;Vlen;A2A2A2A1F_;").
Proof using HLV Hgr.
  intros Hy. destruct (mig_img (lv_MI ia cur L mWc vm HLV) y Hy) as (e & He & Hey). exact (FREE e y ltac:(apply in_app_iff; left; exact He) Hey).
Qed.
Lemma FP y : ltac2:(tb__ "0|0|
S114VL;Vcur;Vy;A3S42S41S55Vza;Vy;A2S57Vy;S56Vza;Vlen;A2A2A2A1F_;").
Proof using HLV Hgr sc.
  intros ([l n] & Hrg & Hy). pose proof (lv_MI ia cur L mWc vm HLV) as LMI. cbn [fst snd] in Hy.
  destruct (footprint_entry_cases' cur l n Hrg) as [[-> ->] | [p ->]].
  - apply IMG. pose proof (mig_ctx LMI) as HCX. cbn [ma_L] in HCX. change (loc_addr L (LCtx 0)) with (ly_ctx L + 0) in Hy. rewrite HCX in Hy.
    cbn [mc_ctx mc_img_lo mc_img_hi C_U] in *. unfold CTX_SIZE in Hy. lia.
  - assert (Hn : 0 <= n).
    { pose proof (fp_mem_range C_U L cur vm p n (mig_vm LMI) (mig_ledger LMI) Hrg) as X.
      destruct (Z_le_dec 0 n); [lia|]. exfalso. change (loc_addr L (LMem p)) with (addr_of L p) in Hy. lia. }
    destruct (proj1 (proj2 (proj2 (proj2 (mig_vm LMI)))) p n Hrg) as (e & He & E1 & E2). cbn [ma_L] in E1, E2.
    change (loc_addr L (LMem p)) with (addr_of L p) in Hy.
    apply (FREE e y ltac:(apply in_app_iff; right; exact He)). lia.
Qed.
Lemma init_cur : st_init_done cur = true.
Proof using HLV.
  pose proof (lv_MI ia cur L mWc vm HLV) as LMI. pose proof (lv_key ia cur L mWc vm HLV) as KK.
  destruct (st_init_done cur) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 (mig_I LMI)) as CX. unfold ctx_ok in CX. cbn [ma_s] in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  unfold keys in KK. rewrite M in KK. destruct KK.
Qed.

Lemma liveX mX (HXo : forall a, 0 <= a < 2 ^ 64 -> ~ (za <= a < za + len) -> mX (Z_to_bv 64 a) = mWc (Z_to_bv 64 a)) : ltac2:(tb__ "0|0|
SdeVia';Vcur;VL;VmX;Vvm;A5").
Proof using HLV Hgr Hi m sc.
  pose proof HLV as [LMI LXr Lhd Lkey Lraw Lro Lgd Lma Lkept Lblk Ltop]. apply set_R_live.
  assert (VIEWS : forall a, 0 <= a < 2 ^ 64 -> ~ (za <= a < za + len) ->
            Glue.rd_of segsU mX (Z_to_bv 64 a) = Glue.rd_of segsU mWc (Z_to_bv 64 a) /\ Glue.wok_of segsU mX (Z_to_bv 64 a) = Glue.wok_of segsU mWc (Z_to_bv 64 a)).
  { intros a Ha Hn. pose proof (HXo a Ha Hn) as E. split; [apply rd_of_mem; exact E | apply wok_of_mem; exact E]. }
  constructor.
  - unfold MInvI. apply (minvG_frame_core C_U (m :: ia_X ia) (ia_R ia) (ia_U ia) cur L _ _ _ _ vm (fun a => za <= a < za + len) LMI LXr).
    + intros a Ha Hn. exact (VIEWS a Ha Hn).
    + intros a Ha Hg. exfalso. apply (IMG a); [cbn [mc_chk_guard mc_img_lo mc_img_hi C_U] in *; lia | exact Ha].
    + intros a. lia.
    + intros a Ha Hf. exact (FP a Hf Ha).
    + intros a Ha Hs. apply (IMG a); [|exact Ha]. unfold static_ng in Hs.
      cbn [mc_libc mc_replaced mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_lock mc_img_lo mc_img_hi C_U] in *. lia.
    + intros Hf. exfalso. rewrite init_cur in Hf. discriminate.
  - exact LXr.
  - exact Lhd.
  - exact Lkey.
  - exact Lraw.
  - intros kk Hkk. rewrite (HXo (0x108cc + kk) ltac:(lia)); [exact (Lro kk Hkk)|]. apply IMG. cbn [mc_img_lo mc_img_hi C_U]. lia.
  - intros j Hj. pose proof (Lgd j Hj) as G. cbn [mc_chk_guard C_U] in *. unfold byteview_of in *.
    rewrite (proj1 (VIEWS (369464 + Z.of_nat j) ltac:(lia) ltac:(apply IMG; cbn [mc_img_lo mc_img_hi C_U]; lia))). exact G.
  - exact Lma.
  -
    intros a Ha Hc1 Hc2 He Hst. pose proof a_facts as (A1 & A2 & _). rewrite <- (Lkept a Ha Hc1 Hc2 He Hst). apply (HXo a Ha).
    exact (client_not_fresh_U (m :: ia_X ia) (ia_R ia) (ia_U ia) cur L _ _ vm LMI LXr a za len (fun e He y Hy => FREE e y He Hy) ltac:(lia) A2 IMG Hc2).
  - exact Lblk.
  - exact Ltop.
Qed.
Lemma live1 : ltac2:(tb__ "0|0|
SdeVia';Vcur;VL;ScfVvm;A5").
Proof using HLV Hgr Hi. exact (liveX m1 m1_out). Qed.
Lemma HE1 : ltac2:(tb__ "0|0|
S66S65S165S48ScfA2S6fQ40A1S6L_;A2S69S61A1U4Se3Via;A1A4").
Proof using HE HLV Hgr Hi.
  intros j Hj. pose proof (HE j Hj) as E. rewrite errno_U in *. unfold byteview_of in *.
  rewrite (rd_of_mem segsU m1 mWc); [exact E|]. apply m1_out; [lia|]. apply IMG. cbn [mc_img_lo mc_img_hi C_U]. lia.
Qed.

Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|0|
S41S55S16cVx;A1Vsc;A2S55Vsc;S16bVx;A1A2A2").
Variable Q : assn.

Hypothesis LEAF_T : ltac2:(tb__ "0|0|
S87S28SecS87R2SfdVx;A1A3Sf1SddVia';ScfA2R2A2VTR;VkB;Sf0S48Sd0S8cR4A1R3A4VQ;A3F_;F_;Frho';FLf;").

Lemma aidx_linkT rhoV : ltac2:(tb__ "0|0|
Sf1SddVia';ScfA2VrhoV;A2Sc5Se2Via';A1Se1Via';A1Sf9A3S40S6fQ40A1S2fVrhoV;SffA2S2fVrhoV;S11Pa1A1A2A3F_;F_;").
Proof using Hi.
  intros Hag Hf. pose proof Hi' as Hi2. pose proof (iplan_range ia' Hi2) as [CR _]. pose proof (iaidx_range ia' Hi2) as AR. pose proof (iqdiv_range ia' Hi2) as QR.
  rewrite (EVw ia' m1 rhoV e_aiT Hag eq_refl eq_refl), (EVw ia' m1 rhoV (SVar 161%positive) Hag eq_refl eq_refl). f_equal.
  cbn [zholds zcond f_lt] in Hf. rewrite (zs176 ia' Hi2), (zs162 ia' Hi2) in Hf. apply Z.ltb_lt in Hf.
  unfold e_aiT. rewrite (ze_alu ia'), (zs176 ia' Hi2), (zs161 ia' Hi2), (ze_lit ia'). cbn [zalu].
  unfold iaidx, mm_aidx. change (4096 - UNIT) with 4080. fold (iqdiv ia').
  replace (icnt ia' - 1 <? iqdiv ia' - 1) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (icnt ia' - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  Z.to_euclidean_division_equations; lia.
Qed.
Lemma aidx_linkF rhoV : ltac2:(tb__ "0|0|
Sf1SddVia';ScfA2VrhoV;A2Sc5Se2Via';A1Se1Via';A1S26Sf9A1A3S40S6fQ40A1S2fVrhoV;SfeA2S2fVrhoV;S11Pa1A1A2A3F_;F_;").
Proof using Hi.
  intros Hag Hf. pose proof Hi' as Hi2. pose proof (iplan_range ia' Hi2) as [CR _]. pose proof (iaidx_range ia' Hi2) as AR. pose proof (iqdiv_range ia' Hi2) as QR.
  rewrite (EVw ia' m1 rhoV e_aiF Hag eq_refl eq_refl), (EVw ia' m1 rhoV (SVar 161%positive) Hag eq_refl eq_refl). f_equal.
  cbn [zholds zcond f_lt] in Hf. rewrite (zs176 ia' Hi2), (zs162 ia' Hi2) in Hf. apply Bool.not_true_is_false in Hf. apply Z.ltb_ge in Hf.
  unfold e_aiF. rewrite !(ze_alu ia'), !(zs162 ia' Hi2), (zs161 ia' Hi2), !(ze_lit ia'). cbn [zalu].
  unfold iaidx, mm_aidx. change (4096 - UNIT) with 4080. fold (iqdiv ia').
  replace (icnt ia' - 1 <? iqdiv ia' - 1) with false by (symmetry; apply Z.ltb_ge; lia).
  set (q := iqdiv ia') in *. replace (-1 mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity. rewrite !(Z.mod_small q) by lia.
  destruct (Z.eq_dec q 0) as [E0|NE].
  - rewrite E0. vm_compute. reflexivity.
  - replace (q - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
    replace ((q + (2 ^ 64 - 1)) mod 2 ^ 64) with (q - 1) by (Z.to_euclidean_division_equations; lia).
    rewrite !(Z.mod_small (q - 1)) by lia.
    replace (q <? q - 1) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (((0 + (2 ^ 64 - 1)) mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 64) by reflexivity.
    replace ((0 + (2 ^ 64 - 1)) mod 2 ^ 64) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma divu_link rhoV : ltac2:(tb__ "0|0|
Sf1SddVia';ScfA2VrhoV;A2S40S6fQ40A1S2fVrhoV;S100A2S2fVrhoV;S11Pa2A1A2A3F_;").
Proof using Hi.
  intros Hag. pose proof Hi' as Hi2. pose proof (isize_range ia' Hi2) as SR. pose proof (iqdiv_range ia' Hi2) as QR.
  assert (E191 : rw rhoV 191%positive = Z_to_bv 64 (isize ia')).
  { rewrite (proj1 Hag 191%positive eq_refl). reflexivity. }
  assert (E162 : rw rhoV 162%positive = Z_to_bv 64 (iqdiv ia')).
  { rewrite (proj1 Hag 162%positive eq_refl). reflexivity. }
  unfold e_divu. cbn [eval]. rewrite E162, E191. unfold mul_div. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 (isize ia')) by (change (bv_modulus 64) with (2 ^ 64); lia).
  replace (isize ia' =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small; [unfold iqdiv; reflexivity | | |]; change (bv_modulus 64) with (2 ^ 64); unfold iqdiv in *; lia.
Qed.

Lemma ZF_T : ltac2:(tb__ "0|0|
S106S14Sc5Se2Via';A1Se1Via';A1A2S138A3").
Proof using Hgr Hi len sc.
  pose proof a_facts as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un). pose proof Hi' as Hi2.
  assert (E187 : zeval (zr2 ia') (zl2 ia') (v 187) = za).
  { rewrite (ze187 ia' Hi2). cbn [ia_Rz ia' set_R]. apply Z.mod_small. lia. }
  assert (E177 : zeval (zr2 ia') (zl2 ia') (v 177) = len) by exact (ze177 ia' Hi2).
  unfold F_T. repeat constructor; cbn [zholds zcond]; rewrite ?(ze_alu ia'), ?E187, ?E177, ?(ze_lit ia'); cbn [zalu]; rewrite ?Z.mod_small by lia; try lia;
    try (rewrite (zr2_187 ia' Hi2); cbn [ia_Rz ia' set_R]; change (2 ^ 12) with 4096; rewrite (Z.mod_small za (2 ^ 64)) by lia; lia);
    try (change (18446744073709551615 mod 2 ^ 64) with 18446744073709551615; intros E; apply Z.eqb_eq in E; lia).
Qed.

Lemma hold_map rhoT ms : ltac2:(tb__ "0|0|
Sf1SddVia';ScfA2VrhoT;A2S3fS48Vms;A2S39S48VrhoT;S109Vms;ScfA2S139A4F_;F_;").
Proof using Hgr Hi.
  intros HagT Hrom. pose proof a_facts as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un).
  assert (E187 : eval rhoT (v 187) = wz za).
  { cbn [eval v]. rewrite (proj1 HagT 187%positive eq_refl). cbn [rho2 rw]. unfold rw2. cbn [rw2v Z.eqb Pos.eqb ia' set_R ia_Rz]. unfold wz. f_equal. apply Z.mod_small. lia. }
  assert (E177 : eval rhoT (v 177) = wz len) by (cbn [eval v]; rewrite (proj1 HagT 177%positive eq_refl); reflexivity).
  unfold obj_holds, O_map, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite E187, Ua, soff_lit_small by lia.
  unfold soff. rewrite E177. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold wz. rewrite u64, toS_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. apply wview_of_views; unfold Glue.wok_of, Glue.rd_of; rewrite (m1_in (za + off) ltac:(lia)); [reflexivity | eexists; reflexivity]. }
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. rewrite (rd_with_mem segsU ms m1 _ Hrom). unfold Glue.rd_of. rewrite (m1_in (za + off) ltac:(lia)). reflexivity.
Qed.

Theorem gen_T rhoT : ltac2:(tb__ "0|1|
Sf1SddVia';ScfA2VrhoT;A2S40S6fQ40A1S1eVrhoT;S23Sb3Vx;A1M0A1A2S63Vza;A1A3VTR;VkB;Sf0S48Sd0S128G0A1VrhoT;A4VQ;A3F_;F_;").
Proof using HLV Hgr Hi HkB Hx LEAF_T RR.
  intros HagT Enx. pose proof a_facts as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un). pose proof Hi' as Hi2. pose proof (iok_sc ia Hi) as SC.
  pose proof live1 as HLV1. pose proof HLV as [LMI LXr Lhd Lkey Lraw Lro Lgd Lma Lkept Lblk Ltop].
  destruct (EK_objs x) as [stkc EO].
  assert (METAFP : forall y, addr_of L m <= y < addr_of L m + 40 -> in_footprint L cur y).
  { intros y Hy. destruct (key_area (m :: ia_X ia) (ia_R ia) (ia_U ia) cur (mig_I LMI) m Lkey) as (ar & k & Har & Hk & Em).
    exists (e_area ar). split; [exact (e_area_In cur ar Har)|]. unfold e_area. cbn [fst snd].
    rewrite Em in Hy. unfold addr_of, loc_addr in *. destruct ar; cbn [padd prid poff] in *. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia. }

  apply (trr_pre RR (SymSoundR.SP segsU K1 (SKTo x) rhoT)).
  { intros [tr [ms md]] [Hsm HK]. split; [|exact HK].
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))) as Hrom.
    assert (E187 : eval rhoT (v 187) = wz za).
    { cbn [eval v]. rewrite (proj1 HagT 187%positive eq_refl). cbn [rho2 rw]. unfold rw2. cbn [rw2v Z.eqb Pos.eqb ia' set_R ia_Rz]. unfold wz. f_equal. apply Z.mod_small. lia. }
    assert (E177 : eval rhoT (v 177) = wz len).
    { cbn [eval v]. rewrite (proj1 HagT 177%positive eq_refl). reflexivity. }
    assert (RM : obj_range rhoT O_map = (za, za + len)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_map. cbn [ob_base ob_lo ob_hi]. rewrite E187, Ua, soff_lit_small by lia.
      unfold soff. rewrite E177. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold wz. rewrite u64, toS_small by lia. f_equal; lia. }
    assert (DSd : forall d, In d (dsM23 x) -> DS2 ia' d).
    { intros d Hd. pose proof (proj1 (forallb_forall _ _) (dsM23_checks x) d Hd) as C. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
      split; [exact C1|]. split; [| exact (dcond2b_sound _ _ _ d Hx C3)].
      apply forallb_forall. intros [[off w] e] Hc. unfold od2_semb in C2. pose proof (proj1 (forallb_forall _ _) C2 e (dcells2_svs sc d off w e Hc)) as Y.
      unfold sv_sem in Y. apply andb_prop in Y as [_ Y]. exact Y. }
    pose proof (m_R ia Hi) as MR. top_ranges.
    apply (smatch_extend_objs segsU rhoT (S_ret_fresh (EK x)) tr ms md [O_map] (ss_next (S_ret_fresh (EK x))) Hsm (SKTo_swf x)).
    - constructor; [|constructor]. rewrite (proj2 (proj2 HagT)). apply hold_map; [exact HagT | exact Hrom].
    - constructor; [|constructor]. unfold S_ret_fresh, S_after. cbn [ss_objs]. rewrite EO. constructor.
      +
        pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts). cbn [fst snd cfg_ms cfg_model ss_objs ss_facts S_ret_fresh S_after] in Hall, Hfacts. rewrite EO in Hall.
        assert (HF3 : Forall (SymState.holds rhoT) ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D)).
        { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hfacts).
          apply (facts_incl_sound ([F_sp_aligned; F_sp_high AS_D] ++ F_depth AS_D ++ F_J)); [exact (EK_facts x)|]. rewrite app_assoc. apply in_app_iff. left. exact Hp. }
        pose proof (window_facts segsU rhoT ms AS_D (mkObj (SVar 10) (SVar 15) (SLit 0) stkc DUnknown) ltac:(unfold AS_D; lia) HF3 eq_refl eq_refl (Forall_inv Hall)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).

        assert (TOPW : topL L <= bv_unsigned (rw rhoT 10%positive) + toS 64 (bv_unsigned (rw rhoT 15%positive))).
        { rewrite (proj1 HagT 10%positive eq_refl), (proj1 HagT 15%positive eq_refl). exact (iok_sp_high ia Hi). }
        rewrite RM. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite WS, soff_lit_small by lia.
        unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
      + apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). rewrite RM.
        rewrite (rngD ia' Hi2 m1 d rhoT (DSd d Hd) HagT).
        apply disjoint_of_pointwise. intros y Hy. unfold dlo2, dhi2, od2_range, od2_rangeP in Hy.
        destruct d; unfold zA in Hy; cbn [fst snd mc_tp C_U ia_sc ia_m ia_L ia' set_R] in Hy; try (apply IMG; cbn [mc_img_lo mc_img_hi C_U]; unfold sc in *; lia).

        apply FP. apply METAFP. unfold L, m. lia.
    - cbn [pairwise_disjoint]. split; [constructor | exact I]. }

  apply (trr_pre RR (SymSoundR.SP segsU K1 (STx x) (setp rhoT []))).
  { intros w HSP. apply (relinkp segsU K1 (setp rhoT []) (SKTo x) (STx x) w [] [(SVar (ss_next (EK x)), v 187)] F_T (SKTo_vars x) (STx_swf x) (sdT x)).
    - unfold diffs_ok. constructor; [|constructor]. cbn [fst snd eval setp set_par rw]. rewrite Enx. cbn [eval v].
      pose proof (proj1 HagT 187%positive eq_refl) as E. cbn [rho2 rw] in E. rewrite E. unfold rw2. cbn [rw2v Z.eqb Pos.eqb ia' set_R ia_Rz]. unfold wz. f_equal. symmetry. apply Z.mod_small. lia.
    - exact (ZFw ia' m1 (setp rhoT []) F_T ltac:(exact HagT) FT_vars FT_sup ZF_T).
    - exact HSP. }

  pose proof (STx_next x) as [Enext Hnx].
  apply ((trr_run RR) kB 500%nat CUTS_K K1 (STx x) (LT x) (setp rhoT []) Q HkB (runT x) (STx_lenient x) (K_v_impl Kc vm1)).
  intros Lf rho' Hin Hab. rewrite LT_single in Hin. destruct Hin as [<-|[]]. cbn [lf_state].
  assert (Hag' : agrees (rho2 ia' m1) rho') by (eapply agrees_below; [exact HagT | exact Hab | rewrite Enext; exact Hnx]).

  apply (trr_pre RR (SymSoundR.SP segsU K1 (SVx x) (setp rho' []))).
  { intros w HSP. apply (relinkp segsU K1 (setp rho' []) (LTc x) (SVx x) w [] [(e_divu, SVar 162%positive)] [] (LTc_vars x) (SVx_swf x) (sdV x)).
    - unfold diffs_ok. constructor; [|constructor]. cbn [fst snd]. apply divu_link. apply (WalkSeg.agrees_setp (rho2 ia' m1) rho' []); [exact Hag' | reflexivity].
    - constructor.
    - exact HSP. }

  apply ((trr_run RR) kB 500%nat CUTS_K K1 (SVx x) (LV x) (setp rho' []) Q HkB (runV x) (SVx_lenient x) (K_v_impl Kc vm1)).
  intros Lf2 rho2' Hin2 Hab2.
  assert (Hag2 : agrees (rho2 ia' m1) rho2').
  { eapply agrees_below; [| exact Hab2 | rewrite SVx_next; exact Hnx]. apply (WalkSeg.agrees_setp (rho2 ia' m1) rho' []); [exact Hag' | reflexivity]. }

  apply (trr_pre RR (SymSoundR.SP segsU K1 (SWx x) (setp rho2' []))).
  { intros w HSP. pose proof (WalkSeg.agrees_setp (rho2 ia' m1) rho2' [] Hag2 eq_refl) as HagS.
    rewrite LV_pair in Hin2. destruct Hin2 as [<-|[<-|[]]]; cbn [lf_state] in HSP |- *.
    - apply (relinkp segsU K1 (setp rho2' []) (LVc x 0) (SWx x) w [] [(e_aiT, SVar 161%positive)] [] (LVc_vars x 0 ltac:(lia)) (SWx_swf x) (sdW0 x)); [| constructor | exact HSP].
      unfold diffs_ok. constructor; [|constructor]. cbn [fst snd]. apply (aidx_linkT _ HagS).
      exact (leaf_factw ia' m1 K1 rho2' (LVc x 0) w f_lt Hag2 HSP (existsb_In _ _ (LV0_fact x)) eq_refl eq_refl).
    - apply (relinkp segsU K1 (setp rho2' []) (LVc x 1) (SWx x) w [] [(e_aiF, SVar 161%positive)] [] (LVc_vars x 1 ltac:(lia)) (SWx_swf x) (sdW1 x)); [| constructor | exact HSP].
      unfold diffs_ok. constructor; [|constructor]. cbn [fst snd]. apply (aidx_linkF _ HagS).
      exact (leaf_factw ia' m1 K1 rho2' (LVc x 1) w (SPNot f_lt) Hag2 HSP (existsb_In _ _ (LV1_fact x)) eq_refl eq_refl). }

  apply ((trr_run RR) kB 500%nat CUTS_K K1 (SWx x) (LW x) (setp rho2' []) Q HkB (runW x) (SWx_lenient x) (K_v_impl Kc vm1)).
  intros Lf3 rho3 Hin3 Hab3. apply (LEAF_T Lf3 rho3 Hin3).
  eapply agrees_below; [| exact Hab3 | rewrite SWx_next; exact Hnx].
  apply (WalkSeg.agrees_setp (rho2 ia' m1) rho2' []); [exact Hag2 | reflexivity].
Qed.
End T.
End Mal_agrp_T.

Module Mal_agrp_NCdefs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs.

Import ListNotations.
Open Scope Z_scope.

Definition SNr0 : sstate := ltac2:(tb__ "0|0|
S21S2cSa0A1S33Sa0A1S31Sa0A1S30Sa0A1S34Sa0A1S0S19Sa1S2S19A1A3S27Sa0A1Sa2SaA9").
Lemma SNr0_swf : swf SNr0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition factsN : list sprop := ltac2:(tb__ "0|0|
SbS14S27Sa0A1S0S14S17S13Z1000A1S11PaA1A2S0S14S1aS4dS13N1b0A1S11PfA1A3S2S14A1A3A3A3").
Definition SNr : sstate := ltac2:(tb__ "0|0|
S21S2cSa0A1S33Sa0A1S31Sa0A1S30Sa0A1S34Sa0A1S0S19Sa1S2S19A1A3S122Sa2SaA9").
Lemma SNr_swf : swf SNr = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sd_SNr : ltac2:(tb__ "0|4|
S40S3S5S4S5S12S12A2M0A1M1S4S14A1M2A2M3A1S108S121S11cA2S7G3S1G1G2S2G0A1S0S14S17S13Z1000A1S11PaA1A2S0S14S1aS4dS13N1b0A1S11PfA1A3S2S14A1A3A3A4A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some ([], [SPUle (SLit 4096) (SVar 10); SPBranch BC_GE (SLit (-432)) (SVar 15)]))). Qed.

Definition SNS : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast SNr [XSplit 0 (SLit (-144))])) in exact x).
Lemma SNS_ok : ltac2:(tb__ "0|0|
S40S3S1bA1Sa4S11cS0Sa3Sa7U0S13N90A1A2S2Sa3A1A3A2S7S1bS11bA2A3").
Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Lemma SNS_swf : swf SNS = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition EvN : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.unbase_obj_at_fast SNS 0 (-144))) in exact x).
Lemma EvN_ok : ltac2:(tb__ "0|0|
S40S3S1bA1S177S11bU0N90A3S7S1bS118A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition sN : wsub := ltac:(let x := eval vm_compute in (infer_sub 10 EvN (Pre_as IEC_U)) in exact x).
Definition RcN : list sobj := ltac:(let x := eval vm_compute in (optR (entails_fr EvN (Pre_as IEC_U) sN)) in exact x).
Lemma entN : ltac2:(tb__ "0|1|
S40S3S4S19A1M0A1S176S118S79S72A1S11aA3S7G0S119A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list sobj)) (Some RcN)). Qed.
Lemma chkN : ltac2:(tb__ "0|0|
S40S8S12dS118S79S72A1S11aS119S0S1bS78S72A1S0S1bS77S72A1S2S1bA1A3A3A5S6A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition TfailN : sstate := ltac:(let x := eval vm_compute in (T_after EvN sN RcN (L_as_fail IEC_U)) in exact x).
Definition TokN : sstate := ltac:(let x := eval vm_compute in (T_after EvN sN RcN (L_as_ok IEC_U)) in exact x).
Lemma TfailN_eq : ltac2:(tb__ "0|0|
S40S1bS135S118S11aS119S78S72A1A4S11dA3"). Proof. vm_cast_no_check (@eq_refl sstate TfailN). Qed.
Lemma TokN_eq : ltac2:(tb__ "0|0|
S40S1bS135S118S11aS119S77S72A1A4S11eA3"). Proof. vm_cast_no_check (@eq_refl sstate TokN). Qed.
Definition SNfail : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TfailN [XRebase 0; XMerge 0])) in exact x).
Lemma SNfail_ok : ltac2:(tb__ "0|1|
S40S3S1bA1Sa4S11dS0Sa3Sa6U0M0A1S0Sa3Sa5G0A1S2Sa3A1A3A3A2S7S1bS11fA2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.
Definition SNok : sstate := ltac:(let x := eval vm_compute in (optS (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.apply_xforms_fast TokN [XRebase 0; XMerge 0])) in exact x).
Lemma SNok_ok : ltac2:(tb__ "0|1|
S40S3S1bA1Sa4S11eS0Sa3Sa6U0M0A1S0Sa3Sa5G0A1S2Sa3A1A3A3A2S7S1bS120A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast.fast_lit. Qed.

Lemma impN_VRES : ltac2:(tb__ "0|0|
S40S12S10cS130S11aS49S77S72A1P12cA4SbdA2S11P136A1A3").
Proof. vm_cast_no_check (@eq_refl sv (SVar 310)). Qed.
Lemma RcN_eq : ltac2:(tb__ "0|0|
S40S4S19A1S119S0S19S107S19U1S32S118A1Sa1A4S2S19A1A3A3"). Proof. reflexivity. Qed.
End Mal_agrp_NCdefs.
