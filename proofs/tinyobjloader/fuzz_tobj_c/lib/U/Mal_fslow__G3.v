(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "option"; "nat"; "cons"; "nil"; "Some"; "app"; "None"; "false"; "fst"; "snd"; "unit"; "negb"; "option_map"; "tt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sstate"; "rw"; "sobj"; "SVar"; "rm"; "SLit"; "ss_next"; "agree_below"; "smatch"; "sprop"; "SAlu"; "ss_objs"; "ss_pc"; "swf"; "ss_facts"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "mkSS"; "reg_sv"; "rl"; "SPBranch"; "SPUle"; "image_byte"; "obj_holds"; "obj_range"; "ss_lenient"; "SPNot"; "enc_bytes"; "mkVal"; "ranges_disjoint"; "ro_addr"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_regs"; "ss_resv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "pow"; "of_nat"; "opp"; "modulo"; "lor"; "mul"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "ameta"; "astate"; "frame"; "st_init_done"; "fr_n"; "RkMap"; "rg_kind"; "rg_live"; "rkind"; "am_sc"; "rg_len"; "am_freed"; "am_maplen"; "am_mem"; "page_round"; "prid"; "am_next"; "am_prev"; "kreq"; "NEST_FUEL"; "nontrivial_free"; "AREA_HDR"; "FUser"; "METAS_PER_AREA"; "META_SIZE"; "am_avail"; "am_last"; "bit"; "fkind"; "fr_kind"; "free"; "ones"; "padd"; "st_areas"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "VmMaps"; "TASK_SIZE"; "map_has"; "page_size"; "vm_maps"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "addr_of"; "mc_errno"; "mc_lock"; "mc_size_classes"; "mc_ctx"; "mc_tp"; "C_U"; "mc_replaced"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_libc"; "mc_med_cnt_tab"; "mc_need_locks"; "mc_small_cnt_tab"; "topL"; "mc_img_hi"; "mc_img_lo"; "size_classes_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "mkMA"; "MA"; "ma_L"; "ma_blocks"; "MInv"; "ma_owned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "call_checkP"; "J_ofP"; "agree_vals"; "call_linkP"; "import_okP"; "import_post"; "state_vars_all"; "import_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "SP"; "jpred"; "stableJ"; "ok_frame"; "liftK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs"; "fvar"; "FS_NEXT"; "reg"; "D_ret"; "O_lock"; "O_sct"; "F_win_facts"; "idx_of"; "O_errnoF"; "fs_cutsX"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "wseg_addr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.FP"; "C"; "E"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "U0"; "layout"; "frame_ptr"; "region_of"; "usedX"; "CTX_SIZE"; "ly_reg"; "active_hd"; "yields"; "MCell"; "VSec"; "frames"; "mcell"; "CTX_secret"; "LCtx"; "LMem"; "alloc_owned"; "image"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView"; "zP"; "rho1"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "Pre_freeI"; "EC_U"; "J_free_preT"; "L_free"; "JL_free"; "V_DEPTH"; "mem_kept"; "vm_insensitive"; "MInvR"; "V_RES"; "ok_sideK"; "top_high"; "mem_kept_owned"; "alloc_static"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease"; "rs1"; "am1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I"; "n"; "rsv"; "slow_case"; "fixed7"; "h3_of"; "has_sct"; "wins"; "S1"; "zEnd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow_C.CallSite"; "x0"; "K1"; "errno_word"; "ret_facts"; "K0"; "nt_in_facts"; "nt_out_facts"; "unmap_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "with_mem"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "RsCut"; "instr_at"; "lf_state"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.Main"; "QF"; "okKs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow_C"; "nt_out_facts"; "nt_in_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "mmap_n"; "mmap_nZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "ok_pframe"; "ok_pframeJ"; "smatch_pending"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XRebase"; "XSplit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow"; "fs_ff"; "fs_ret_call"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs.RP"; "c"; "e"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC"; "LN"; "V_LEN"; "PreN"; "hdrX"; "V_BASE"; "addOF"; "XcG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.DrvInst"; "KcD"; "XFd"; "XPd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.DrvInstS"; "KcS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "JLd_free"; "drvN"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "L_nt"; "NTE_U"; "NTE_U"; "Pre_nt"; "V_RES1"; "magree"; "xzomb"; "ne_entry"; "nt_stack"; "ne_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS"; "JLdS_free"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow"; "rsv32_stmt"; "JL_ntRY"; "JL_ntR"; "nt_contractR"; "nt_contractR_P"; "nt_contractR_d"; "nt_contractR_d_P"; "nt_contractR_ex";
"nt_contractR_ex_P"; "nt_contractR_exd"; "nt_contractR_exd_P"; "J_free_drvST"; "J_nt_preR"; "J_nt_preRG"; "XFd"; "XPd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap"; "km_s'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast"; "ff_nontrivial_free"; "ff_ctx"; "ff_entry"; "ff_libc"; "ff_lockword"; "ff_sctab"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow_C.CallSite.T"; "R2"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib"; "inclb"; "ro_view"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quickE"; "J_free_drvT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow.NTR"; "JL_ntR"; "JL_ntRY"; "J_nt_preR"; "J_nt_preRG"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "unbase_obj_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface"; "L_SIZECLASSES"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel"; "frame_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reserved_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_T"; "QF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "ltb"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require Stdlib.Logic.FunctionalExtensionality.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlowYield.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_fslow_C.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_I2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Local Notation SP := SymSoundR.SP.
Local Notation wz := (Z_to_bv 64).

Section Gen.
Variables (segs : list Segment) (C : mconsts).
Hypothesis HSI : statics_in_image C.
Hypothesis HSD : ltac2:(tb__ "0|d|
S6S4S0S43S85VC;A1M0R1A2S45R1S44G0SccA2A2A2S0S43S82VC;A1M1R1A2S45R1S44G1Z4M2A2A2A2A2S0S2S0S43S8cVC;A1M3R2A2S45R2S44G3Z38A2A2A2A1S0S2S0S43S88VC;A1M4R2A2S45R2S44G4G2A2A2A2A1S0S2S0S43S83VC;A1M5R2A2S45R2S44G5G2A2A2A2A1S0S2S0S43S84VC;A1M6R2A2S45R2S44G6Z60A2A2A2A1S0S2S0S43S8fVC;A1M7R2A2S45R2S44G7Z1bA2A2A2A1S0S2S0S43S8dVC;A1M8R2A2S45R2S44G8G2A2A2A2A1S0S2S0S43S8bVC;A1M9R2A2S45R2S44G9Z20A2A2A2A1S0S2S0S43S8aVC;A1MaR2A2S45R2S44GaZ8MbA2A2A2A1S2S0S43S89VC;A1McR2A2S45R2S44GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

Lemma alloc_owned_lowG : ltac2:(tb__ "0|1|
S8S4eA1SdSaS4eS6A2A1S6S6F_;S9aS7bQ40A1M0SdS7bQ8A1A1F_;G0SbF_;S75S6SbeVC;R8R7R6R5R4R3R2A8Sd7S9bR6A1S98R6A1R2A3S0S45Z0R3A2S45R3S90S9bR7A1A1A2A2F_;F_;Fx;Fvm;Fwok;Frd;FA;FU;FR;FX;").
Proof using HSI.
  intros X R U [s0 L0] rd wok vm x HM [([l k] & He & Hx) _]. cbn [ma_s ma_L fst snd] in *.
  pose proof HSI as X0. unfold statics_in_image in X0. cbn beta zeta in X0. unfold CTX_SIZE, PGSZ, UNIT in X0.
  pose proof (mig_layout HM) as HL. pose proof HL as (_ & _ & _ & POS). destruct (POS _ He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd ma_s ma_L] in P1, P2.
  destruct (footprint_entry_cases s0 l k He) as [[-> ->] | [q ->]].
  - unfold loc_addr in Hx. pose proof (mig_ctx HM) as CX. cbn [ma_L] in CX. rewrite CX in Hx. unfold CTX_SIZE in Hx. lia.
  - pose proof (FpLaws.fp_mem_range C L0 s0 vm q k (mig_vm HM) (mig_ledger HM) He) as FR. unfold addr_of in FR. destruct q as [qr qo]. cbn [loc_addr] in Hx, FR.
    unfold PGSZ in FR. destruct (Z_le_dec 0 k); [specialize (FR ltac:(lia)); lia | lia].
Qed.

Lemma MInvI_rm_ext : ltac2:(tb__ "0|4|
S8S4eA1SdSaS4eS6A2A1S6S6F_;S9aS7bQ40M0A1M1SdS7bQ8A1A1M2F_;G1G2Fx;S75SbeVC;R7R6R5R4Sb9Vsegs;R3A2SbaVsegs;R3A2R1A8S170R8S98R5A1A2S1SbS53S98R6A1A1ScA3S6S0S43Z0R1A2S45R1S47Z2Z40A2A2A2S45R2S90S9bR9A1A1A2S1G2R8S7cG0R3A2M3A1R9G3A1A3F_;F_;Fa;SbeVC;RbRaR9R8Sb9Vsegs;R6A2SbaVsegs;R6A2R5A8F_;F_;F_;F_;Fvm;Fm2;Fm1;FA;FU;FR;FX;").
Proof using HSD HSI.
  intros X R U [s0 L0] m1 m2 vm HM HX Hi Hag. top_ranges.
  pose proof HSI as X0. unfold statics_in_image in X0. cbn beta zeta in X0. unfold CTX_SIZE, PGSZ, UNIT in X0.
  assert (AG : forall a, 0 <= a < 2 ^ 64 -> a < topL L0 ->
            byteview_of (rd_of segs m2) (wok_of segs m2) a = byteview_of (rd_of segs m1) (wok_of segs m1) a
            /\ byteview_of (rd_of segs m2) (fun _ => true) a = byteview_of (rd_of segs m1) (fun _ => true) a).
  { intros a Ha Hl. unfold byteview_of, rd_of, wok_of. rewrite (Hag a Ha Hl). split; reflexivity. }
  unfold MInvI.
  refine (minv_postGX C (Inv X R U) (Inv X R U) s0 s0 L0 L0 (rd_of segs m1) (rd_of segs m2) (wok_of segs m1) (wok_of segs m2) vm vm
            HM (mig_I HM) (mig_bounded HM) (mig_layout HM) eq_refl eq_refl (mig_vm HM) (mig_ledger HM) eq_refl
            (fun a => topL L0 <= a) (fun a => Z_le_dec (topL L0) a) [] _ _ _ _ _ _ _ _ _ _ _ HSI _ _ _ (mig_maps HM)); cbn [ma_s ma_L] in *.
  - intros e He. left. exact He.
  - intros e _ _. reflexivity.
  - intros b _. reflexivity.
  - intros e a [].
  - intros a Ha NT. apply AG; lia.
  - intros cl Hcl (k & Hk & T). exfalso.
    pose proof (Zones2.cell_in_footprintI X R U s0 L0 (mig_I HM) HX cl Hcl) as (e & He & [I1 I2]). unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
    assert (OW : loc_addr L0 (mc_loc cl) + Z.of_nat k < topL L0).
    { destruct e as [l len]. cbn [fst snd] in *.
      destruct (footprint_entry_cases s0 l len He) as [[-> ->] | [q ->]].
      - replace (loc_addr L0 (LCtx 0)) with (ly_ctx L0 + 0) in I1, I2 by reflexivity. pose proof (mig_ctx HM) as CX. cbn [ma_L] in CX. rewrite CX in I1, I2. unfold CTX_SIZE in *. lia.
      - pose proof (mig_layout HM) as (_ & _ & _ & POS). destruct (POS _ He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd] in P1, P2.
        pose proof (FpLaws.fp_mem_range C L0 s0 vm q len (mig_vm HM) (mig_ledger HM) He) as FR. unfold addr_of in FR.
        destruct (Z_le_dec 0 len); [specialize (FR ltac:(lia)); lia | lia]. }
    lia.
  - intros a Ha T OW. exfalso. pose proof (alloc_owned_lowG X R U (mkMA s0 L0) _ _ vm a HM OW) as AOL. cbn [ma_L] in AOL. lia.
  - intros cl Hcl _. auto.
  - intros cl Hcl. exact (Zones2.cell_spanI X R U s0 L0 (mig_I HM) HX (mig_layout HM) cl Hcl).
  - intros a Ha. exact (Zones2.owned_spanI s0 L0 (mig_layout HM) a Ha).
  - intros cl Hcl. exact (Zones2.cell_w_posI s0 cl Hcl).
  - intros a T Himg. exfalso. lia.
  - exact HSD.
  - intros Hf. exfalso. rewrite Hi in Hf. discriminate Hf.
Qed.
End Gen.

Section CallSite.
Variables (segs : list Segment) (C : mconsts) (c : fs_consts) (e : ntentry_consts).
Hypothesis HSI : statics_in_image C.
Hypothesis Hrc : ltac2:(tb__ "0|2|
S4S43S44S85VC;A1M0SccA2S88VC;A1M1A2S43S44G1Z4A2G0A2A2").
Hypothesis HCc : ltac2:(tb__ "0|1|
S0S1S6S158S124Vc;A1M0A1S85VC;A1A3S0S1S6S44S15aG0A1Z3A2S8eVC;A1A3S0S1S6S15bG0A1S83VC;A1A3S1S6S15cG0A1S84VC;A1A3A2A2A2").
Hypothesis NLW : ltac2:(tb__ "0|0|
S1SbSbbVsegs;S7cQ40S8eVC;A1A2A2ScA3").
Hypothesis SCT : ltac2:(tb__ "0|4|
S6S0S43Z0M0R1A2S45R1Z60A2A2S0S1SbS3dVsegs;S7cQ40S44S84VC;A1R2A2A2M1A2ScA3S1SdS7bQ8M2A1M3A1S35Vsegs;G1A2S11G3SddG3S4dR2A1SdbS6G3S7cG2A1S93A4S7cG2G0A2A4A2A3A2F_;Fkk;").
Hypothesis HTP : ltac2:(tb__ "0|1|
S0S43Z1000S86VC;A1M0A2S0S1S6S4aG0Z4A2Z0A3S45G0S47Z2Z40A2A2A2A2").
Hypothesis HORD : ltac2:(tb__ "0|2|
S0S43S44S84VC;A1Z60A2S8eVC;A1M0A2S0S43S44G0Z1A2S83VC;A1M1A2S43S44G1Z4A2S85VC;A1A2A2A2").
Hypothesis WSEG : ltac2:(tb__ "0|2|
S7bQ40M0A1S1SbSbbVsegs;R1A2ScA3S0S43S92VC;A1S7aG0R2A2M1A2S45G1S91VC;A1A2A2F_;Fw;").
Hypothesis HSD : ltac2:(tb__ "0|d|
S6S4S0S43S85VC;A1M0R1A2S45R1S44G0SccA2A2A2S0S43S82VC;A1M1R1A2S45R1S44G1Z4M2A2A2A2A2S0S2S0S43S8cVC;A1M3R2A2S45R2S44G3Z38A2A2A2A1S0S2S0S43S88VC;A1M4R2A2S45R2S44G4G2A2A2A2A1S0S2S0S43S83VC;A1M5R2A2S45R2S44G5G2A2A2A2A1S0S2S0S43S84VC;A1M6R2A2S45R2S44G6Z60A2A2A2A1S0S2S0S43S8fVC;A1M7R2A2S45R2S44G7Z1bA2A2A2A1S0S2S0S43S8dVC;A1M8R2A2S45R2S44G8G2A2A2A2A1S0S2S0S43S8bVC;A1M9R2A2S45R2S44G9Z20A2A2A2A1S0S2S0S43S8aVC;A1MaR2A2S45R2S44GaZ8MbA2A2A2A1S2S0S43S89VC;A1McR2A2S45R2S44GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").

Hypothesis ERRIMG : ltac2:(tb__ "0|3|
S6S0S43Z0R1A2S45R1Z4A2A2S0S3S7bQ8A1M0G0S1SdG0A1S35Vsegs;S7cQ40M1S44S82VC;A1M2R3A2A2A2S11G0R1A2A3Lb;A2S1SbSbbVsegs;S7cG1S44G2R2A2A2A2ScA3A2F_;Fk;").
Hypothesis ERRLK : ltac2:(tb__ "0|3|
S4S43S44S82VC;A1M0Z4M1A2S83VC;A1M2A2S43S44G2G1A2G0A2A2").

Hypothesis HNE : ltac2:(tb__ "0|0|
S1S6S13eVe;A1S157S124Vc;A1A1A3").

Variable X_nt : fvar -> sstate.
Variables (Xc Xs Ev TN N0 N1 : fvar -> sstate) (sA : fvar -> wsub) (RA : fvar -> list sobj).
Hypothesis X_nt_shape : ltac2:(tb__ "0|1|
SafS0S1S6S29VX_nt;R1A1M0A1S157S124Vc;A1A1A3S0S1S1cSb1G0U1A2S22S125Vc;A1A1A3S0S1S1cSb1G0U2A2S27S107S20PaA1S22N30A1A3A3S0S1S1cSb1G0UaA2S172P84A1A3S0S1S1cSb1G0UbA2Sb6R1A1A3S1S7S23G0A1Sb0A3A2A2A2A2A2Fx;").
Hypothesis X_nt_objs : ltac2:(tb__ "0|3|
SafS1S8S1fA1M0S28VX_nt;R1A1A1M1S12S1fSdcS1fU1G1A3SfS1fS12cS12S1fSc6S1fSf7Vc;Sf8R1A1A2A2S12S1fSfaR1A1SbG0L_;Sf9R1A1SfS1fSb4Vc;A1S10S1fA1M2A3G2Xbx2A3A3A3A3A3Fx;").
Hypothesis Xc_eq : ltac2:(tb__ "0|0|
SafS1S1dVXc;R1A1S12fVX_nt;R1A1A1A3Fx;").
Hypothesis Xs_ok : ltac2:(tb__ "0|0|
SafS1SdS1dA1S120VXc;R1A1SfS11fS123U0S22N30A1A2S10S11fA1A3A2S11S1dVXs;R1A1A2A3Fx;").
Hypothesis Ev_ok : ltac2:(tb__ "0|0|
SafS1SdS1dA1S16aVXs;R1A1U0N30A3S11S1dVEv;R1A1A2A3Fx;").
Hypothesis RA_ok : ltac2:(tb__ "0|1|
SafS1SdS8S1fA1M0A1S152VEv;R1A1S12bVe;A1VsA;R1A1A3S11G0VRA;R1A1A2A3Fx;").
Hypothesis call_ok : ltac2:(tb__ "0|0|
SafS1SbSa1VEv;R1A1S12bVe;A1VsA;R1A1VRA;R1A1SfS1dS129Ve;A1S10S1dA1A3A5ScA3Fx;").
Hypothesis TN_ok : ltac2:(tb__ "0|1|
SafS1SdS1dA1S120S16bVEv;R1A1VsA;R1A1VRA;R1A1S129Ve;A1A4SfS11fS122U0M0A1SfS11fS121G0A1S10S11fA1A3A3A2S11S1dVTN;R1A1A2A3Fx;").
Hypothesis N0_eq : ltac2:(tb__ "0|0|
SafS1S1dVN0;R1A1S12eVTN;R1A1SfS1fSb3Vc;A1S10S1fA1A3SfS26S33S108S20S12aA1S22Z0A1A3S10S26A1A3A3A3Fx;").
Hypothesis N1_eq : ltac2:(tb__ "0|0|
SafS1S1dVN1;R1A1S12eVTN;R1A1SfS1fSb3Vc;A1SfS1fSb7S10S1fA1A3A3SfS26S39S33S108S20S12aA1S22Z0A1A3A1SfS26S34S20Pb6A1S22ZffffffffA1A2S10S26A1A3A3A3A3Fx;").
Hypothesis N0_ent : ltac2:(tb__ "0|3|
SafS0S1SbS153VN0;R1A1M0Sb2Vc;Ve;ScA3M1S15fS7eG0G1A3M2A3ScA3S0S1SbSc3G2S7eA2ScA3S0S1S1cSbfG2Pb4A2S20S12dA1A3S1S1cSbfG2Pb5A2S20S12aA1A3A2A2A2Fx;").
Hypothesis N1_ent : ltac2:(tb__ "0|4|
SafS0S1SbS153VN1;R1A1M0Sb2Vc;Ve;S14A3M1S15fS7eG0G1A3M2A3ScA3S0S1SbSc3G2S7eA2ScA3S0S1S1cSbfG2Pb4A2S20S12dA1A3S0S1S1cSbfG2Pb5A2S20S12aA1A3S1S1cSbfG2Pb6M3A2S20G3A1A3A2A2A2A2Fx;").
Hypothesis sA_regs : ltac2:(tb__ "0|4|
SafS0S1S1cSbfVsA;R1A1M0PaM1A2S27S107S20G1A1S22N30A1A3A3S0S1S1cSbfG0PfM2A2S27S107S20G2A1S22Z30A1A3A3S0S1S1cSbfG0P18M3A2S20G3A1A3S0S1S1cSbfG0PcA2S20P84A1A3S1S1cSbfG0PdA2Sb6R1A1A3A2A2A2A2Fx;").
Hypothesis RA_shape : ltac2:(tb__ "0|2|
SafS1S8SaSaS1cS1cA2M0S1cA2M1A1SdbS1fG1S1fS9G0S1cS9S1cS1cS2dR1A1S2fR1A1A4S2eR1A1A4Lo;VRA;R1A1A4SfG1S9G0S1cS9S1cS1cS20PaA1S22N30A1A4S22Z0A1A4S10G1A1A3A3Fx;").
Hypothesis Ev_misc : ltac2:(tb__ "0|7|
SafS0S1S8S26A1S2bVEv;R1A1M0A1SfS26S34S22Z1000A1S20PaA1M1A2S2bVX_nt;R1A1M2A1A3A3S0S1S7S23G0A1Sb0A3S0S1S6S29G0A1S29G2A1A3S0S1S8SaS1cS1cA2M3A1SdbS1fG3S1fS9S1cS1cS2dR1A1S2eR1A1A4Lo;S28G0A1M4A4SfG3S9S1cS1cS27S107G1S22N30A1M5A3S22Z0A1M6A4SfG3S9S1cS1cG1G6A4S10G3A1A3A3A3S1S8S1cA1SdbS1fS1cS2fG4A4SfS1cS27S107S20PfA1S22Z30A1A3SfS1cG5S10S1cA1A3A3A3A2A2A2A2Fx;").
Hypothesis imp_res : ltac2:(tb__ "0|1|
SafS0S1S1cSbfSa8VsA;R1A1S7eS129Ve;A1S23VEv;R1A1A1A4M0SedA2S20S12dA1A3S1S1cSbfG0S13bA2S20S12aA1A3A2Fx;").
Hypothesis N_swf : ltac2:(tb__ "0|0|
SafS0S1SbS2aVN0;R1A1A1ScA3S0S1SbS2aVN1;R1A1A1ScA3S1SbSa7S7S18S173R1Pb6A2A1Lv;VTN;R1A1A2ScA3A2A2Fx;").
Hypothesis TN_stk : ltac2:(tb__ "0|4|
SafS0S1S8SaSaS1cS1cA2M0S1cA2M1A1SdbS1fG1S1fS9G0S1cS9S1cS1cS2dR1A1S2fR1A1A4S2eR1A1A4Lo;S28VTN;R1A1M2A1A4SfG1S9G0S1cS9S1cS1cS20PaA1M3S20Se9A1A4S22Z0A1A4S10G1A1A3A3S0S1SbS160Sb5S2bG2A1A2ScA3S0S1S7S23G2A1P154A3S0S1S1cSb1G2U2A2S27S107G3S22N30A1A3A3S1S6S29G2A1S140Ve;A1A3A2A2A2A2Fx;").
Hypothesis Xc_swf : ltac2:(tb__ "0|1|
SafS0S1SbS2aVXc;R1A1A1ScA3S1SbS2aS30S29VX_nt;R1A1M0A1S41G0A1S40G0A1S3fG0A1S42G0A1SdcS1fU1S28G0A1A3S2bG0A1S23G0A1S38G0A1A9A1ScA3A2Fx;").
Hypothesis X_nt_stk : ltac2:(tb__ "0|3|
SafS0S1S8SaSaS1cS1cA2M0S1cA2M1A1SdbS1fG1S1fS9G0S1cS9S1cS1cS2dR1A1S2fR1A1A4S2eR1A1A4Lo;SdcS1fU1S28VX_nt;R1A1M2A1A3A4SfG1S9G0S1cS9S1cS1cS20PaA1S20Se9A1A4S22Z0A1A4S10G1A1A3A3S0S1SbS160Sb5S2bG2A1A2ScA3S1SbSa7S7S175R1Sb0A2Lv;G2A2ScA3A2A2Fx;").

Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (Kc : list event -> Model -> Prop) (rhoE : valuation) (tr0 : list event) (md : Model).
Variables (m1 : word -> option byte) (a : sptr) (k : Z).
Hypothesis Hfr : ltac2:(tb__ "0|2|
Sc4SaSaSaS4eS50A2M0S6A2M1S52A2S9G1S52S9G0S6S9S4eS50Vg;Vam;A4Vi;A4Vfr;A4Sd2Vs;A1A3").
Hypothesis Hkind : ltac2:(tb__ "0|0|
S1S6cS6dVfr;A1S66A3").
Hypothesis HslowI : ltac2:(tb__ "0|1|
S4S1S6S5bVam;A1M0Z0A3S1S6S44S4bG0S69Vam;A1A2S6bVi;A1A2S6fS6aVam;A1A1A3A2").
Local Notation rhoC := (set_rm rhoE m1).
Local Notation zP := (BlockView.zP L am i fr).
Local Notation n := (U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Notation rsv := (U.Mal_fslow__G1.Mal_fslow_I.rsv am fr).
Local Notation rhoF := (BlockView.rho1 L g am i fr (rho_set_rw rhoC 137%positive (Z_to_bv 64 rsv))).
Hypothesis HpC : ltac2:(tb__ "0|0|
S1S6S7aQ40S1eS105VrhoE;Vm1;A2PcA2A2Sd9VL;Vam;Vi;Vfr;A4A3").
Hypothesis HnC : ltac2:(tb__ "0|0|
S1S6S7aQ40S1eS105VrhoE;Vm1;A2PdA2A2Sf4Vfr;A1A3").
Hypothesis Hrsv32 : ltac2:(tb__ "0|0|
S1S6S59Vam;A1Z3fA3S45Sf5Vam;Vfr;A2S47Z2Z20A2A2F_;").
Hypothesis HMI1 : ltac2:(tb__ "0|0|
S9dVC;S99Vs;VL;A2Sb9Vsegs;Vm1;A2SbaVsegs;Vm1;A2S74Vmd;A1A5").
Hypothesis Harea : ltac2:(tb__ "0|2|
S0Sc4S4eVa;S71Vs;A1A3S0S0S43Z0Vk;A2S45Vk;S67A2A2S0S1S4eVg;S70Va;S44S65S4cS68Vk;A2A2A2A3S0Sc4Sd3Sd0Sd6Va;A1U8M0Sd1A3Sd8Vs;A1M1A3Sc4Sd3Sd0Sd5Sd4A1G0Sd1A3G1A3A2A2A2A2").
Hypothesis HTPv : ltac2:(tb__ "0|0|
S1S6S7aQ40S1eVrhoE;P18A2A2S86VC;A1A3").

Hypothesis HtopE : ltac2:(tb__ "0|0|
SefS99Vs;VL;A2VrhoE;A2").
Hypothesis M1blk : ltac2:(tb__ "0|3|
S6S0S43Sd9VL;Vam;Vi;Vfr;A4M0R1A2S45R1S44G0Sf4Vfr;A1A2A2A2S0S1SbSbaVsegs;Vm1;S7cQ40M1R2A2A3ScA3S3S7bQ8A1M2G2S1SdG2A1Sb9Vsegs;Vm1;S7cG1R3A2A3S11G2R1A2A3Lb;A2A2F_;Fx;").
Hypothesis M1out : ltac2:(tb__ "0|3|
S7bQ40M0A1S2S0S43Sd9VL;Vam;Vi;Vfr;A4M1S7aG0R1A2M2A2S45G2S44G1Sf4Vfr;A1A2A2A2A1S1SdS7bQ8A1A1Vm1;R2A1S21VrhoE;R2A2A3F_;Fw;").
Hypothesis M1sct : ltac2:(tb__ "0|2|
S6S0S43S84VC;A1M0R1A2S45R1S44G0Z60A2A2A2S1SdS7bQ8A1M1A1Vm1;S7cQ40R2A2A1S13G1A1A3F_;Fx;").

Local Abbreviation F_n := (@U.Mal_fslow__G1.Mal_fslow_I.n fr).
Local Notation "§1§ h__" := (h__ am fr) (at level 10, h__ global).
Local Abbreviation F_rsv := (§1§ U.Mal_fslow__G1.Mal_fslow_I.rsv).
Local Abbreviation F_Hp := (@U.Mal_fslow__G1.Mal_fslow_I.Hp L am i fr rhoC HpC).
Local Abbreviation F_Hpv := (@U.Mal_fslow__G1.Mal_fslow_I.Hpv ).
Local Abbreviation F_rhoF_rm := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rm L g am i fr rhoC).
Local Abbreviation F_rhoF_rl1 := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rl1 L g am i fr rhoC).
Local Abbreviation F_rhoF_rl_other := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rl_other L g am i fr rhoC).
Local Abbreviation F_rhoF_rw_low := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_rw_low L g am i fr rhoC).
Local Abbreviation F_rhoF_137 := (@U.Mal_fslow__G1.Mal_fslow_I.rhoF_137 L g am i fr rhoC).
Local Abbreviation F_FFx := (@U.Mal_fslow__G1.Mal_fslow_I.FFx segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr).
Local Abbreviation F_HMII := (@U.Mal_fslow__G1.Mal_fslow_I.HMII segs C s L (m_vmmaps md) m1 HMI1).
Local Abbreviation F_zEnd := (@U.Mal_fslow__G1.Mal_fslow_I.zEnd L am i).
Local Abbreviation F_NUMS := (@U.Mal_fslow__G1.Mal_fslow_I.NUMS segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_BV := (@U.Mal_fslow__G1.Mal_fslow_I.BV segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_In5 := (@U.Mal_fslow__G1.Mal_fslow_I.In5 C c Hrc HCc s g a k Harea).
Local Abbreviation F_st_nums := (@U.Mal_fslow__G1.Mal_fslow_I.st_nums C HSI L).
Local Abbreviation F_zr1_137 := (@U.Mal_fslow__G1.Mal_fslow_I.zr1_137 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze137 := (@U.Mal_fslow__G1.Mal_fslow_I.ze137 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze12 := (@U.Mal_fslow__G1.Mal_fslow_I.ze12 segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_ze_ffidx := (@U.Mal_fslow__G1.Mal_fslow_I.ze_ffidx segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_code := (@U.Mal_fslow__G1.Mal_fslow_I.ze_code segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_mem16 := (@U.Mal_fslow__G1.Mal_fslow_I.ze_mem16 segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_st_class := (@U.Mal_fslow__G1.Mal_fslow_I.st_class segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_S := (@U.Mal_fslow__G1.Mal_fslow_I.ze_S segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_stride := (@U.Mal_fslow__G1.Mal_fslow_I.ze_stride segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_end := (@U.Mal_fslow__G1.Mal_fslow_I.ze_end segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea).
Local Abbreviation F_st_map := (@U.Mal_fslow__G1.Mal_fslow_I.st_map segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_strideM := (@U.Mal_fslow__G1.Mal_fslow_I.ze_strideM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_endM := (@U.Mal_fslow__G1.Mal_fslow_I.ze_endM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_endX := (@U.Mal_fslow__G1.Mal_fslow_I.endX ).
Local Abbreviation F_kindok := (@U.Mal_fslow__G1.Mal_fslow_I.kindok am).
Local Abbreviation F_ze_endX := (@U.Mal_fslow__G1.Mal_fslow_I.ze_endX segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea).
Local Abbreviation F_HIF := (@U.Mal_fslow__G1.Mal_fslow_I.HIF segs C s L (m_vmmaps md) m1 HMI1).
Local Abbreviation F_cellIF := (@U.Mal_fslow__G1.Mal_fslow_I.cellIF segs C s L (m_vmmaps md) m1 HMI1).
Local Abbreviation F_ownIF := (@U.Mal_fslow__G1.Mal_fslow_I.ownIF segs C Hrc s L (m_vmmaps md) m1 HMI1).
Local Abbreviation F_cE := (@U.Mal_fslow__G1.Mal_fslow_I.cE am i).
Local Abbreviation F_cPN := (@U.Mal_fslow__G1.Mal_fslow_I.cPN am i fr).
Local Abbreviation F_cR := (@U.Mal_fslow__G1.Mal_fslow_I.cR am i fr).
Local Abbreviation F_cR5 := (@U.Mal_fslow__G1.Mal_fslow_I.cR5 am i).
Local Abbreviation F_QC := (@U.Mal_fslow__G1.Mal_fslow_I.QC segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind).
Local Abbreviation F_addr_cE := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cE L am i).
Local Abbreviation F_addr_cPN := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cPN segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_addr_cR := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cR L g am i fr rhoC).
Local Abbreviation F_addr_cR5 := (@U.Mal_fslow__G1.Mal_fslow_I.addr_cR5 L g am i fr rhoC).
Local Abbreviation F_G_Hng := (@U.Mal_fslow__G1.Mal_fslow_I.G_Hng segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind).
Local Abbreviation F_tail_owned := (@U.Mal_fslow__G1.Mal_fslow_I.tail_owned segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ev0 := (@U.Mal_fslow__G1.Mal_fslow_I.ev0 L g am i fr rhoC).
Local Abbreviation F_ev137 := (@U.Mal_fslow__G1.Mal_fslow_I.ev137 L g am i fr rhoC).
Local Abbreviation F_ev5 := (@U.Mal_fslow__G1.Mal_fslow_I.ev5 L g am i fr rhoC).
Local Abbreviation F_bE := (@U.Mal_fslow__G1.Mal_fslow_I.bE segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind).
Local Abbreviation F_bPN := (@U.Mal_fslow__G1.Mal_fslow_I.bPN segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_bR := (@U.Mal_fslow__G1.Mal_fslow_I.bR segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind).
Local Abbreviation F_bR5 := (@U.Mal_fslow__G1.Mal_fslow_I.bR5 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_covE := (@U.Mal_fslow__G1.Mal_fslow_I.covE segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind).
Local Abbreviation F_covPN := (@U.Mal_fslow__G1.Mal_fslow_I.covPN segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_covR := (@U.Mal_fslow__G1.Mal_fslow_I.covR segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_rsv_ok_r := (§1§ U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_r).
Local Abbreviation F_rsv_ok_j := (§1§ U.Mal_fslow__G1.Mal_fslow_I.rsv_ok_j).
Local Abbreviation F_ze_sub_code := (@U.Mal_fslow__G1.Mal_fslow_I.ze_sub_code segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_sub_137 := (@U.Mal_fslow__G1.Mal_fslow_I.ze_sub_137 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_rsv_small := (@U.Mal_fslow__G1.Mal_fslow_I.rsv_small segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea Hrsv32).
Local Abbreviation F_ZF_p := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_p segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_ZF_align12 := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_align12 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_ZF_gm_common := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_gm_common segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_ZF_gm_sized := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_gm_sized segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_ZF_gm_direct := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_gm_direct segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_gm_nomap := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_gm_nomap segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_gm_map := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_gm_map segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_idx94 := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_idx94 segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_lor_range := (@U.Mal_fslow__G1.Mal_fslow_I.lor_range segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_lor_bit_clear := (@U.Mal_fslow__G1.Mal_fslow_I.lor_bit_clear segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr).
Local Abbreviation F_lor_plus_bit := (@U.Mal_fslow__G1.Mal_fslow_I.lor_plus_bit segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_mask := (@U.Mal_fslow__G1.Mal_fslow_I.ze_mask segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ze_self := (@U.Mal_fslow__G1.Mal_fslow_I.ze_self segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_maskself := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_maskself segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_sx32_1 := (@U.Mal_fslow__G1.Mal_fslow_I.sx32_1 s L g am i fr rhoC Hfr HpC).
Local Abbreviation F_ZF_and1 := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_and1 segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_ZF_last0 := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_last0 segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_lastnz := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_lastnz segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_strideM := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_strideM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_ZF_kmA1 := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_kmA1 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea Hrsv32 HTP).
Local Abbreviation F_ZF_kc := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_kc segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_ZF_km := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_km segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea Hrsv32 HTP).
Local Abbreviation F_ze_en_minus_p := (@U.Mal_fslow__G1.Mal_fslow_I.ze_en_minus_p segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_rsv20 := (@U.Mal_fslow__G1.Mal_fslow_I.rsv20 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea Hrsv32 HTP).
Local Abbreviation F_ZF_rsv := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_rsv segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea Hrsv32 HTP).
Local Abbreviation F_ZF_rsvM := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_rsvM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea Hrsv32 HTP).
Local Abbreviation F_ze_maskself := (@U.Mal_fslow__G1.Mal_fslow_I.ze_maskself segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_ze_allmask := (@U.Mal_fslow__G1.Mal_fslow_I.ze_allmask segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_ZF_why := (@U.Mal_fslow__G1.Mal_fslow_I.ZF_why segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP HslowI).
Local Abbreviation F_why_map := (@U.Mal_fslow__G1.Mal_fslow_I.why_map segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP HslowI).
Local Abbreviation F_xof_cases := (@U.Mal_fslow__G1.Mal_fslow_I.xof_cases segs C Hrc s L g am i fr (m_vmmaps md) m1 HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_psupp_facts := (@U.Mal_fslow__G1.Mal_fslow_I.psupp_facts ).
Local Abbreviation F_D_call_facts_eq := (@U.Mal_fslow__G1.Mal_fslow_I.D_call_facts_eq c).
Local Abbreviation F_ZONES2 := (@U.Mal_fslow__G2.Mal_fslow_I2.ZONES2 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_rng_lit := (@U.Mal_fslow__G2.Mal_fslow_I2.rng_lit C L g am i fr rhoC HTP).
Local Abbreviation F_evu12 := (@U.Mal_fslow__G2.Mal_fslow_I2.evu12 L g am i fr rhoC HpC).
Local Abbreviation F_evu_mem := (@U.Mal_fslow__G2.Mal_fslow_I2.evu_mem segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_evu132 := (@U.Mal_fslow__G2.Mal_fslow_I2.evu132 segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_evu_area := (@U.Mal_fslow__G2.Mal_fslow_I2.evu_area segs C Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_evu_lit := (@U.Mal_fslow__G2.Mal_fslow_I2.evu_lit L g am i fr rhoC).
Local Abbreviation F_rng7 := (@U.Mal_fslow__G2.Mal_fslow_I2.rng7 segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP HORD).
Local Abbreviation F_pw7 := (@U.Mal_fslow__G2.Mal_fslow_I2.pw7 segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP HORD).
Local Abbreviation F_win_vs7 := (@U.Mal_fslow__G2.Mal_fslow_I2.win_vs7 segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP HORD).
Local Abbreviation F_fixed7_misc := (@U.Mal_fslow__G2.Mal_fslow_I2.fixed7_misc segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP HORD).
Local Notation "§2§ h__" := (h__ L am i fr) (at level 10, h__ global).
Local Abbreviation F_winsZ := (§2§ U.Mal_fslow__G2.Mal_fslow_I2.winsZ).
Local Abbreviation F_rngW := (@U.Mal_fslow__G2.Mal_fslow_I2.rngW segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_winsZM := (§2§ U.Mal_fslow__G2.Mal_fslow_I2.winsZM).
Local Abbreviation F_rngWM := (@U.Mal_fslow__G2.Mal_fslow_I2.rngWM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_tailZ := (§2§ U.Mal_fslow__G2.Mal_fslow_I2.tailZ).
Local Abbreviation F_winsZ_ok := (@U.Mal_fslow__G2.Mal_fslow_I2.winsZ_ok segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_winsZM_ok := (@U.Mal_fslow__G2.Mal_fslow_I2.winsZM_ok segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_rsv_ok_rr := (@U.Mal_fslow__G2.Mal_fslow_I2.rsv_ok_rr segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea).
Local Abbreviation F_rsv_ok_jj := (@U.Mal_fslow__G2.Mal_fslow_I2.rsv_ok_jj segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_wins_x := (@U.Mal_fslow__G2.Mal_fslow_I2.wins_x segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP).
Local Abbreviation F_mid_pw := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_pw segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP HORD).
Local Abbreviation F_mid_misc := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_misc segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP HORD).
Local Abbreviation F_rv_of_carvable := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_of_carvable segs C L g am i fr m1 rhoC).
Local Abbreviation F_rv_grp := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_grp segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_rv_meta := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_meta segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_rv_area := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_area segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_rv_sec := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_sec segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_rv_hdr4 := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_hdr4 segs C c HSI Hrc HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea).
Local Abbreviation F_rv_nl := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_nl segs C c HSI HCc NLW s L g am i fr (m_vmmaps md) m1 rhoC HMI1 HTP HORD).
Local Abbreviation F_rv_lock := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_lock segs C c HSI HCc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 HTP).
Local Abbreviation F_rv_win := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_win segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_rv_rsv := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_rsv segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind a k Harea HTP).
Local Abbreviation F_rv_rsvM := (@U.Mal_fslow__G2.Mal_fslow_I2.rv_rsvM segs C HSI Hrc s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC a k Harea HTP).
Local Abbreviation F_mid_rv := (@U.Mal_fslow__G2.Mal_fslow_I2.mid_rv segs C c HSI Hrc HCc NLW s L g am i fr (m_vmmaps md) m1 rhoC HMI1 Hfr Hkind HpC HnC a k Harea HTP HORD).

Let A : MA := mkMA s L.
Let s1 : astate := ltac2:(tb__ "0|0|
Sf2Vs;Vg;Vam;Vi;A4").
Let A1 : MA := mkMA s1 L.
Definition x0 : fvar := xof am fr.

Lemma FFx : ltac2:(tb__ "0|0|
S16dVs;Vg;Vam;Vi;Vfr;A5"). Proof using HMI1 Hfr. exact (frame_facts_of s g am i fr (proj1 HMI1) Hfr). Qed.
Lemma HW : WF s. Proof using HMI1. exact (proj1 HMI1). Qed.
Lemma Hreach : reach_ok s. Proof using HMI1. pose proof HMI1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R). exact R. Qed.

Definition K0 : list event -> Model -> Prop := ltac2:(tb__ "0|1|
S8S73A1M0S72S0VKc;R2R1A2S0S1G0R2Vtr0;A3S1S72R1Vmd;A3A2A2Lmdx;Ltr;").

Definition K1 (A' : MA) (m4 : word -> option byte) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S8S73A1S72S0VKc;R2R1A2SbeVC;S10S4eA1S13SaS4eS6A2A1Sc7VA';Sb9Vsegs;Vm4;A2SbaVsegs;Vm4;A2S74R1A1A8A2Lmdx;Ltr;").

Definition nt_in_facts (rho : valuation) (tr : list event) (mdx : Model) : Prop := ltac2:(tb__ "0|6|
S0S1S6S81VL;Vg;A2S7aQ40M0S1eVrho;PcA2A2A3S0S1S6Vi;S7aG0S1eVrho;PdA2A2A3S0SbeVC;S10S4eA1M1S11SaS4eS6A2S9S4eS6Vg;Vi;A4A2Sc7VA1;Sb9Vsegs;S21Vrho;A1M2A2SbaVsegs;G2A2S74Vmdx;A1A8S0ScbG1Vs1;Vg;Sf3Vam;Vi;A2M3A4S0S2S1SaSdS4eA1M4G4A2S9G4G4S61G3A1S60G3A1A4S9G4G4S13S4eA1M5G5A4A3A1S2S1G4SceVs1;S59G3A1A2S11S4eVg;A2A3A1S2S1S6S5bG3A1Z0A3A1F_;F_;S0S43S10cZ40S7aG0S1eVrho;Se9A2A2A2N180A2S0S10bVs1;A1S0S1S6S7aG0S1eVrho;P18A2A2S86VC;A1A3S0VKc;Vtr;Vmdx;A2SefVA1;Vrho;A2A2A2A2A2A2A2A2A2A2").

Variable XP : ltac2:(tb__ "0|0|
S9aSdSaSeS4fA2A1OF_;F_;").
Definition nt_out_facts (rho0 rho' : valuation) (tr : list event) (mdx : Model) : Prop := ltac2:(tb__ "0|6|
S7aQ40M0S1eVrho';SedA2A2S6S7aG0S1eVrho';S13bA2A2S6S3S9aS9aS0SbeVC;S10S4eA1M1S13SaS4eS6A2A1Sc7R1Sb9Vsegs;S21Vrho';A1M2A2SbaVsegs;G2A2S74Vmdx;A1A8S0S1Sc8S9bR1A1VL;A3S0S156G1Vs1;S98R1A1M3A3S0S155Vs1;G3A2S0S10bG3A1S0S1SbS53G3A1ScA3S0S4S0S1S6R2Z0M4A3S0S1S6R3G4A3VXP;R1S13SaSeS4fA2M5A1A2A2A2S0S45G4R2A2S3SeSeS3S4fS4fS0S1SdS4fA1ScaS98R3A1R2A2S11S4fR1A2A3S0S1S58S56R1A1S55A3S0S1SbS57R1A1ScA3S0S1S6S5aR1A1S5eR4A1A3S0S1S6ScdS9bR3A1R2A2R5A3S0S4eS50ScbG1S98R5A1R2R1A4S45G4S5cR2A1A2S2S1SeS5fS5dR3A1A1R6A3A1F_;F_;Faq;Fq;VXP;R3S11G5S9SeS4fR2R1A4A2A2A2A2A2A2A2A2Lrg;A2Lkr;A2A2A2S0Sf0VC;VA1;R1S21Vrho0;A1G2A5VKc;Vtr;Vmdx;A2A2A2A2A2A2A2A2A2LA';A2Tlen;Tbase;").

Definition ret_facts (A' : MA) (rho4 : valuation) : Prop := ltac2:(tb__ "0|4|
S0S1Sc8S9bVA';A1VL;A3S0S10bS98VA';A1M0A1S0S1SbS53G0A1ScA3S0S3S8SaS6S6A2M1A1M2G2S3G2G2S0S1G2S9cVA;A1S12G1R2SfG1S9S6S6Sd9VL;Vam;Vi;Vfr;A4Sf4Vfr;A1A4R1A3A3A3S1G2S9cVA';A1S12G1R2R1A3A3A2Ll2;A2Ll1;A2S0S7S174R1S7eA2S1S7bQ40M3A1S1eVrho4;R2A2S1eVrhoE;R2A2A3F_;Fj;S0S7S1S8S7bQ8A1A1S32Vrho4;R1A2S32SdaVL;Vg;Vam;Vi;Vfr;S11aS105VrhoE;Vm1;A2P89S7cG3Sf5Vam;Vfr;A2A2A3A6R1A2A3Fl;SeaVsegs;VC;VA;VA';S21VrhoE;A1S21Vrho4;A1A6A2A2A2A2A2A2").
Definition unmap_facts (A' : MA) (rho4 : valuation) : Prop := ltac2:(tb__ "0|3|
S7aQ40M0S1eVrho4;Pb4A2A2S6S7aG0S1eVrho4;Pb5A2A2S6S0S45Z0M1R1A2S3SeSeS3S4fS4fS0S1SdS4fA1ScaS98VA';A1M2R2A2S11S4fR1A2A3S0S1S58S56R1A1S55A3S0S1SbS57R1A1ScA3S0S1S6S5aR1A1S5eR3A1A3S0S1S6ScdS9bVA';A1R2A2R4A3S0S4eS50ScbS10S4eA1G2R2R1A4S45G1S5cR2A1A2S2S1SeS5fS5dR3A1A1R6A3A1F_;F_;Faq;Fq;VXP;VA';S11SaSeS4fA2S9SeS4fR2R1A4A2A2A2A2A2A2A2A2Lrg;A2Lkr;A2A2Tlen;Tbase;").

Lemma hold_lockI : ltac2:(tb__ "0|0|
S8S4eA1SdSaS4eS6A2A1S6S6F_;S9aS7bQ40A1SdS7bQ8A1A1F_;S1bSdfS4SbeVC;R7R6R5R4Sb9Vsegs;R3A2SbaVsegs;R3A2S74Vmd;A1A8S3S75S75SbeVC;R8R7R6R5Sb9Vsegs;R4A2SbaVsegs;R4A2R1A8Lvm;A2A2S3eVsegs;R2A2S36Vsegs;R4S106R3R5A2Sb3Vc;A1A4F_;F_;Fms;Frho;Fm;FA';FU;FR;FX;").
Proof using HCc HSI HTP Kc L XP tr0.
  intros X R U A' m rho ms HM Hrom. pose proof F_st_nums as (SN1 & SN2 & SN3 & SN4 & SN5 & SN6).
  assert (LK : MallocLayout.holds (byteview_of (rd_of segs m) (wok_of segs m)) (mc_lock C) 4 0).
  { destruct HM as [HM | [vm HM]]; destruct (mig_statics HM) as (_ & _ & _ & LK & _); exact LK. }
  unfold MallocLayout.holds in LK.
  change (O_lock c) with (carved (SLit (ff_lockword (fs_ff c))) 0 4 [(0, 4%nat, SLit 0)]). rewrite (proj1 (proj2 (proj2 HCc))).
  apply (obj_holds_frame_lit segs rho ms m (SLit (mc_lock C)) 0 4 [(0, 4%nat, SLit 0)] Hrom); cbn [eval]; rewrite ?u64_of_sum by lia; try lia.
  - constructor; [|constructor]. cbn. lia.
  - intros off Hoff. replace off with (Z.of_nat (Z.to_nat off)) by lia.
    destruct (byteview_of_Some _ _ _ _ (LK (Z.to_nat off) ltac:(lia))) as (_ & W & b & Hb & _). split; [exact W | eexists; exact Hb].
  - constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    destruct (byteview_of_Some _ _ _ _ (LK j Hj)) as (_ & _ & b & Hb & Eb). rewrite Hb. f_equal. cbn [eval].
    rewrite nth_enc_bytes by lia. rewrite <- (Z_to_bv_bv_unsigned 8 b), <- Eb. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Definition errno_bs (m : word -> option byte) : list byte := ltac2:(tb__ "0|2|
SdbSeS7bQ8M0A1M1SeSdG1A1G1Lx;Sb9Vsegs;Vm;S7cQ40S44S82VC;A1S48R1A1A2A2A3G1R1Lb;S7cG0Z0A2Xdx2Lj;SdeU0U4A2A4").
Definition errno_word (m : word -> option byte) : word := le_bytes_to_word (errno_bs m).
Lemma errno_bytes : ltac2:(tb__ "0|4|
S7bQ40M0A1SdS7bQ8A1M1A1M2F_;SeS15eR1U4A2S3G1G1S0S1G2Sb9Vsegs;R4S7cG0S44S82VC;A1S48R3A1A2A2M3A3S11G1R1A2A3S1SbSbaVsegs;R4G3A3ScA3A2Lb;A2F_;Fj;Fm;").
Proof using A1 ERRIMG Kc XP md tr0.
  intros m j Hj. destruct (ERRIMG (Z.of_nat j) ltac:(lia)) as [[b0 IB] WS]. unfold rd_of, wok_of.
  destruct (m (wz (mc_errno C + Z.of_nat j))) as [b|]; [exists b; auto | exists b0; auto].
Qed.
Lemma errno_word_small : ltac2:(tb__ "0|1|
S7bQ40M0A1SdS7bQ8A1A1F_;S45S7aG0SffR1A1A2S47Z2Z20A2A2Fm;").
Proof using A1 Kc XP md tr0.
  intros m. unfold errno_word, le_bytes_to_word. pose proof (bytes_le_to_Z_bound (errno_bs m)) as B.
  replace (length (errno_bs m)) with 4%nat in B by reflexivity. change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in B. rewrite u64_of_sum by lia. lia.
Qed.
Lemma errno_word_bytes : ltac2:(tb__ "0|5|
S7bQ40M0A1SdS7bQ8M1A1M2A1M3F_;SeS15eR1U4M4A2S1G3Sb9Vsegs;R3S7cG0S44S82VC;A1S48R2A1A2A2A3S11G2SddG2R2S3aG4SffR3A1A2S7cG1Z0A2A4A2A3F_;Fj;Fm;").
Proof using A1 ERRIMG Kc XP md tr0.
  intros m j Hj. unfold errno_word. rewrite enc_bytes_le_word by (reflexivity || lia).
  destruct (errno_bytes m j Hj) as (b & Hb & _). unfold errno_bs.
  destruct j as [|[|[|[|j]]]]; cbn [map seq nth Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hb; rewrite Hb; [reflexivity..|lia].
Qed.

Lemma swf_drop_facts pc r f cs vv objs F facts nx l : ltac2:(tb__ "0|0|
S1SbS2aS30Vpc;Vr;Vf;Vcs;Vvv;Vobjs;S12S26VF;Vfacts;A3Vnx;Vl;A9A1ScA3S1SbS2aS30Vpc;Vr;Vf;Vcs;Vvv;Vobjs;Vfacts;Vnx;Vl;A9A1ScA3F_;").
Proof using .
  unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts]. intros H.
  apply andb_prop in H as [H HF]. rewrite H. rewrite forallb_app in HF. apply andb_prop in HF as [_ HF]. exact HF.
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S8S73A1S72OF_;F_;OF_;").
Variable QF : assn.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S94S94S94S95R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S94S94S95R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inhP : ltac2:(tb__ "0|0|
S94S94S95R3R1A1S3S94S94S0R1R3A1VTR;R1R4A2A2LP';A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
SabSabS1dS1dSc2S8S1fA1M0S8SaS1dS9fA2M1A1S94S1bS1SdG0A1S152R7R6R5A3S11G0R4A2A3S1SbSa1R8R7R6R5SdbG1S1dS15S1dS9fA2R4A4A5ScA3S1bVTR;Sa9Vsegs;RbR9R1A4Sa0Vsegs;S23R9A1R1R6A4A2Frho1;S8S73A1M2SdfS72S25Vsegs;R7RdS9G2Se2R3Se3R2R1A2A4A4R10R8R4R2A3R10Sc1Sc0R9RcR4A3RdA2R5R3A3F_;F_;Fmdx;Fms;Ftr;S1dS9fG2SdfS72S1bG2SdfS72Sc4G1S9S1dS9fR9R8A4R10A3S25Vsegs;RfR15S9G2Se2R8Se3R7R6A2A4A4R18R10R9R7A3Sa3S23R16A1Sc1Sc0R11R14R9A3R15A2R7A3S25Vsegs;R8RdS9G2Se2R7Se3R6R5A2A4A4RdSc1Sc0R13R16RbA3R17A2R9R8R6A4S0Sa5R14RcR17R18R19RfRaA7S1bSa4R15RdR18R19R1aR1bR10R1RbA9VTR;Sa9Vsegs;Sa2R10Sc1Sc0R16R19ReA3R1aA2RcA3Sa6R1aS23R1bA1R11S23R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmdx;Fms;Ftr;FJL;FLf;VTR;Sa9Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ';FPosts;FR;Fsb;FPre;FCl;FJp;FJ;").

Variables (Jp : jpred) (JLp : jpost).
Hypothesis NT : ltac2:(tb__ "0|1|
S1bVTR;Sa9Vsegs;VJp;S12bVe;A1R1A4Sa0Vsegs;S7eR1SfSaS1dS9fA2M0S9S1dS9fS129Ve;A1VJLp;A4S10G0A1A3A4A2Frho;").
Hypothesis JIN : ltac2:(tb__ "0|0|
S1bS8S73A1S72S102R3R2R1A3VJp;R4R3R2A3F_;Fmdx;Ftr;Frho;").
Hypothesis JOUT : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72VJLp;R4R3R2R1A4S103R5R4R3R2A4F_;Fmdx;Ftr;Frho';Frho0;").

Hypothesis CONT0 : ltac2:(tb__ "0|0|
S9aS1bS100R2R1A2S1S6S7aQ40S1eR2Pb5A2A2Z0A3VXP;R4S13SaSeS4fA2A1A2VTR;SaaVsegs;SfeR5S21R4A1A2Sb2Vc;Ve;ScA3R4A4VQF;A2F_;F_;F_;Frho4;FA';").
Hypothesis CONT1 : ltac2:(tb__ "0|0|
S9aS1bS100R2R1A2S104R3R2A2VTR;SaaVsegs;SfeR4S21R3A1A2Sb2Vc;Ve;S14A3R3A4VQF;A2F_;F_;Frho4;FA';").

Definition R2 : list sobj := ltac2:(tb__ "0|1|
SfS1fS12cS12S1fSc6S1fSf7Vc;Sf8SfdA1A2A2S12S1fSfaSfdA1SbS8S1fA1L_;Sf9SfdA1SfS1fSb4Vc;A1S10S1fA1M0A3G0Xbx2A3A3A3").

Lemma NUMSx : ltac2:(tb__ "0|6|
S0S43Z0M0Sf5Vam;Vfr;A2M1A2S0S1S6S44S44Sd9VL;Vam;Vi;Vfr;A4M2Sf4Vfr;A1M3A2G1A2SfcVL;Vam;Vi;A3M4A3S0S43G0G3A2S0S43Z1000S46G2Z10A2A2S0S43S44G4Z4A2S90VL;A1M5A2S45G5S47Z2Z2fA2A2A2A2A2A2A2").
Proof using HMI1 HSI HTP Harea Hfr Hkind Hrc Kc okK rhoE. pose proof F_NUMS as N. cbn zeta in N. lia. Qed.

Lemma R2_cases : ltac2:(tb__ "0|0|
S1fSc4S1fR1S15dA3S4S1S1fR2S12cA3S4S0Sc4S1fR2S12S1fSc6S1fSf7Vc;Sf8SfdA1A2A2SfaSfdA1A3A3S161Vsegs;SdaVL;Vg;Vam;Vi;Vfr;S11aS105VrhoE;Vm1;A2P89S7cQ40Sf5Vam;Vfr;A2A2A3A6Vm1;R2A4A2S0S1S1fR2Sb4Vc;A1A3S1SbSf9SfdA1ScA3A2A2A2F_;Fo;").
Proof using HCc HMI1 HORD HSI HTP Harea Hfr Hkind HnC HpC Hrc NLW.
  intros o Ho. unfold R2 in Ho. destruct Ho as [<-|Ho]; [left; reflexivity|right].
  rewrite app_assoc in Ho. apply in_app_iff in Ho as [Ho|Ho].
  - left. split; [exact Ho|]. exact (proj1 (Forall_forall _ _) F_mid_rv o Ho).
  - right. destruct (has_sct x0); [|destruct Ho]. destruct Ho as [<-|[]]. auto.
Qed.

Lemma R2_zone : ltac2:(tb__ "0|2|
S1fS6Sc4S1fR2S15dA3S0S43S15S6S6S37SdaVL;Vg;Vam;Vi;Vfr;S11aS105VrhoE;Vm1;A2P89S7cQ40Sf5Vam;Vfr;A2A2A3A6R3A2M0A3R2A2S45R2S16S6S6G0A3A2A2S4S9eVC;VA;R3A3S4Sf1VC;R3A2S0S43S84VC;A1M1R3A2S45R3S44G1Z60A2A2A2A2A2F_;F_;Fx;Fo;").
Proof using HCc HMI1 HORD HSI HTP Harea Hfr Hkind HnC HpC Hrc Kc okK.
  intros o x Ho Hx. pose proof F_BV as (_ & _ & _ & _ & OWN). pose proof NUMSx as N. pose proof HCc as (E1 & E2 & E3 & E4).
  unfold R2 in Ho. destruct Ho as [<-|Ho].
  { left. apply (proj1 (Forall_forall _ _) OWN (bv_hdr (BlockView.pS 12%positive))); [left; reflexivity|].
    unfold obj_range, obj_lo_of, obj_hi_of, hdrX in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx. rewrite !soff_lit_small in Hx by lia.
    unfold d_range, bv_hdr. cbn [fst snd]. exact Hx. }
  apply in_app_iff in Ho as [Ho|Ho].
  {
    pose proof (F_rng7 (h3_of x0)) as RG.
    pose proof (f_equal (fun l => nth 1%nat l (0,0)) RG) as Rgrp. pose proof (f_equal (fun l => nth 2%nat l (0,0)) RG) as Rmeta.
    pose proof (f_equal (fun l => nth 3%nat l (0,0)) RG) as Rarea. pose proof (f_equal (fun l => nth 4%nat l (0,0)) RG) as Rsec.
    pose proof (f_equal (fun l => nth 5%nat l (0,0)) RG) as Rnl. pose proof (f_equal (fun l => nth 6%nat l (0,0)) RG) as Rlock.
    cbn [nth map fixed7] in Rgrp, Rmeta, Rarea, Rsec, Rnl, Rlock. clear RG.
    unfold fixed7 in Ho. cbn [tl] in Ho.
    destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    - left. apply (proj1 (Forall_forall _ _) OWN (bv_grp (BlockView.pS 12%positive))); [right; left; reflexivity|]. rewrite Rgrp in Hx. unfold d_range, bv_grp. cbn [fst snd].
      pose proof F_evu_mem as EM. change gm_mem_sv with (bv_mem (BlockView.pS 12%positive)) in EM. rewrite EM. cbn [fst snd] in Hx. lia.
    - left. apply (proj1 (Forall_forall _ _) OWN (bv_meta (BlockView.pS 12%positive))); [right; right; left; reflexivity|]. rewrite Rmeta in Hx. unfold d_range, bv_meta. cbn [fst snd].
      pose proof F_evu132 as EM. change (v 132) with bv_g in EM. rewrite EM. cbn [fst snd] in Hx. lia.
    - left. apply (proj1 (Forall_forall _ _) OWN bv_area); [right; right; right; left; reflexivity|]. rewrite Rarea in Hx. unfold d_range, bv_area. cbn [fst snd].
      pose proof F_evu_area as EM. change (SAlu ALU_AND (v 132) (SLit MASK_PAGE)) with (SAlu ALU_AND bv_g (SLit BlockViewIface.MASK_PAGE)) in EM. rewrite EM. cbn [fst snd] in Hx. lia.
    - left. apply (proj1 (Forall_forall _ _) OWN (bv_ctx C)); [right; right; right; right; left; reflexivity|]. rewrite Rsec in Hx. unfold d_range, bv_ctx. cbn [fst snd eval].
      rewrite u64_of_sum by (pose proof F_st_nums; destruct F_ZONES2 as (G0 & RL & ZZ); lia). cbn [fst snd] in Hx. lia.
    - right; left. rewrite Rnl in Hx. cbn [fst snd] in Hx. unfold alloc_static. unfold mc_need_locks in Hx. lia.
    - left. right. rewrite Rlock in Hx. cbn [fst snd] in Hx. lia. }
  apply in_app_iff in Ho as [Ho|Ho].
  {
    left. left. destruct F_wins_x as (WZ & EW & TW & _).
    assert (T : tailZ L am i fr (obj_range rhoF o)).
    { apply (proj1 (Forall_forall _ _) TW). rewrite <- EW. apply in_map. exact Ho. }
    destruct T as [T1 T2]. apply F_tail_owned. cbn zeta. lia. }
  destruct (has_sct x0); [|destruct Ho]. destruct Ho as [<-|[]]. right; right.
  unfold obj_range, obj_lo_of, obj_hi_of, O_sct in Hx. cbn [ob_base ob_lo ob_hi fst snd eval] in Hx. rewrite (proj2 (proj2 (proj2 HCc))) in Hx.
  rewrite !soff_lit_small, u64_of_sum in Hx by (destruct F_ZONES2 as (G0 & RL & ZZ); lia). lia.
Qed.

Lemma forallb_app_iff {T} (f : T -> bool) l1 l2 : ltac2:(tb__ "0|0|
S5S1SbSc5VT;Vf;S12VT;Vl1;Vl2;A3A3ScA3S0S1SbSc5VT;Vf;Vl1;A3ScA3S1SbSc5VT;Vf;Vl2;A3ScA3A2A2").
Proof using . rewrite forallb_app. split; [intros H; apply andb_prop in H; exact H | intros [H1 H2]; rewrite H1, H2; reflexivity]. Qed.

Lemma hdr_bytes rho ms : ltac2:(tb__ "0|6|
S36Vsegs;Vrho;Vms;S12cA4S1S6S7aQ40M0S2cVrho;S20PcA1A2A2Sd9VL;Vam;Vi;Vfr;A4M1A3S0S1SdS7bQ8M2A1M3A1M4Se1Vms;S7cG0S46G1Z4A2A2A2S11G3S7cG2Z0A2A2M5A3S0S1G4Se1Vms;S7cG0S46G1Z3A2A2A2S11G3S7cG2ZffA2A2A3S0S1G4Se1Vms;S7cG0S46G1Z2A2A2A2G5A3S1G4Se1Vms;S7cG0S46G1Z1A2A2A2G5A3A2A2A2F_;F_;").
Proof using HMI1 HORD HSI HTP Harea Hfr Hkind Hrc Kc WSEG okK rhoE.
  intros HO E12. pose proof NUMSx as N.
  assert (G : forall cl kk off, In cl (ob_cells hdrX) -> (kk < Z.to_nat (c_width cl))%nat -> c_off cl = SLit off -> -4 <= off /\ off + Z.of_nat kk < 0 ->
             ms_mem ms (wz (zP + off + Z.of_nat kk)) = Some (nth kk (enc_bytes (Z.to_nat (c_width cl)) (eval rho (c_val cl))) (Z_to_bv 8 0))).
  { intros cl kk off Hin Hkk Hoff Hr.
    pose proof (cell_bytes_sym segs rho ms hdrX cl kk HO Hin Hkk) as R. cbn [ob_base hdrX] in R. rewrite Hoff, soff_lit_small, E12 in R by lia.
    unfold rd, ms_read_byte in R.
    destruct (ms_mem ms (wz (zP + off + Z.of_nat kk))) as [b|] eqn:E; [exact R|]. exfalso.
    pose proof (proj1 (proj2 HO) (off + Z.of_nat kk)) as W. unfold obj_lo_of, obj_hi_of, hdrX in W. cbn [ob_base ob_lo ob_hi ob_dflt] in W.
    rewrite !soff_lit_small, E12 in W by lia. replace (zP + (off + Z.of_nat kk)) with (zP + off + Z.of_nat kk) in W by lia.
    specialize (W ltac:(lia) eq_refl). unfold wview in W. rewrite E in W.
    assert (WS : wseg_addr segs (wz (zP + off + Z.of_nat kk)) = true).
    { unfold wseg_addr. destruct (find_segment segs (bv_unsigned (wz (zP + off + Z.of_nat kk))) 1) as [seg|]; [|exfalso; apply W; reflexivity].
      destruct (seg_writable seg); [reflexivity | exfalso; apply W; reflexivity]. }
    pose proof (WSEG _ WS) as IMG. rewrite u64_of_sum in IMG by lia. destruct F_ZONES2 as (G0 & RL & ZZ). pose proof F_NUMS as NN. cbn zeta in NN. lia. }
  pose proof (G (mkCell (SLit (-4)) 1 (SLit 0)) 0%nat (-4) ltac:(right; right; left; reflexivity) ltac:(cbn; lia) eq_refl ltac:(lia)) as B4.
  pose proof (G (mkCell (SLit (-3)) 1 (SLit 18446744073709551615)) 0%nat (-3) ltac:(right; left; reflexivity) ltac:(cbn; lia) eq_refl ltac:(lia)) as B3.
  pose proof (G (mkCell (SLit (-2)) 2 (SLit 0)) 0%nat (-2) ltac:(left; reflexivity) ltac:(cbn; lia) eq_refl ltac:(lia)) as B2.
  pose proof (G (mkCell (SLit (-2)) 2 (SLit 0)) 1%nat (-2) ltac:(left; reflexivity) ltac:(cbn; lia) eq_refl ltac:(lia)) as B1.
  replace (zP + -4 + Z.of_nat 0) with (zP - 4) in B4 by lia. replace (zP + -3 + Z.of_nat 0) with (zP - 3) in B3 by lia.
  replace (zP + -2 + Z.of_nat 0) with (zP - 2) in B2 by lia. replace (zP + -2 + Z.of_nat 1) with (zP - 1) in B1 by lia.
  rewrite B4, B3, B2, B1. repeat split; f_equal; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma at_cut : ltac2:(tb__ "0|4|
S1bS8S73A1M0SdfS24Sb0SdaVL;Vg;Vam;Vi;Vfr;S11aS105VrhoE;Vm1;A2P89S7cQ40M1Sf5Vam;Vfr;A2A2A3A6R3A3S25Vsegs;R4VX_nt;SfdA1S9G0Se2R3Se3R2Vmd;A2A4A4S16fR5S15dR3A3S7bG1A1SdS7bQ8A1A1M2F_;S3bS1eR6A1S32R6A1R1A3S1bS0S25Vsegs;R1VXc;SfdA1S9G0Se2R6Se3R5Vmd;A2A4A4S0SbeVC;S10S4eA1S11SaS4eS6A2S9S4eS6Vg;Vi;A4A2Sc7VA1;Sb9Vsegs;R2A2SbaVsegs;R2A2S74Vmd;A1A8S6S0S43Z0R1A2S45R1S47Z2Z40A2A2A2S2S9eVC;VA;R2A3A1S2Sf1VC;R3A2A1S1G2R6S7cG1R4A2M3A1Vm1;G3A1A3F_;F_;F_;Fx;A2A2Trho3;Tm2;F_;F_;Fms;Ftr;Frho2;").
Proof using HCc HMI1 HORD HSD HSI HTP Harea Hfr Hkind HnC HpC Hrc Kc M1blk M1sct NLW SCT WSEG X_nt_objs X_nt_shape X_nt_stk Xc_eq Xc_swf okK s1.
  intros rho2 tr ms Hag2 Hsm0 m2 rho3.
  pose proof Hag2 as (AGw & AGl & AGm). pose proof NUMSx as N. top_ranges.
  assert (Hrm2 : forall w, rm rho2 w = m1 w).
  { intros w. rewrite <- AGm. pose proof F_rhoF_rm as E. cbn [rm set_rm] in E. rewrite E. reflexivity. }

  destruct (smatch_release_suffix segs rho2 (X_nt x0) tr ms md (firstn 1 (ss_objs (X_nt x0))) R2 (ss_next (X_nt x0)) Hsm0 (X_nt_objs x0) (proj2 (Xc_swf x0)))
    as (Hsm1 & M2out & M2in & Hold2). fold m2 in Hsm1, M2out, M2in. change (mkVal (rw rho2) (rl rho2) m2) with rho3 in Hsm1.
  pose proof Hsm0 as (_ & _ & _ & _ & Hrom & Hroc & _). cbn [fst snd cfg_ms] in Hrom, Hroc.

  assert (WO : forall o, In o R2 -> obj_wf FS_NEXT o = true).
  { intros o Ho. pose proof (swf_objs _ (smatch_swf segs _ _ _ Hsm0)) as W. rewrite (X_nt_objs x0) in W. apply forallb_app_iff in W as [_ W].
    rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (X_nt_shape x0)))))) in W. exact (proj1 (forallb_forall _ _) W o Ho). }
  assert (RNG : forall o, In o R2 -> obj_range rho2 o = obj_range rhoF o).
  { intros o Ho. exact (obj_range_agree FS_NEXT rhoF rho2 o Hag2 (WO o Ho)). }
  assert (RV2 : forall o, In o (tl (fixed7 c (h3_of x0)) ++ wins x0) -> ro_view segs rhoF m1 o -> ro_view segs rho2 m1 o).
  { intros o Ho Hv. apply (ro_view_agree_vars segs (fun v => Pos.ltb v FS_NEXT) rhoF rho2 m1 o); [intros v Hv'; apply AGw; apply Pos.ltb_lt; exact Hv' | exact AGl | | exact Hv].
    apply obj_wf_vars_all. apply WO. unfold R2. right. rewrite app_assoc. apply in_app_iff. left. exact Ho. }

  assert (M2eq : forall w, ~ (zP - 4 <= bv_unsigned w < zP) -> rd_of segs m2 w = rd_of segs m1 w /\ wok_of segs m2 w = wok_of segs m1 w).
  { intros w Hw. destruct (in_ranges_dec rho2 R2 w) as [Hin | Hni].
    - pose proof Hin as (o & Ho & Hr). rewrite (RNG o Ho) in Hr.
      destruct (R2_cases o Ho) as [-> | [[Ho' Hv] | [-> HS]]].
      + exfalso. unfold obj_range, obj_lo_of, obj_hi_of, hdrX in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. rewrite !soff_lit_small in Hr by lia.
        pose proof F_evu12 as E12. change (v 12) with (SVar 12) in E12. rewrite E12 in Hr. lia.
      + apply (ro_view_release segs rho2 ms m1 o w Hrom (proj1 (Forall_forall _ _) Hold2 o Ho) (RV2 o Ho' Hv)); [rewrite (RNG o Ho); exact Hr | exact (M2in w Hin)].
      + unfold obj_range, obj_lo_of, obj_hi_of, O_sct in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. rewrite (proj2 (proj2 (proj2 HCc))) in Hr.
        destruct F_ZONES2 as (G0 & RL & ZZ). rewrite !soff_lit_small, u64_of_sum in Hr by lia.
        assert (Hn2 : m2 w = None). { rewrite (M2in w Hin). apply Hroc. rewrite <- (Z_to_bv_bv_unsigned 64 w). replace (bv_unsigned w) with (mc_size_classes C + (bv_unsigned w - mc_size_classes C)) by lia. apply (proj1 (SCT (bv_unsigned w - mc_size_classes C) ltac:(lia))). }
        assert (Hn1 : m1 w = None). { rewrite <- (Z_to_bv_bv_unsigned 64 w). apply M1sct. lia. }
        unfold rd_of, wok_of. rewrite Hn1, Hn2. split; reflexivity.
    - unfold rd_of, wok_of. rewrite (M2out w Hni), Hrm2. split; reflexivity. }

  assert (HDR : obj_holds segs rho2 ms hdrX) by (apply (proj1 (Forall_forall _ _) Hold2); left; reflexivity).
  assert (E12 : bv_unsigned (eval rho2 (SVar 12)) = zP). { cbn [eval]. rewrite <- (AGw 12%positive) by reflexivity. pose proof F_evu12 as E. exact E. }
  destruct (hdr_bytes rho2 ms HDR E12) as (B4 & B3 & B2 & B1).
  assert (INH : forall x, zP - 4 <= x < zP -> in_ranges rho2 R2 (wz x)).
  { intros x Hx. exists hdrX. split; [left; reflexivity|]. rewrite (RNG hdrX ltac:(left; reflexivity)). unfold obj_range, obj_lo_of, obj_hi_of, hdrX. cbn [ob_base ob_lo ob_hi fst snd].
    pose proof F_evu12 as E. change (v 12) with (SVar 12) in E. rewrite !soff_lit_small, E, u64_of_sum by lia. lia. }

  assert (HMI2 : MInvI C [] (Some (g, i)) U0 A1 (rd_of segs m2) (wok_of segs m2) (m_vmmaps md)).
  { apply (FreeRelease.minv_release C s L g am i fr (rd_of segs m1) (rd_of segs m2) (wok_of segs m1) (wok_of segs m2) (m_vmmaps md) HMI1 FFx Hkind HSI HSD).
    - intros x Hx NTx. unfold MallocLayout.wz. unfold rtouched, gzp, gp in NTx. change (addr_of L (frame_ptr am i fr)) with zP in NTx.
      destruct (Z.eq_dec x (zP - 4)) as [-> | NE]; [| apply M2eq; rewrite u64_of_sum by lia; lia].
      pose proof F_rv_hdr4 as [R4 W4]. unfold rd_of, wok_of. unfold rd_of, wok_of in R4, W4. rewrite (M2in _ (INH (zP - 4) ltac:(lia))), B4.
      destruct (m1 (wz (zP - 4))) as [b1|] eqn:E1.
      + split; [exact (eq_sym R4) | reflexivity].
      + split; [exact (eq_sym R4) | symmetry; exact W4].
    - intros x Tx. unfold MallocLayout.wz. unfold rtouched, gzp, gp in Tx. change (addr_of L (frame_ptr am i fr)) with zP in Tx. unfold rnew, gzp, gp. change (addr_of L (frame_ptr am i fr)) with zP.
      unfold rd_of, wok_of. rewrite (M2in _ (INH x ltac:(lia))).
      destruct (Z.eq_dec x (zP - 3)) as [-> | NE3]; [rewrite B3, Z.eqb_refl; split; reflexivity|].
      replace (x =? zP - 3) with false by (symmetry; apply Z.eqb_neq; lia).
      destruct (Z.eq_dec x (zP - 2)) as [-> | NE2]; [rewrite B2; split; reflexivity|].
      replace x with (zP - 1) by lia. rewrite B1; split; reflexivity.
    - intros x Hx. unfold MallocLayout.wz. unfold gzp, gp, gn in Hx. change (addr_of L (frame_ptr am i fr)) with zP in Hx. change (fr_n fr) with n in Hx. exact (M1blk x Hx). }
  split; [|split; [exact HMI2|]].
  -
    rewrite Xc_eq. unfold XcG.
    destruct Hsm1 as (Hwf & Hpc & Hpend & Hhalt & Hrom' & Hroc' & Hr & Hf & Hc & Hv & Hm & Hfa). cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
    pose proof (proj1 (Xc_swf x0)) as SW. rewrite Xc_eq in SW. unfold XcG in SW.
    split; [exact SW|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom'|]. split; [exact Hroc'|].
    split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [exact Hm|].
    apply Forall_cons; [|exact Hfa].

    destruct Hm as (Hall & _ & _). pose proof (X_nt_stk x0) as (OB & INC & _).
    destruct (firstn 1 (ss_objs (X_nt x0))) as [|o [|]]; try discriminate OB. cbn [map] in OB. injection OB as Eb El Eh.
    pose proof (Forall_inv Hall) as HO.
    assert (HF3 : Forall (SymState.holds rho3) F_win_facts) by (apply (Forall_inclb rho3 _ (ss_facts (X_nt x0))); [exact INC | exact Hfa]).
    pose proof (window_facts segs rho3 ms free_stack o ltac:(unfold free_stack; lia) HF3 Eb El HO) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
    cbn [SymState.holds eval]. rewrite u64_of_sum by lia. unfold free_stack in W1. lia.
  - intros x Hx NO NS. destruct (in_ranges_dec rho2 R2 (wz x)) as [Hin | Hni]; [| rewrite (M2out _ Hni); apply Hrm2].
    pose proof Hin as (o & Ho & Hr). rewrite (RNG o Ho), u64_of_sum in Hr by lia.
    destruct (R2_zone o x Ho Hr) as [OW | [ST | TB]]; [exfalso; exact (NO OW) | exfalso; exact (NS ST) |].
    rewrite (M2in _ Hin), M1sct by exact TB. apply Hroc. replace x with (mc_size_classes C + (x - mc_size_classes C)) at 1 by lia. apply (proj1 (SCT (x - mc_size_classes C) ltac:(lia))).
Qed.

Lemma depth_shift : ltac2:(tb__ "0|4|
S1bS43S10cZ40M0S7aQ40M1S1eR1PfM2A2A2A2N1d0A2S43S49S47Z2Z28A2A1S10cG0S7aG1S1eR2G2A2A2A2A2S1S6S10cG0S7aG1S2cR3S27S107S20G2A1S22Z30M3A1A3A2A2A2S44S10cG0S7aG1S1eR3G2A2A2A2G3A2A3F_;F_;Frho;").
Proof using C Kc okK.
  intros rho D1 D2. rewrite (eval_zeval rho) by reflexivity. cbn [zeval zalu]. unfold zr_of.
  pose proof (urange (rw rho 15%positive)) as U. set (u := bv_unsigned (rw rho 15%positive)) in *.
  change (48 mod 2 ^ 64) with 48. rewrite (Z.mod_small u) by lia.
  unfold toS in *. rewrite (Z.mod_small u) in D1, D2 by lia. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (u <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia | apply Z.ltb_ge in E].
  rewrite !(Z.mod_small (u + 48)), !(Z.mod_small u) by lia. replace (u + 48 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). replace (u <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Theorem L_Xnt : ltac2:(tb__ "0|0|
S1bS24Sb0SdaVL;Vg;Vam;Vi;Vfr;S11aS105VrhoE;Vm1;A2P89S7cQ40Sf5Vam;Vfr;A2A2A3A6R1A3VTR;SaaVsegs;S101VX_nt;SfdA1R2A4VQF;A2F_;Frho2;").
Proof using CONT0 CONT1 ERRIMG ERRLK Ev_misc Ev_ok HCc HMI1 HORD HSD HSI HTP HTPv HtopE Harea Hfr Hkind HnC HpC Hrc JIN JOUT M1blk M1out M1sct N0_ent N0_eq N1_ent N1_eq NLW NT N_swf RA_ok RA_shape SCT TN_ok TN_stk TR_callP TR_inhP TR_pre WSEG X_nt_objs X_nt_shape X_nt_stk Xc_eq Xc_swf Xs_ok call_ok imp_res okK sA_regs.
  intros rho2 Hag2. apply TR_inhP. intros w0 [Hsm0 HK0w]. destruct w0 as [tr [ms mdx]]. cbn [w_tr w_cfg fst snd cfg_model] in HK0w.
  destruct HK0w as (HKc & Etr & Emd). subst tr mdx.
  destruct (at_cut rho2 tr0 ms Hag2 Hsm0) as (HsmC & HMI2 & M2M1).
  set (m2 := release_mem rho2 R2 ms) in *. set (rho3 := mkVal (rw rho2) (rl rho2) m2) in *.
  exists (SP segs K0 (Xc x0) rho3). split; [split; [exact HsmC | cbn [w_tr w_cfg fst snd cfg_model]; split; [exact HKc | split; reflexivity]]|]. clear Hsm0.
  pose proof Hag2 as (AGw & AGl & AGm). pose proof NUMSx as N. top_ranges.
  assert (Hrw3 : forall j, (j < FS_NEXT)%positive -> rw rho3 j = rw rhoF j) by (intros j Hj; cbn [rho3 rw]; symmetry; apply AGw; exact Hj).

  pose proof HsmC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallC & _ & _) & HfactsC). cbn [fst snd cfg_ms cfg_model] in HallC, HfactsC.
  pose proof (X_nt_stk x0) as (OB & INC & _).
  assert (HF3 : Forall (SymState.holds rho3) F_win_facts).
  { apply (Forall_inclb rho3 _ (ss_facts (Xc x0))); [|exact HfactsC]. rewrite Xc_eq. cbn [XcG ss_facts].
    unfold inclb in INC |- *. apply forallb_forall. intros f Hf. cbn [existsb]. apply Bool.orb_true_intro. right. exact (proj1 (forallb_forall _ _) INC f Hf). }
  assert (OBC : exists o, ss_objs (Xc x0) = [o] /\ ob_base o = SVar 10 /\ ob_lo o = SVar V_DEPTH /\ ob_hi o = SLit 0).
  { rewrite Xc_eq. cbn [XcG ss_objs]. destruct (firstn 1 (ss_objs (X_nt x0))) as [|o [|]]; try discriminate OB. cbn [map] in OB. injection OB as Eb El Eh. exists o. auto. }
  destruct OBC as (oC & EobjC & Eb & El & Eh). rewrite EobjC in HallC. pose proof (Forall_inv HallC) as HOC.
  pose proof (window_facts segs rho3 ms free_stack oC ltac:(unfold free_stack; lia) HF3 Eb El HOC) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
  unfold free_stack in W1. set (sp := bv_unsigned (rw rho3 10%positive)) in *.
  assert (RR : forall a0, in_ranges rho3 (RA x0) a0 <-> sp - 48 <= bv_unsigned a0 < sp).
  { intros a0. pose proof (RA_shape x0) as P6. destruct (RA x0) as [|o [|o2 R2']]; try discriminate P6. cbn in P6. injection P6 as Hb' Hl' Hh'.
    unfold in_ranges. split.
    - intros (o1 & [<- | []] & Hr). unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb', Hl', Hh' in Hr. cbn [fst snd eval] in Hr. rewrite !soff_lit_small in Hr by (clear; lia). clear - Hr. lia.
    - intros Hr. exists o. split; [left; reflexivity|]. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb', Hl', Hh'. cbn [fst snd eval]. rewrite !soff_lit_small by (clear; lia). clear - Hr. lia. }

  eapply TR_pre with (P := SP segs K0 (Ev x0) rho3).
  { intros w HSP. apply (SPJ_unbase segs (liftK K0) rho3 (Xs x0) 0 (-48) (Ev x0) w (Ev_ok x0)). exact (SP_xforms segs K0 _ rho3 (Xc x0) (Xs x0) w (Xs_ok x0) HSP). }
  pose proof (Ev_misc x0) as (EvF & EvN & EvPC & EvO1 & EvO2). pose proof (sA_regs x0) as (S10 & S15 & S24 & S12 & S13).

  assert (E310 : rw rho3 10%positive = rw rhoE 10%positive /\ rw rho3 15%positive = rw rhoE 15%positive).
  { pose proof F_rhoF_rw_low as RL. rewrite (Hrw3 10%positive), (Hrw3 15%positive) by (cbv; reflexivity). rewrite (RL 10%positive), (RL 15%positive) by (cbv; reflexivity). cbn [rw set_rm]. split; reflexivity. }
  assert (TOPW : topL L <= sp + toS 64 (bv_unsigned (rw rho3 15%positive))).
  { pose proof HtopE as T. unfold top_high, V_DEPTH in T. cbn [ma_L] in T. unfold sp. rewrite (proj1 E310), (proj2 E310). exact T. }
  assert (TOPC : forall msx, top_high A1 (rho_sub (rho_absorb rho3 (RA x0) msx) (sA x0))).
  { intros msx. apply (U.Mal_mdirect__G2.Mal_mdirect_C.top_high_frame (mkMA s L) A1 rho3 _ 48);
      [reflexivity | unfold sp in *; clear - W1 W3 TOPW; lia | change V_DEPTH with 15%positive; clear - W1 W2; lia | change V_DEPTH with 15%positive; clear - W1 W2; lia
      | cbn [rho_sub rw]; rewrite S10; reflexivity | cbn [rho_sub rw]; change V_DEPTH with 15%positive; rewrite S15; reflexivity |].
    unfold top_high. cbn [ma_L]. rewrite (proj1 E310). change V_DEPTH with 15%positive. rewrite (proj2 E310). pose proof HtopE as T. unfold top_high, V_DEPTH in T. cbn [ma_L] in T. exact T. }
  apply (TR_callP (liftK K0) Jp (Ev x0) (PreN e) (sA x0) (RA x0) [(LN e, JLp)] QF rho3 (RA_ok x0) (call_ok x0) NT).
  -
    intros tr ms' mdx Hsm [HKc' [-> ->]]. apply JIN. unfold nt_in_facts. cbn [rho_sub rw].
    rewrite S12, S13, S24. rewrite !eval_absorb.
    split. { cbn [eval]. rewrite Hrw3 by reflexivity. pose proof F_evu132 as E. cbn [eval Mal_get_meta.v] in E. rewrite E. reflexivity. }
    split. { destruct F_xof_cases as [(kx & EX & K) | (kx & EX & K)]; unfold x0; rewrite EX; cbn [idx_of].
             - rewrite (eval_agree_vars (fun v => Pos.ltb v FS_NEXT) rho3 rhoF); [| intros q Hq; apply Hrw3; apply Pos.ltb_lt; exact Hq | intros l; cbn [rho3 rl]; symmetry; apply AGl | reflexivity].
               rewrite (eval_zeval rhoF) by reflexivity. pose proof F_ze_ffidx as E. unfold ff_idx, Mal_get_meta.v in E. symmetry. exact E.
             - cbn [eval]. rewrite u64_of_sum by (clear; lia). destruct kx; cbn [kindok] in K; pose proof F_NUMS as NN; cbn zeta in NN; clear - K NN; lia. }
    split. { apply (MInvI_rm_ext segs C HSI HSD [] (Some (g, i)) U0 A1 m2 _ (m_vmmaps md) HMI2 (Zones2.xraw_nil _)).
             - cbn [ma_s A1 s1]. exact (ff_init _ _ _ _ _ FFx).
             - intros a0 Ha0 Hlow. rewrite rm_absorb_out; [reflexivity|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by (clear - Ha0; lia). cbn [ma_L A1] in Hlow. clear - Hin Hlow W1 W4 TOPW. lia. }
    split; [exact (FreeRelease.R_u1 s g am i)|].
    split; [exact (FreeRelease.R_ring s g am i fr HW FFx)|].
    split. { unfold V_DEPTH. rewrite S15. cbn [rho3] in W1, W2 |- *. rewrite depth_shift by (cbn [rw]; clear - W1 W2; lia). cbn [rw]. clear - W1 W2. lia. }
    split; [exact (FreeRelease.R_reach s g am i fr FFx Hreach)|].
    split. { cbn [eval]. rewrite Hrw3 by reflexivity. pose proof F_rhoF_rw_low as RL. rewrite (RL 24%positive) by reflexivity. cbn [rw set_rm]. exact HTPv. }
    split; [exact HKc' | exact (TOPC ms')].
  -
    intros Lf JL tr ms' mdx rhoL tr' ms'' md' HinL Hsm [HKc' [-> ->]] Hag1 HsmL HJL.
    destruct HinL as [EL|[]]. injection EL as <- <-.
    set (rin := rho_sub (rho_absorb rho3 (RA x0) ms') (sA x0)) in *.
    destruct (JOUT _ _ _ _ HJL) as (A' & HM' & HL' & Hcorr & Hub & Hreach' & Hinit' & Hres & Hkept & HKcL).
    assert (KEPT : forall a0, in_ranges rho3 (RA x0) a0 -> rm rhoL a0 = rm rin a0).
    { intros a0 Hin. pose proof Hin as Hin'. apply RR in Hin'. rewrite <- (Z_to_bv_bv_unsigned 64 a0). pose proof (urange a0) as Ua.
      pose proof HSI as X; unfold statics_in_image in X; cbn beta zeta in X; unfold UNIT in X.
      assert (HI : topL L <= bv_unsigned a0) by (clear - Hin' W1 W4 TOPW; lia).
      apply Hkept; [exact Ua | | | unfold errno_range; clear - HI X; lia | unfold alloc_static; clear - HI X; lia].
      - intros [OW | LK]; [pose proof (alloc_owned_lowG C HSI [] (Some (g, i)) U0 A1 _ _ _ _ HMI2 OW) as H; cbn [ma_L A1] in H; clear - HI H; lia| clear - HI X LK; lia].
      - intros [OW | LK]; [pose proof (alloc_owned_lowG C HSI [] None U0 A' _ _ _ _ HM' OW) as H; rewrite HL' in H; clear - HI H; lia| clear - HI X LK; lia]. }
    split. { split; [exact KEPT|]. intros o' oR Hin' _. cbn in Hin'. destruct Hin'. }
    intros rho' Hlink. apply TR_inhP. intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
    clear A' HM' HL' Hcorr Hub Hreach' Hinit' Hres Hkept HKcL.
    destruct (JOUT _ _ _ _ HJ') as (A' & HM' & HL' & Hcorr & Hub & Hreach' & Hinit' & Hres & Hkept & HKcL).
    set (rhoP := rho_patch rho' (patchf rho3 rho' (RA x0))).
    assert (Hag' : agree_vals (ss_next (Ev x0)) rho3 rho') by (destruct Hlink as (X0 & _); exact X0).
    assert (HrmP : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (sp - 48 <= a0 < sp) -> rm rhoP (wz a0) = rm rhoL (wz a0)).
    { intros a0 Ha Hna. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
      destruct (in_ranges_dec rho3 (RA x0) (wz a0)) as [Hi | Hni]; [exfalso; apply RR in Hi; rewrite u64_of_sum in Hi by (clear - Ha; lia); clear - Hi Hna; lia|].
      eapply call_linkP_rm. exact Hlink. }
    assert (HrmPin : forall a0, 0 <= a0 < 2 ^ 64 -> sp - 48 <= a0 < sp -> rm rhoP (wz a0) = m2 (wz a0)).
    { intros a0 Ha Hr. unfold rhoP. cbn [rho_patch rm]. unfold patchf.
      destruct (in_ranges_dec rho3 (RA x0) (wz a0)) as [Hi | Hni]; [reflexivity|]. exfalso. apply Hni. apply RR. rewrite u64_of_sum by (clear - Ha; lia). clear - Hr. lia. }
    assert (RWP : forall j, (j < FS_NEXT)%positive -> rw rhoP j = rw rho3 j).
    { intros j Hj. unfold rhoP. cbn [rho_patch rw]. symmetry. apply (proj1 Hag' j). rewrite EvN. exact Hj. }

    pose proof (cont_smatch segs (Ev x0) (PreN e) (LN e) (sA x0) (RA x0) rho3 rho' tr0 ms' md w (RA_ok x0) Hsm eq_refl Hag' Hsm') as HsmT. fold rhoP in HsmT.
    pose proof (smatch_xforms segs _ _ _ (TN x0) _ (TN_ok x0) HsmT) as HsmN.
    destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in HKcL, HM' |- *.
    assert (HMP : MInvI C [] None U0 A' (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps mdw)).
    { apply (MInvI_rm_ext segs C HSI HSD [] None U0 A' (rm rhoL) (rm rhoP) _ HM' (Zones2.xraw_nil _) Hinit'). intros a0 Ha Hlow. rewrite HL' in Hlow. apply HrmP; [exact Ha | clear - Hlow W1 W4 TOPW; lia]. }
    pose proof HsmN as (_ & _ & _ & _ & HromN & _ & _ & _ & _ & _ & (HallN & _ & _) & HfactsN). cbn [fst snd cfg_ms cfg_model] in HromN, HallN, HfactsN.
    pose proof (TN_stk x0) as (OBN & INCN & NXN & SPN & PCN).
    assert (HF3' : Forall (SymState.holds rhoP) F_win_facts) by (apply (Forall_inclb rhoP _ (ss_facts (TN x0))); [exact INCN | exact HfactsN]).
    destruct (ss_objs (TN x0)) as [|oN [|]] eqn:EON; try discriminate OBN. cbn [map] in OBN. injection OBN as Eb1 El1 Eh1.
    pose proof (Forall_inv HallN) as HO1.
    pose proof (window_facts segs rhoP msw free_stack oN ltac:(unfold free_stack; lia) HF3' Eb1 El1 HO1) as (V1 & V2 & V3 & V4 & V5 & V6 & VS). unfold free_stack in V1.
    assert (Esp : bv_unsigned (rw rhoP 10%positive) = sp) by (unfold sp; rewrite RWP by reflexivity; reflexivity).
    rewrite Esp in V3, V4, V5, V6.
    pose proof HSI as SI. unfold statics_in_image in SI. cbn beta zeta in SI. unfold CTX_SIZE, PGSZ, UNIT in SI.

    assert (RGL : obj_range rhoP (O_lock c) = (mc_lock C + 0, mc_lock C + 4)).
    { unfold obj_range, obj_lo_of, obj_hi_of, O_lock. cbn [ob_base ob_lo ob_hi eval]. rewrite (proj1 (proj2 (proj2 HCc))). rewrite u64_of_sum, !soff_lit_small by (clear - SI; lia). reflexivity. }
    assert (R24P : bv_unsigned (rw rhoP 24%positive) = mc_tp C).
    { rewrite RWP by reflexivity. rewrite Hrw3 by reflexivity. pose proof F_rhoF_rw_low as RL. rewrite (RL 24%positive) by reflexivity. cbn [rw set_rm]. exact HTPv. }
    assert (RGE : forall rhoX, bv_unsigned (rw rhoX 24%positive) = mc_tp C -> obj_range rhoX O_errnoF = (mc_errno C + 0, mc_errno C + 4)).
    { intros rhoX HX. unfold obj_range, obj_lo_of, obj_hi_of, O_errnoF. cbn [ob_base ob_lo ob_hi eval]. rewrite HX, !soff_lit_small by (clear; lia). unfold mc_errno. f_equal; clear; lia. }
    assert (RGS : obj_range rhoP oN = (sp + toS 64 (bv_unsigned (rw rhoP 15%positive)), sp + 0)).
    { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb1, El1, Eh1. unfold V_DEPTH. cbn [eval]. rewrite Esp, VS, soff_lit_small by (clear; lia). reflexivity. }

    assert (RF0 : forall rho4, (forall j, (j < NF)%positive -> rw rho4 j = rw rhoP j) -> (forall l, rl rho4 l = rl rhoP l) -> rm rho4 = rm rhoP -> ret_facts A' rho4).
    { intros rho4 R4w R4l R4m. unfold ret_facts.
      split; [exact HL'|]. split; [exact Hreach'|]. split; [exact Hinit'|]. split.
      { destruct (FreeRelease.R_blocks s g am i fr HW FFx Hkind L) as (l1 & l2 & E1 & E2). exists l1, l2. split; [exact E1|].
        destruct A' as [s' L'']. cbn [ma_s ma_L] in *. subst L''. unfold ma_blocks, blocks. cbn [ma_s ma_L]. unfold blocks in E2.
        rewrite (ub_same_user_blocks s1 s' (proj1 (inv_keys (mig_I HMI2))) (proj1 (inv_keys (mig_I HM'))) Hub). exact E2. }
      split. { intros j Hj. rewrite (R4w j Hj), RWP by (clear - Hj; unfold NF, FS_NEXT in *; lia). rewrite Hrw3 by (clear - Hj; unfold NF, FS_NEXT in *; lia).
               pose proof F_rhoF_rw_low as RL. rewrite (RL j) by (clear - Hj; unfold NF in Hj; lia). reflexivity. }
      split. { intros l. rewrite R4l. unfold rhoP. cbn [rho_patch rl]. rewrite <- (proj2 Hag' l). cbn [rho3 rl]. symmetry. apply AGl. }
      intros a0 Ha HcA HcA' NE NS. rewrite R4m.
      assert (HMI4 : MInv C A' (rd_of segs (rm rhoP)) (wok_of segs (rm rhoP)) (m_vmmaps mdw)) by (apply (proj2 (MInv_MInvI _ _ _ _ _)); split; [exact HMP | exact Hreach']).
      assert (NO : ~ ma_owned C A a0) by (apply (client_addr_not_owned segs C HSI WSEG A (set_rm rhoE m1) md a0); [unfold MInvR; cbn [rm set_rm]; exact HMI1 | exact HcA]).
      assert (NO' : ~ ma_owned C A' a0) by (apply (client_addr_not_owned segs C HSI WSEG A' rhoP mdw a0); [unfold MInvR; exact HMI4 | exact HcA']).
      assert (NB : ~ (zP <= a0 < zP + n)).
      { destruct (FreeRelease.R_blocks s g am i fr HW FFx Hkind L) as (l1 & l2 & E1 & E2). change (addr_of L (frame_ptr am i fr)) with zP in E1. change (fr_n fr) with n in E1.
        assert (EB' : ma_blocks A' = l1 ++ l2).
        { destruct A' as [s' L'']. cbn [ma_s ma_L] in *. subst L''. unfold ma_blocks, blocks. cbn [ma_s ma_L]. unfold blocks in E2.
          rewrite (ub_same_user_blocks s1 s' (proj1 (inv_keys (mig_I HMI2))) (proj1 (inv_keys (mig_I HM'))) Hub). exact E2. }
        intros Hb. destruct HcA' as [Hst | [(b & nb & Hin & Hr) | (Hw & _)]].
        - rewrite HL' in Hst. clear - Hb Hst N. lia.
        - pose proof (new_block_disjoint C A _ _ _ l1 l2 (zP, n) HMI1 E1 (b, nb) ltac:(rewrite <- EB'; exact Hin)) as D. unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. clear - Hb Hr D. lia.
        - pose proof (WSEG _ Hw) as X. rewrite u64_of_sum in X by exact Ha. destruct F_ZONES2 as (G0 & RL & ZZ). pose proof F_NUMS as NN. cbn zeta in NN. clear - Hb X ZZ NN. lia. }
      assert (M1E : m1 (wz a0) = rm rhoE (wz a0)) by (apply M1out; rewrite u64_of_sum by (clear - Ha; lia); clear - NB; lia).
      destruct (Z_le_dec (sp - 48) a0) as [Hge|Hlt]; [destruct (Z_lt_dec a0 sp) as [Hlt2|Hge2]|].
      - rewrite (HrmPin a0 Ha) by (clear - Hge Hlt2; lia). rewrite (M2M1 a0 Ha NO NS). exact M1E.
      - rewrite (HrmP a0 Ha) by (clear - Hge Hge2; lia). rewrite (Hkept a0 Ha); [| | exact NO' | exact NE | exact NS].
        + unfold rin. rewrite rm_absorb_out; [cbn [rho3 rm]; rewrite (M2M1 a0 Ha NO NS); exact M1E|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by (clear - Ha; lia). clear - Hin Hge2. lia.
        + intros [OW | LK]; [|apply NO; right; exact LK]. destruct (FreeRelease.R_own C s L g am i fr _ _ _ HMI1 FFx Hkind a0 OW) as [OW0 | BL]; [apply NO; left; exact OW0 | apply NB].
          unfold gzp, gp, gn in BL. exact BL.
      - rewrite (HrmP a0 Ha) by (clear - Hlt; lia). rewrite (Hkept a0 Ha); [| | exact NO' | exact NE | exact NS].
        + unfold rin. rewrite rm_absorb_out; [cbn [rho3 rm]; rewrite (M2M1 a0 Ha NO NS); exact M1E|]. intros Hin. apply RR in Hin. rewrite u64_of_sum in Hin by (clear - Ha; lia). clear - Hin Hlt. lia.
        + intros [OW | LK]; [|apply NO; right; exact LK]. destruct (FreeRelease.R_own C s L g am i fr _ _ _ HMI1 FFx Hkind a0 OW) as [OW0 | BL]; [apply NO; left; exact OW0 | apply NB].
          unfold gzp, gp, gn in BL. exact BL. }

    set (TL := mkSS (ss_pc (TN x0)) (ss_regs (TN x0)) (ss_fregs (TN x0)) (ss_fcsr (TN x0)) (ss_resv (TN x0)) (ss_objs (TN x0) ++ [O_lock c]) (ss_facts (TN x0)) (ss_next (TN x0)) (ss_lenient (TN x0))).
    pose proof (N_swf x0) as (SW0 & SW1 & V182).
    assert (HLK : obj_holds segs rhoP (with_mem msw (rm rhoP)) (O_lock c)) by (apply (hold_lockI [] None U0 A' (rm rhoP) rhoP msw (or_intror (ex_intro _ (m_vmmaps mdw) HMP)) HromN)).
    assert (DLK : SymState.ranges_disjoint (obj_range rhoP oN) (obj_range rhoP (O_lock c))).
    { rewrite RGS, RGL. unfold SymState.ranges_disjoint; cbn [fst snd]. clear - V1 V4 SI. lia. }
    assert (HsmTL : smatch segs rhoP TL (trw, mkCfg msw mdw)).
    { apply (smatch_extend_objs segs rhoP (TN x0) trw msw mdw [O_lock c] (ss_next (TN x0))); [exact HsmN | | | |].
      - pose proof SW0 as W. rewrite N0_eq in W. unfold addOF in W. rewrite ?EON in W |- *.
        exact (swf_drop_facts _ _ _ _ _ _ _ _ _ _ W).
      - constructor; [exact HLK | constructor].
      - constructor; [|constructor]. rewrite ?EON. constructor; [|constructor]. exact DLK.
      - cbn. split; [constructor | exact I]. }
    clear HsmT.

    pose proof (imp_res x0) as [IB IL].
    assert (LK4 : forall v, rw rhoL v = eval rho' (wsub_get (import_sub (sA x0) NF (LN e) (ss_next (Ev x0))) v) -> forall q, wsub_get (import_sub (sA x0) NF (LN e) (ss_next (Ev x0))) v = SVar q -> rw rhoP q = rw rhoL v).
    { intros v Hv q Hq. rewrite Hv, Hq. reflexivity. }
    destruct Hlink as (_ & _ & _ & L4).
    assert (EB : rw rhoP V_BASE = rw rhoL V_RES).
    { apply (LK4 V_RES); [|exact IB]. apply L4; [reflexivity | cbv; clear; lia]. }
    assert (ELN : rw rhoP V_LEN = rw rhoL V_RES1).
    { apply (LK4 V_RES1); [|exact IL]. apply L4; [reflexivity | cbv; clear; lia]. }
    destruct Hres as [(Hlen0 & Hbase0 & HXP0) | (Hlenpos & kr & rg & Hrg & Hrk & Hrl & Hrlen & Hrbase & Hnom & HXP1)].
    +
      assert (F0 : Forall (SymState.holds rhoP) [SPBranch BC_EQ (SVar V_LEN) (SLit 0)]).
      { constructor; [|constructor]. cbn [SymState.holds eval branch_taken]. unfold bv_eqb. apply Z.eqb_eq. rewrite ELN, u64_of_sum by (clear; lia). exact Hlen0. }
      assert (B0 : forallb (sprop_below (ss_next TL)) [SPBranch BC_EQ (SVar V_LEN) (SLit 0)] = true) by (unfold TL; cbn; rewrite NXN; reflexivity).
      pose proof (smatch_add_facts segs rhoP _ TL _ HsmTL F0 B0) as HsmN0.
      unfold add_facts, TL in HsmN0. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in HsmN0.
      replace (mkSS (ss_pc (TN x0)) (ss_regs (TN x0)) (ss_fregs (TN x0)) (ss_fcsr (TN x0)) (ss_resv (TN x0)) (ss_objs (TN x0) ++ [O_lock c])
                    ([SPBranch BC_EQ (SVar V_LEN) (SLit 0)] ++ ss_facts (TN x0)) (ss_next (TN x0)) (ss_lenient (TN x0))) with (N0 x0) in HsmN0
        by (rewrite N0_eq; reflexivity).
      destruct (N0_ent x0) as (HE & HID & S180 & S181).
      pose proof (entails_sound segs (N0 x0) (D_ret c e true) _ _ _ HE HsmN0) as Hsm4.
      set (rho4 := rho_sub rhoP (infer_sub NF (N0 x0) (D_ret c e true))) in Hsm4.
      exists (SP segs (K1 A' (rm rho4)) (D_ret c e true) rho4). split; [split; [exact Hsm4 | split; [exact HKcL | exact HMP]]|].
      apply (CONT0 A' rho4).
      * apply RF0; [intros j Hj; unfold rho4; cbn [rho_sub rw]; rewrite (wsub_get_id _ NF j HID Hj); reflexivity | intros l; reflexivity | reflexivity].
      * unfold rho4. cbn [rho_sub rw]. rewrite S181. cbn [eval]. rewrite ELN. exact Hlen0.
      * exact HXP0.
    +
      set (rhoQ := rho_set_rw rhoP 182%positive (errno_word (rm rhoP))).
      assert (RWQ : forall v, v <> 182%positive -> rw rhoQ v = rw rhoP v) by (intros v Hv; unfold rhoQ; rewrite rho_set_rw_other by (intros E; apply Hv; rewrite E; reflexivity); reflexivity).
      assert (HsmNQ : smatch segs rhoQ (TN x0) (trw, mkCfg msw mdw)).
      { apply (smatch_agree_vars segs (fun v => negb (Pos.eqb v 182)) rhoP rhoQ (TN x0)); [intros v Hv; symmetry; apply RWQ; intros ->; discriminate Hv | intros l; reflexivity | reflexivity | exact V182 | exact HsmN]. }
      set (TE := mkSS (ss_pc (TN x0)) (ss_regs (TN x0)) (ss_fregs (TN x0)) (ss_fcsr (TN x0)) (ss_resv (TN x0)) (ss_objs (TN x0) ++ [O_lock c; O_errnoF]) (ss_facts (TN x0)) (ss_next (TN x0)) (ss_lenient (TN x0))).
      assert (R24Q : bv_unsigned (rw rhoQ 24%positive) = mc_tp C) by (rewrite RWQ by discriminate; exact R24P).
      assert (OV : obj_vars_all (fun v => negb (Pos.eqb v 182)) oN = true).
      { pose proof V182 as X. unfold state_vars_all in X. rewrite EON in X. apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. cbn [forallb] in X. apply andb_prop in X as [X _]. exact X. }
      assert (RGSQ : obj_range rhoQ oN = obj_range rhoP oN).
      { apply (obj_range_agree_vars (fun v => negb (Pos.eqb v 182)) rhoP rhoQ oN); [intros v Hv; symmetry; apply RWQ; intros ->; discriminate Hv | intros l; reflexivity | exact OV]. }
      assert (RGLQ : obj_range rhoQ (O_lock c) = (mc_lock C + 0, mc_lock C + 4)).
      { rewrite <- RGL. apply (obj_range_agree_vars (fun v => negb (Pos.eqb v 182)) rhoP rhoQ (O_lock c)); [intros v Hv; symmetry; apply RWQ; intros ->; discriminate Hv | intros l; reflexivity | unfold O_lock; reflexivity]. }
      assert (HsmE : smatch segs rhoQ TE (trw, mkCfg msw mdw)).
      { apply (smatch_extend_objs segs rhoQ (TN x0) trw msw mdw [O_lock c; O_errnoF] (ss_next (TN x0)) HsmNQ).
        - pose proof SW1 as W. rewrite N1_eq in W. unfold addOF in W. unfold TE. rewrite ?EON in W |- *. exact (swf_drop_facts _ _ _ _ _ _ _ _ _ _ W).
        - constructor; [apply (hold_lockI [] None U0 A' (rm rhoQ) rhoQ msw (or_intror (ex_intro _ (m_vmmaps mdw) HMP)) HromN)|]. constructor; [|constructor].
          change O_errnoF with (carved (SVar 24) (-164) (-160) [(-164, 4%nat, v 182)]).
          apply (obj_holds_frame_lit segs rhoQ msw (rm rhoQ) (SVar 24) (-164) (-160) [(-164, 4%nat, v 182)] HromN); cbn [eval]; rewrite ?R24Q; [clear; lia | clear; lia | clear; lia | clear - HTP; lia | clear - HTP; lia | | |].
          -- constructor; [cbn; clear; lia | constructor].
          -- intros off Hoff. replace (mc_tp C + off) with (mc_errno C + Z.of_nat (Z.to_nat (off + 164))) by (unfold mc_errno; clear - Hoff; lia).
             destruct (errno_bytes (rm rhoQ) (Z.to_nat (off + 164)) ltac:(clear - Hoff; lia)) as (b & Hb & Hw). split; [exact Hw | exists b; exact Hb].
          -- constructor; [|constructor]. intros j Hj. replace (mc_tp C + -164 + Z.of_nat j) with (mc_errno C + Z.of_nat j) by (unfold mc_errno; clear; lia).
             change (rm rhoQ) with (rm rhoP). rewrite (errno_word_bytes (rm rhoP) j Hj); try reflexivity; f_equal; f_equal; unfold Mal_get_meta.v; cbn [eval]; unfold rhoQ; rewrite rho_set_rw_at; reflexivity.
        - rewrite EON. constructor; [|constructor; [|constructor]]; (constructor; [|constructor]).
          -- rewrite RGSQ, RGS, RGLQ. unfold SymState.ranges_disjoint; cbn [fst snd]. clear - V1 V4 SI. lia.
          -- rewrite RGSQ, RGS, (RGE rhoQ R24Q). unfold SymState.ranges_disjoint; cbn [fst snd]. clear - V1 V4 SI. unfold mc_errno in *. lia.
        - cbn. split; [|split; [constructor | exact I]]. constructor; [|constructor]. rewrite RGLQ, (RGE rhoQ R24Q). unfold SymState.ranges_disjoint; cbn [fst snd]. clear - ERRLK. lia. }
      assert (F1 : Forall (SymState.holds rhoQ) [SPNot (SPBranch BC_EQ (SVar V_LEN) (SLit 0)); SPUle (SVar 182) (SLit 4294967295)]).
      { constructor; [|constructor; [|constructor]].
        -- cbn [SymState.holds eval branch_taken]. rewrite RWQ by discriminate. rewrite ELN. intros X. unfold bv_eqb in X. apply Z.eqb_eq in X.
           rewrite u64_of_sum in X by (clear; lia). clear - X Hlenpos. lia.
        -- cbn [SymState.holds eval]. unfold rhoQ. rewrite rho_set_rw_at. rewrite u64_of_sum by (clear; lia). pose proof (errno_word_small (rm rhoP)). pose proof (urange (errno_word (rm rhoP))). clear - H H0. lia. }
      assert (B1 : forallb (sprop_below (ss_next TE)) [SPNot (SPBranch BC_EQ (SVar V_LEN) (SLit 0)); SPUle (SVar 182) (SLit 4294967295)] = true) by (unfold TE; cbn; rewrite NXN; reflexivity).
      pose proof (smatch_add_facts segs rhoQ _ TE _ HsmE F1 B1) as HsmN1.
      unfold add_facts, TE in HsmN1. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in HsmN1.
      replace (mkSS (ss_pc (TN x0)) (ss_regs (TN x0)) (ss_fregs (TN x0)) (ss_fcsr (TN x0)) (ss_resv (TN x0)) (ss_objs (TN x0) ++ [O_lock c; O_errnoF])
                    ([SPNot (SPBranch BC_EQ (SVar V_LEN) (SLit 0)); SPUle (SVar 182) (SLit 4294967295)] ++ ss_facts (TN x0)) (ss_next (TN x0)) (ss_lenient (TN x0))) with (N1 x0) in HsmN1
        by (rewrite N1_eq; reflexivity).
      destruct (N1_ent x0) as (HE & HID & S180 & S181 & S182).
      pose proof (entails_sound segs (N1 x0) (D_ret c e false) _ _ _ HE HsmN1) as Hsm4.
      set (rho4 := rho_sub rhoQ (infer_sub NF (N1 x0) (D_ret c e false))) in Hsm4.
      exists (SP segs (K1 A' (rm rho4)) (D_ret c e false) rho4). split; [split; [exact Hsm4 | split; [exact HKcL | exact HMP]]|].
      apply (CONT1 A' rho4).
      * apply RF0; [intros j Hj; unfold rho4; cbn [rho_sub rw]; rewrite (wsub_get_id _ NF j HID Hj); cbn [eval]; apply RWQ; unfold NF in Hj; intros ->; clear - Hj; lia | intros l; reflexivity | reflexivity].
      * unfold unmap_facts. unfold rho4. cbn [rho_sub rw]. rewrite S180, S181. cbn [eval]. rewrite !RWQ by discriminate. rewrite EB, ELN.
        split; [exact Hlenpos|]. exists kr, rg. split; [exact Hrg|]. split; [exact Hrk|]. split; [exact Hrl|]. split; [exact Hrlen|]. split; [exact Hrbase|]. split; [exact Hnom | exact HXP1].
Qed.

End T.
End CallSite.
End Mal_fslow_C.

Module Mal_fslow.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMain OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooterLemmas OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeQuickPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockViewIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.BlockView OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeRelease OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlowYield.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_slow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_quick OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G2.Mal_free_quick2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G1.Mal_fslow_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_I2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_CC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G3.Mal_fslow_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_fslow__G2.Mal_fslow_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].

Local Notation SP := SymSoundR.SP.
Local Notation wz := (Z_to_bv 64).

Section NTR.
Variables (segs : list Segment) (C : mconsts) (e : ntentry_consts).
Definition J_nt_preR (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|7|
S1bS8S73A1S72S7aQ40M0S1eR3PcA2A2S6S7aG0S1eR4PdA2A2S6S3S4eS4eS3S50S50S3S7bG0A1SdS7bQ8A1A1F_;M1G1S0S1S6S81S9bVA;A1M2R3A2R5A3S0SbeVC;VX;S11SaS4eS6A2S9S4eS6R3R4A4A2VU;VA;Sb9Vsegs;R1A2SbaVsegs;R1A2S74R6A1A8S0S13cG2VX;R1S21R8A1A4S0S13dVX;S98VA;A1M3A2S0ScbVX;G3R3R2A4S0S6S43Z0M4VU;R1A1A2Fc;S0S2S1SaSdS4eA1M5G5A2S9G5G5S61R2A1S60R2A1A4S9G5G5S13S4eA1M6G6A4A3A1S2S1G5SceG3S59R3A1A2S11S4eR4A2A3A1S2S1S6S5bR4A1G4A3A1F_;F_;S0S43S10cZ40S7aG0S1eR8Se9A2A2A2S49S13fU3A1A1A2S0S10bG3A1S0S1S6S7aG0S1eR8P18A2A2S86VC;A1A3S0VKc;R7R6A2SefVA;R8A2A2A2A2A2A2A2A2A2A2A2A2Lmv;A2Lam;A2Lg;A2Ti;Tga;Lmd;Ltr;Lrho;").
Definition JL_ntR (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|7|
S1bS1bS8S73A1S72S7aQ40M0S1eR3SedA2A2S6S7aG0S1eR4S13bA2A2S6S3S9aS9aS3S7bG0A1SdS7bQ8A1A1F_;M1G1S0SbeVC;VX;S13SaS4eS6A2A1VU;R2Sb9Vsegs;R1A2SbaVsegs;R1A2S74R5A1A8S0S13cS9bVA;A1M2VX;R1S21R7A1M3A4S0S13dVX;S98R2A1M4A2S0S1Sc8S9bR2A1G2A3S0S1SbS53G4A1ScA3S0S156VX;S98VA;A1M5G4A3S0S155G5G4A2S0S10bG4A1S0S4S0S1S6R3Z0M6A3S1S6R4G6A3A2S0S45G6R3A2S3SeSeS3S4fS4fS0S1SdS4fA1ScaS98R4A1R2A2S11S4fR1A2A3S0S1S58S56R1A1S55A3S0S1SbS57R1A1ScA3S0S1S6S5aR1A1S5eR5A1A3S0S1S6ScdS9bR4A1R2A2R6A3S4eS50ScbVX;S98R6A1R2R1A4S45G6S5cR2A1A2S2S1SeS5fS5dR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2Lrg;A2Lk;A2A2A2S0Sf0VC;VA;R2S21R8A1G3A5VKc;R6R5A2A2A2A2A2A2A2A2A2A2A2Lmv';A2LA';A2Tlen;Tbase;Lmd;Ltr;Lrho';Lrho0;").
Definition nt_contractR : Prop := ltac2:(tb__ "0|1|
S95OF_;S8S4eA1S6S6F_;S9aS8S73A1S72OF_;F_;S1bSeeVsegs;R6R2A3S97Vsegs;R7Sa9Vsegs;S166R6R5R4R3A4S13aVe;A1R2A4Sa0Vsegs;S7eR2SfSaS1dS9fA2M0S9S1dS9fS137Ve;A1S164R6R5R4R3A4A4S10G0A1A3A4A4F_;Frho;FKc;FA;FU;FX;Fok;").
Definition nt_contractR_ex : Prop := ltac2:(tb__ "0|1|
S8S4eA1S6S6F_;S9aS8S73A1S72OF_;F_;S1bSebR2A1S96Vsegs;Sa9Vsegs;S166R6R5R4R3A4S13aVe;A1R2A4Sa0Vsegs;S7eR2SfSaS1dS9fA2M0S9S1dS9fS137Ve;A1S164R6R5R4R3A4A4S10G0A1A3A4A3F_;Frho;FKc;FA;FU;FX;").

Definition J_nt_preRG (g : sptr) (i : Z) (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|7|
S1bS8S73A1S72S0S1S6S81S9bVA;A1M0Vg;A2S7aQ40M1S1eR3PcA2A2A3S0S1S6Vi;S7aG1S1eR3PdA2A2A3S3S50S50S3S7bG1A1SdS7bQ8A1A1F_;M2G2S0SbeVC;VX;S11SaS4eS6A2S9S4eS6Vg;Vi;A4A2VU;VA;Sb9Vsegs;R1A2SbaVsegs;R1A2S74R3A1A8S0S13cG0VX;R1S21R5A1A4S0S13dVX;S98VA;A1M3A2S0ScbVX;G3Vg;R2A4S0S6S43Z0M4VU;R1A1A2Fc;S0S2S1SaSdS4eA1M5G5A2S9G5G5S61R2A1S60R2A1A4S9G5G5S13S4eA1M6G6A4A3A1S2S1G5SceG3S59R3A1A2S11S4eVg;A2A3A1S2S1S6S5bR4A1G4A3A1F_;F_;S0S43S10cZ40S7aG1S1eR5Se9A2A2A2S49S13fU3A1A1A2S0S10bG3A1S0S1S6S7aG1S1eR5P18A2A2S86VC;A1A3S0VKc;R4R3A2SefVA;R5A2A2A2A2A2A2A2A2A2A2A2Lmv;A2Lam;A2A2A2Lmd;Ltr;Lrho;").
Definition JL_ntRY (g : sptr) (i : Z) (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|b|
S1bS1bS8S73A1S72S7aQ40M0S1eR3SedA2A2S6S7aG0S1eR4S13bA2A2S6S3S9aS9aS3S7bG0A1SdS7bQ8A1A1F_;M1G1S0SbeVC;VX;S13SaS4eS6A2A1VU;R2Sb9Vsegs;R1A2SbaVsegs;R1A2S74R5A1A8S0S13cS9bVA;A1M2VX;R1S21R7A1M3A4S0S13dVX;S98R2A1M4A2S0S1Sc8S9bR2A1G2A3S0S1SbS53G4A1ScA3S0S156VX;S98VA;A1M5G4A3S0S155G5G4A2S0S10bG4A1S0S3S8SaS62S6A2A1M6G6S3SdSaSeS6A2M7A1M8G8S0ScfSaG8S51A2S64S63Vg;Vi;G5A4R2S9G8S51R1S98R4A1A4A4S4S0S1G8R1S13G7A1A3S0S1S6R5Z0M9A3S1S6R6G9A3A2A2S3SeSeS3S4fS4fS0S1G8R3S11G7S9SeS6R2S5aR1A1MaA4A2A3S0S45G9R7A2S0S1SdS4fA1ScaS98R6A1R2A2S11S4fR1A2A3S0S1S58S56R1A1S55A3S0S1SbS57R1A1ScA3S0S1S6GaS5eR7A1A3S0S1S6ScdS9bR6A1R2A2R8A3S4eS50ScbVX;S98R8A1R2R1A4S45G9S5cR2A1A2S2S1SeS5fS5dR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2A2A2Lrg;A2Lk;A2A2A2Lmres;A2Lktr;A2S0Sf0VC;VA;R2S21R8A1G3A5VKc;R6R5A2A2A2A2A2A2A2A2A2A2A2Lmv';A2LA';A2Tlen;Tbase;Lmd;Ltr;Lrho';Lrho0;").
Definition nt_contractR_exd : Prop := ltac2:(tb__ "0|1|
S4eS6S8S4eA1S6S6F_;S9aS8S73A1S72OF_;F_;S1bS96Vsegs;Sa9Vsegs;S167R7R6R5R4R3R2A6S13aVe;A1R1A4Sa0Vsegs;S7eR1SfSaS1dS9fA2M0S9S1dS9fS137Ve;A1S165R7R6R5R4R3R2A6A4S10G0A1A3A4A3Frho;FKc;FA;FU;FX;Fi;Fg;").

Definition nt_contractR_d : Prop := ltac2:(tb__ "0|1|
S95OF_;S4eS6S8S4eA1S6S6F_;S9aS8S73A1S72OF_;F_;S1bSadVsegs;R8R2A3S97Vsegs;R9Sa9Vsegs;S167R8R7R6R5R4R3A6S13aVe;A1R2A4Sa0Vsegs;S7eR2SfSaS1dS9fA2M0S9S1dS9fS137Ve;A1S165R8R7R6R5R4R3A6A4S10G0A1A3A4A4F_;Frho;FKc;FA;FU;FX;Fi;Fg;Fok;").

Definition rsv32_stmt : Prop := ltac2:(tb__ "0|3|
S9aS7bQ40A1M0SdS7bQ8A1A1F_;G0SbF_;S75S4eS50S6S52S9dVC;R8R7R6R5A5Sc4SaSaSaS4eS50A2M1S6A2M2S52A2S9G2S52S9G1S6S9S4eS50R5R4A4R3A4R2A4Sd2S98R9A1A1A3S1S6S59R5A1Z3fA3S45S16eR6R4A2S47Z2Z20A2A2F_;F_;F_;Ffr;Fi;Fam;Fg;Fvm;Fwok;Frd;FA;").
End NTR.
Definition nt_contractR_P : Prop := ltac2:(tb__ "0|0|
S145S7dS80S138A3").
Definition nt_contractR_ex_P : Prop := ltac2:(tb__ "0|0|
S149S7dS80S138A3").
Definition nt_contractR_exd_P : Prop := ltac2:(tb__ "0|0|
S14bS7dS80S138A3").
Definition nt_contractR_d_P : Prop := ltac2:(tb__ "0|0|
S147S7dS80S138A3").
Definition nt_contractR_U : Prop := ltac2:(tb__ "0|0|
S145S7fS87S139A3").
Definition nt_contractR_ex_U : Prop := ltac2:(tb__ "0|0|
S149S7fS87S139A3").
Definition nt_contractR_exd_U : Prop := ltac2:(tb__ "0|0|
S14bS7fS87S139A3").
Definition nt_contractR_d_U : Prop := ltac2:(tb__ "0|0|
S147S7fS87S139A3").

Lemma vm_insensitive_munmap : ltac2:(tb__ "0|2|
S8S73A1M0S72OF_;F_;SebR1A1G0S72S7bQ40A1M1G1R6R4R3A2R7R5S117R4R3R2A3A2F_;Fk;Fa;Fmd;Ftr;F_;FKc;").
Proof. intros Kc HI tr md a k HK. unfold munmap_model, Mmap.with_mmap_destroyed. apply (vm_insensitive_forget Kc HI). apply (vm_insensitive_maps Kc HI). exact HK. Qed.

Module FP.
Import RP.
Definition C : mconsts := C_U.
Definition E : entry_consts := EC_U.
Lemma HSD : ltac2:(tb__ "0|d|
S6S4S0S43S85SbcA1M0R1A2S45R1S44G0SccA2A2A2S0S43S82SbcA1M1R1A2S45R1S44G1Z4M2A2A2A2A2S0S2S0S43S8cSbcA1M3R2A2S45R2S44G3Z38A2A2A2A1S0S2S0S43S88SbcA1M4R2A2S45R2S44G4G2A2A2A2A1S0S2S0S43S83SbcA1M5R2A2S45R2S44G5G2A2A2A2A1S0S2S0S43S84SbcA1M6R2A2S45R2S44G6Z60A2A2A2A1S0S2S0S43S8fSbcA1M7R2A2S45R2S44G7Z1bA2A2A2A1S0S2S0S43S8dSbcA1M8R2A2S45R2S44G8G2A2A2A2A1S0S2S0S43S8bSbcA1M9R2A2S45R2S44G9Z20A2A2A2A1S0S2S0S43S8aSbcA1MaR2A2S45R2S44GaZ8MbA2A2A2A1S2S0S43S89SbcA1McR2A2S45R2S44GcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;Fx;").
Proof.
  intros x Hx. unfold mc_errno in Hx. change C with C_U in Hx |- *.
  cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *. unfold CTX_SIZE in Hx. lia.
Qed.
Lemma ERRLK : ltac2:(tb__ "0|3|
S4S43S44S82SbcA1M0Z4M1A2S83SbcA1M2A2S43S44G2G1A2G0A2A2").
Proof. unfold mc_errno. cbn [mc_tp mc_lock C C_U]. lia. Qed.
Lemma HNE : ltac2:(tb__ "0|0|
S1S6S13eS127A1S157S124S126A1A1A3"). Proof. reflexivity. Qed.
Lemma LOCKW : ltac2:(tb__ "0|0|
S6S0S43Z0R1A2S45R1Z4A2A2S1SbSbbS128S7cQ40S44S83SbcA1R2A2A2A2ScA3F_;Fk;").
Proof. intros k Hk. exact (forall_range_dec (fun k => wseg_addr segs (wz (mc_lock C + k))) 0 4 ltac:(vm_compute; reflexivity) k ltac:(lia)). Qed.
Lemma Lfree_norl : ltac2:(tb__ "0|0|
S1SbS11eS16cSe7SbdA1A2S14A3"). Proof. vm_compute. reflexivity. Qed.
Lemma run_entry : ltac2:(tb__ "0|1|
S1SdS8S10dA1M0A1S10eS128U2SfS6S159S124S126A1A1S10S6A1A3Se4SbdA1ScA5S11G0SfS10dS112SfbS126A1S10fA2S10S10dA1A3A2A3"). Proof. OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.run_cast. Qed.
End FP.

Section Main.
Import RP CCP EP FP.
Let segs := segsU. Let C := C_U. Let E := EC_U.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame).
Variables (Kc : list event -> Model -> Prop) (rho : valuation).

Hypothesis KcM : ltac2:(tb__ "0|1|
S8S73A1S72S7bQ40A1M0G0VKc;R4R3A2VKc;R5S117R4R3R2A3A2F_;Fk;Fa;Fmd;Ftr;").
Hypothesis Hslow : ltac2:(tb__ "0|0|
Sf6Vs;Vg;Vam;Vi;Vfr;A5").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S1S6S81VL;Sc9Vam;Vi;Vfr;A3A2S7aQ40S1eVrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S1S6S54Vfr;A1S7aQ40S1eVrho;PdA2A2A3").
Hypothesis RSV : rsv32_stmt C.
Local Notation A := (mkMA s L).
Local Notation A1 := (mkMA (rs1 s g am i) L).

Variables (XP : MA -> option (nat * region) -> Prop) (XF : MA -> Prop) (JLX : jpost).
Hypothesis XF0 : ltac2:(tb__ "0|0|
S9aVXP;R1S13SaSeS4fA2A1A2VXF;R2A1F_;FA';").
Hypothesis XF1 : ltac2:(tb__ "0|0|
S51SeS4fVXP;S99R3VL;A2S11SaSeS4fA2S9SeS4fR2R1A4A2A2S1SdS4fA1ScaR4R3A2S11S4fR2A2A3S1S58S56R3A1S55A3S1SbS57R4A1ScA3VXF;S99S154R7R6R5A3VL;A2A1F_;F_;F_;F_;Frg;Fkr;Fs';").
Hypothesis MKPOST : ltac2:(tb__ "0|3|
S1bS24S7eVrho;R1A3S9aS1bS8S73A1S72S8SaS6S6A2M0A1M1G1SecVsegs;VC;R6R5R3A5S1SbS53S98R7A1A1ScA3S1Sc8S9bR8A1VL;A3S1G1S9cS99Vs;VL;A2M2A1S12G0R5SfG0S9S6S6Sd9VL;Vam;Vi;Vfr;A4Sf4Vfr;A1A4R4A3A3A3S1G1S9cRaA1S12G0R6R5A3A3SeaVsegs;VC;G2RbS21RdA1S21RaA1A6VKc;RaR9A2VXF;RdA1VJLX;R10RdRcRbA4F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmdx;Ftr;Frho';FA';F_;FrhoE;").
Hypothesis JLX_shift : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S24S7eVrho;R4A3VJLX;R5R4R3R2A4VJLX;Vrho;R5R4R3A4F_;F_;Fmdx;Ftr;Frho';FrhoE;").
Definition QF : assn := ltac2:(tb__ "0|1|
Sa0Vsegs;S7eVrho;SfSaS1dS9fA2M0S9S1dS9fSe7VE;A1VJLX;A4S10G0A1A3A4").

Lemma LQP_shift : ltac2:(tb__ "0|0|
S1bS24S7eVrho;R1A3S95S171Vsegs;VE;R3VJLX;R1A5S113R2A1F_;Fw;F_;FrhoE;").
Proof using JLX_shift.
  intros rhoE HagE [tr [ms md]] (Lf & JL & rho' & Hin & [AW AL] & Hsm & HJL). destruct Hin as [Ein|[]]. injection Ein as <- <-. pose proof HagE as (EW & EL & EM).
  exists (L_free E), JLX, rho'. split; [left; reflexivity|]. split; [|split; [exact Hsm|]].
  - split; [intros j Hj; rewrite (EW j Hj); apply AW; exact Hj | intros l; rewrite EL; apply AL].
  - cbn [w_tr w_cfg cfg_model snd] in HJL |- *. exact (JLX_shift rhoE rho' tr md HagE HJL).
Qed.

Section T.
Variable TR : assn -> assn -> Prop.
Variable okK : ltac2:(tb__ "0|0|
S8S73A1S72OF_;F_;OF_;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S94S94S94S95R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ';FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
S94S94S94S95R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_skip : ltac2:(tb__ "0|0|
S94S94S95R3R1A1R3R2A1F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_inhP : ltac2:(tb__ "0|0|
S94S94S95R3R1A1S3S94S94S0R1R3A1VTR;R1R4A2A2LP';A2F_;Fw;VTR;R3R2A2F_;FQ';FP;").
Hypothesis TR_seq : ltac2:(tb__ "0|1|
S94S94S94VTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ';FR';FP;").
Hypothesis TR_run : ltac2:(tb__ "0|1|
S8S73A1S72OF_;F_;S1dSeS8S10dA1M0S1bS94S1SdG0A1S10eVsegs;R4Sb8S126A1R5ScA5S11G0R3A2A3S1SbS38R6A1S14A3VokK;R8A1S10dS1bSc4S10dR2R8A3S24S23RbA1R8R2A3VTR;SaaVsegs;RdS111R4A1R3A4R8A2F_;F_;Frho';FLf;VTR;SaaVsegs;RaR9R6A4R5A2F_;F_;F_;F_;FQ';FrhoX;Fleaves;Ffuel;FS;FK;").
Hypothesis okK_of : ltac2:(tb__ "0|1|
S8S73A1M0S72OF_;F_;G0S72R3R2R1A2VKc;R3R2A2F_;Fmdx;Ftr;VokK;R2A1F_;FK;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
SabSabS1dS1dSc2S8S1fA1M0S8SaS1dS9fA2M1A1S94S1bS1SdG0A1S152R7R6R5A3S11G0R4A2A3S1SbSa1R8R7R6R5SdbG1S1dS15S1dS9fA2R4A4A5ScA3S1bVTR;Sa9Vsegs;RbR9R1A4Sa0Vsegs;S23R9A1R1R6A4A2Frho1;S8S73A1M2SdfS72S25Vsegs;R7RdS9G2Se2R3Se3R2R1A2A4A4R10R8R4R2A3R10Sc1Sc0R9RcR4A3RdA2R5R3A3F_;F_;Fmdx;Fms;Ftr;S1dS9fG2SdfS72S1bG2SdfS72Sc4G1S9S1dS9fR9R8A4R10A3S25Vsegs;RfR15S9G2Se2R8Se3R7R6A2A4A4R18R10R9R7A3Sa3S23R16A1Sc1Sc0R11R14R9A3R15A2R7A3S25Vsegs;R8RdS9G2Se2R7Se3R6R5A2A4A4RdSc1Sc0R13R16RbA3R17A2R9R8R6A4S0Sa5R14RcR17R18R19RfRaA7S1bSa4R15RdR18R19R1aR1bR10R1RbA9VTR;Sa9Vsegs;Sa2R10Sc1Sc0R16R19ReA3R1aA2RcA3Sa6R1aS23R1bA1R11S23R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmdx;Fms;Ftr;FJL;FLf;VTR;Sa9Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;FrhoX;FQ';FPosts;FR;Fsb;FPre;FCl;FJp;FJ;").
Hypothesis TR_munmap : ltac2:(tb__ "0|b|
S8S73A1M0S72OF_;F_;M1G1S1dS1bS1SdS109A1S110Vsegs;S29R2A1A2S11S109S10aA2A3S1S1cS31R3Z11A2S22Zd7A1A3VokK;R6A1G0SdfS72S11dVsegs;R7R8S9G0Se2R3Se3R2R1A2A4A4RbR4R2A2S0S1S6S4aS7aQ40M2Se0R4U0M3A2M4A2M5S78A2Z0M6A3S0S2S1S7bG2A1Se0R4U1M7A2M8S7cG2G6A2A3A1S0S43S44G5S119G8A1A2S76A2S0S1SbS77S79S74R3A1A1G4S118G8A1M9A3ScA3S0S1fSc4S1fR1S28RbA1A3S3cS37RbR2A2S9S6S6S7aG2Se0R6G3A2A2MaS44GaS119Se0R6G7A2A1A2A4A2F_;Fo;RbR5S117R3G4G9A3A2A2A2A2A2A2F_;F_;Fmdx;Fms;Ftr;VTR;SaaVsegs;R8R6R5A4SaaVsegs;R7S169R6G6A2S105R5S168S21R5A1S2cR5S31R6ZaA2A2S118S2cR5S31R6ZbA2A2A1A3A2A4A2F_;F_;F_;F_;FrhoX;FS;FK';FK;").

Variables (Jp : jpred) (JLp : jpost).
Hypothesis NT : ltac2:(tb__ "0|1|
S1bVTR;Sa9Vsegs;VJp;S12bS127A1R1A4Sa0Vsegs;S7eR1SfSaS1dS9fA2M0S9S1dS9fS129S127A1VJLp;A4S10G0A1A3A4A2Frho1;").
Hypothesis JIN : ltac2:(tb__ "0|0|
S1bS8S73A1S72S116Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;R3R2R1AbVJp;R4R3R2A3F_;Fmdx;Ftr;FrhoX;").
Hypothesis JOUT : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72VJLp;R4R3R2R1A4S115Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;VXP;R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").

Theorem slow_main : ltac2:(tb__ "0|0|
S1bS24S7eVrho;R1A3VTR;Sa9Vsegs;Se6Vsegs;VC;S99Vs;VL;A2VKc;A4SfbS126A1R2A4S113A2F_;FrhoE;").
Proof using HP12 HP13 Hslow JIN JLX_shift JOUT KcM MKPOST NT RSV TR_callP TR_inhP TR_munmap TR_post TR_pre TR_run TR_seq TR_skip XF0 XF1 okK_of.
  intros rhoE HagE. pose proof (MKPOST rhoE HagE) as MKPOSTE. apply TR_inhP. intros w [Hsm HJ]. destruct w as [tr0 [ms0 md]]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  pose proof HagE as (EW & EL & EM).
  assert (HP12' : addr_of L (frame_ptr am i fr) = bv_unsigned (rw rhoE 12%positive)) by (rewrite <- (EW 12%positive) by (cbv; reflexivity); exact HP12).
  assert (HP13' : fr_n fr = bv_unsigned (rw rhoE 13%positive)) by (rewrite <- (EW 13%positive) by (cbv; reflexivity); exact HP13).
  pose proof HJ as (HMI0 & _ & HKc & Htp & Hinit & HtopX).
  assert (Hrsv32 : am_sc am = 63 -> reserved_of am fr < 2 ^ 32) by (intros H63; exact (RSV A _ _ _ g am i fr HMI0 (proj1 Hslow) H63)).
  destruct (entry_P s L g am i fr Kc rhoE tr0 ms0 md Hsm HJ Hslow HP12' HP13' Hrsv32) as (m1 & a & k & Har & HsmD & HMI1 & M1out & M1in & MB & M1sct).
  exists (SP segs (U.Mal_fslow__G3.Mal_fslow_C.K0 Kc tr0 md) (D_call c (xof am fr)) (BlockView.rho1 L g am i fr (rho_set_rw (set_rm rhoE m1) 137%positive (Z_to_bv 64 (U.Mal_fslow__G1.Mal_fslow_I.rsv am fr))))).
  split; [split; [exact HsmD | cbn [w_tr w_cfg fst snd cfg_model]; split; [exact HKc | split; reflexivity]]|].

  apply (TR_run (U.Mal_fslow__G3.Mal_fslow_C.K0 Kc tr0 md) (D_call c (xof am fr)) 400%nat _ _ _ (run_call (xof am fr)) ltac:(destruct (xof am fr); reflexivity) (okK_of _ (fun tr mdx HK => proj1 HK))).
  intros Lf rho2 [<-|[]] Hag2. cbn [lf_state]. replace (ss_next (D_call c (xof am fr))) with FS_NEXT in Hag2 by (destruct (xof am fr); reflexivity).
  apply (TR_post _ (U.Mal_fslow__G2.Mal_fslow_T.QF segs E rhoE JLX) _ (LQP_shift rhoE HagE)).
  pose proof Hsm as (_ & _ & _ & _ & Hrom0 & _). cbn [fst snd cfg_ms] in Hrom0.
  assert (M1blk : forall x, BlockView.zP L am i fr <= x < BlockView.zP L am i fr + U.Mal_fslow__G1.Mal_fslow_I.n fr -> wok_of segs m1 (wz x) = true /\ exists b, rd_of segs m1 (wz x) = Some b).
  { intros x Hx. destruct (MB x Hx) as [W [b Rb]].
    pose proof (minv_block_geom C A _ _ _ _ _ HMI1 (U.Mal_fslow__G2.Mal_fslow_E.Hblocks s L g am i fr Hslow)) as (_ & _ & G0 & G & _). top_ranges.
    unfold wok_of, rd_of. rewrite (M1in (wz x)) by (rewrite u64_of_sum by (clear - Hx G G0; unfold PGSZ, UNIT, IB, U.Mal_fslow__G1.Mal_fslow_I.n in *; lia); exact Hx).
    unfold rd, ms_read_byte in Rb. unfold wview in W. destruct (ms_mem ms0 (wz x)) as [b0|] eqn:EM0.
    - split; [reflexivity | exists b0; reflexivity].
    - split; [| exists b; rewrite <- Rb; symmetry; apply Hrom0].
      unfold wseg_addr. change RP.segs with segs in W. destruct (find_segment segs (bv_unsigned (wz x)) 1) as [seg|]; [|exfalso; apply W; reflexivity]. destruct (seg_writable seg); [reflexivity | exfalso; apply W; reflexivity]. }
  refine (U.Mal_fslow__G3.Mal_fslow_C.L_Xnt segs C c e statics_in_image_U EP.Hrc EP.HCc EP.NLW EP.SCT EP.HTP EP.HORD wseg_in_image_U FP.HSD U.Mal_mdirect__G2.Mal_mdirect_E.errno_img FP.ERRLK
            X_nt Xc Xs Ev TN N0 N1 sA RA X_nt_shape X_nt_objs Xc_eq Xs_ok Ev_ok RA_ok call_ok TN_ok N0_eq N1_eq N0_ent N1_ent sA_regs RA_shape Ev_misc imp_res N_swf TN_stk Xc_swf X_nt_stk
            s L g am i fr Kc rhoE tr0 md m1 a k (proj1 Hslow) (proj1 (proj2 Hslow)) _ _ HMI1 Har Htp HtopX M1blk M1out M1sct XP TR okK
            (U.Mal_fslow__G2.Mal_fslow_T.QF segs E rhoE JLX) TR_pre TR_inhP TR_callP Jp JLp NT JIN JOUT _ _ rho2 Hag2).
  - cbn [rw set_rm]. symmetry. exact HP12'.
  - cbn [rw set_rm]. symmetry. exact HP13'.
  -
    intros A' rho4 RF HL0 HXP0.
    exact (U.Mal_fslow__G2.Mal_fslow_T.tail0 segs C c e E statics_in_image_U EP.HCc U.Mal_mdirect__G2.Mal_mdirect_E.errno_img errno_frame_U client_addr_not_owned_U FP.LOCKW X_ret E_mu D_after run_ret0 Xr1_ok E_mu_ok FP.Lfree_norl
             s L g am i fr Kc rhoE m1 XP XF JLX XF0 MKPOSTE TR okK TR_skip TR_run okK_of A' rho4 RF HL0 HXP0).
  -
    intros A' rho4 RF UF.
    exact (U.Mal_fslow__G2.Mal_fslow_T.tail1 segs C c e E statics_in_image_U EP.HCc U.Mal_mdirect__G2.Mal_mdirect_E.errno_img errno_frame_U client_addr_not_owned_U FP.LOCKW wseg_in_image_U E_mu D_after X_ret2 run_unmap D_after_eq run_after Xr2_ok E_mu_ok FP.Lfree_norl
             s L g am i fr Kc rhoE m1 Htp HtopX KcM XP XF JLX XF1 MKPOSTE TR okK TR_skip TR_seq TR_run okK_of TR_munmap A' rho4 RF UF).
Qed.

Lemma JIN_R : ltac2:(tb__ "0|0|
S1bS8S73A1S72S116Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;R3R2R1AbS14eVsegs;VC;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2VKc;R4R3R2A9F_;Fmdx;Ftr;FrhoX;").
Proof using .
  intros rhoX tr mdx (Hg & Hi & HM & Hu & Hring & Hd & Hr & Ht & HK & HT). unfold J_nt_preR.
  exists g, (am1 am i), (rm rhoX). split; [exact Hg|]. split; [rewrite <- Hi; exact HM|]. split; [apply magree_refl|]. split; [intros x []|].
  split; [exact Hu|]. split; [intros c0; unfold U0; clear; lia|]. split; [exact Hring|]. split; [replace (- nt_stack 3) with (-384) by reflexivity; exact Hd|]. split; [exact Hr|]. split; [exact Ht|]. split; [exact HK | exact HT].
Qed.
Lemma JIN_RG : ltac2:(tb__ "0|0|
S1bS8S73A1S72S116Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;R3R2R1AbS14fVsegs;VC;Vg;Vi;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2VKc;R4R3R2AbF_;Fmdx;Ftr;FrhoX;").
Proof using .
  intros rhoX tr mdx (Hg & Hi & HM & Hu & Hring & Hd & Hr & Ht & HK & HT). unfold J_nt_preRG.
  split; [exact Hg|]. split; [exact Hi|]. exists (am1 am i), (rm rhoX). split; [exact HM|]. split; [apply magree_refl|]. split; [intros x []|].
  split; [exact Hu|]. split; [intros c0; unfold U0; clear; lia|]. split; [exact Hring|]. split; [replace (- nt_stack 3) with (-384) by reflexivity; exact Hd|]. split; [exact Hr|]. split; [exact Ht|]. split; [exact HK | exact HT].
Qed.
End T.

Definition okKs (ok : world -> Prop) (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S0SadVsegs;Vok;VK;A3S11bVsegs;Vok;VK;A3A2").
Lemma triple_inhP : ltac2:(tb__ "0|0|
S95OF_;S94S94S95R3R1A1S3S94S94S0R1R3A1S97Vsegs;R6R1R4A4A2LP';A2F_;Fw;S97Vsegs;R4R3R2A4F_;FQ';FP;Fok;").
Proof using . intros ok P Q' H n Hg w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT n Hg w HP'). Qed.
Lemma ok_pframe_imp : ltac2:(tb__ "0|2|
S95OF_;S8S73A1M0S72OF_;F_;M1G1G0S72R3R2R1A2R5R3R2A2F_;Fmd;Ftr;S11bVsegs;R4R3A3S11bVsegs;R5R3A3F_;F_;FK';FK;Fok;").
Proof using . intros ok K K' HI HK tr ms md x8 H. apply (HK tr ms md x8). apply HI. exact H. Qed.
Lemma ok_pframe_liftK : ltac2:(tb__ "0|0|
S95OF_;S8S73A1S72OF_;F_;S11bVsegs;R2R1A3S11cVsegs;R3SaeR2A1A3F_;FK;Fok;").
Proof using . intros ok K H rho0 tr ms md x8 Hk. exact (H tr ms md x8 Hk). Qed.

Hypothesis JOUT_R : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S144Vsegs;VC;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2VKc;R4R3R2R1AaS115Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;VXP;R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").
Theorem free_contract_slow : ltac2:(tb__ "0|0|
S95OF_;SeeVsegs;R1VKc;A3S146S97Vsegs;R3Sa9Vsegs;Se6Vsegs;VC;S99Vs;VL;A2VKc;A4Se4VE;A1Vrho;A4S113A4F_;F_;Fok;").
Proof using HP12 HP13 Hslow JLX_shift JOUT_R KcM MKPOST RSV XF0 XF1.
  intros ok HS NTC. pose proof HS as (Hok & Hokp & _).
  assert (okK_of : forall K : list event -> Model -> Prop, (forall tr md, K tr md -> Kc tr md) -> okKs ok K).
  { intros K HK. split; [eapply ok_frame_imp; [exact HK | exact Hok] | eapply ok_pframe_imp; [exact HK | exact Hokp]]. }

  eapply triple_seq.
  { apply triple1_triple.
    apply (sym_run_soundJ_strict segs 2 [ff_entry (fs_ff c)] (Pre_freeI E) [mkLeaf (S1 c) RsCut] ok (J_free_preT segs C A Kc) rho eq_refl FP.run_entry).
    - intros rho0 tr ms md ms' (_ & _ & HK & _). exact (Hok tr ms md ms' HK).
    - apply U.Mal_free__G2.Mal_free_quick2.stableJ_free_pre. }
  intros n Hg [tr [ms md]] (Lf & rhoE & HinL & Hag & Hsm' & HJ'). destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'.
  refine (slow_main (triple segs ok) (okKs ok) _ _ (triple_skip segs ok) (triple_inhP ok) (@triple_seq segs ok) _ okK_of (call_soundP segs ok) _
            (J_nt_preR segs C [] U0 A1 Kc) (JL_ntR segs C [] U0 A1 Kc) _ JIN_R JOUT_R rhoE Hag n Hg (tr, mkCfg ms md) (conj Hsm' HJ')).
  - intros P P' Q' H HT. eapply triple_conseq; [exact H | intros w Hw; exact Hw | exact HT].
  - intros P Q Q' H HT. eapply triple_conseq; [intros w Hw; exact Hw | exact H | exact HT].
  - intros K S fuel leaves rhoX Q' Hrun Hlen [HokK _] Hc. exact (run_tr segs ok fuel (fs_cutsX c) S leaves K rhoX Q' Hrun Hlen HokK Hc).
  - intros K K' S rhoX Hi H17 [HK1 HK2] HJ. apply triple1_triple.
    exact (triple1_munmapJ segs ok (liftK K) (liftK K') S rhoX (ok_frame_liftK segs ok K HK1) (ok_pframe_liftK ok K HK2) Hi H17 HJ).
  - intros rho1. exact (NTC ok [] U0 A1 Kc rho1 HS).
Qed.

Lemma etriple_inhP : ltac2:(tb__ "0|0|
S94S94S95R3R1A1S3S94S94S0R1R3A1S96Vsegs;R1R4A3A2LP';A2F_;Fw;S96Vsegs;R3R2A3F_;FQ';FP;").
Proof using . intros P Q' H w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT w HP'). Qed.

Theorem free_contract_slow_ex : ltac2:(tb__ "0|0|
SebVKc;A1S14aS96Vsegs;Sa9Vsegs;Se6Vsegs;VC;S99Vs;VL;A2VKc;A4Se4VE;A1Vrho;A4S113A3F_;F_;").
Proof using HP12 HP13 Hslow JLX_shift JOUT_R KcM MKPOST RSV XF0 XF1.
  intros HVI NTC w0 Hw0.
  destruct (sym_run_completeJ segs 2 [ff_entry (fs_ff c)] (Pre_freeI E) [mkLeaf (S1 c) RsCut] (J_free_preT segs C A Kc) rho w0 eq_refl (U.Mal_free__G2.Mal_free_quick2.stableJ_free_pre A Kc) FP.run_entry Hw0)
    as (Lf & rhoE & w1 & HinL & Hst & Hag & HSP). destruct HinL as [<-|[]]. cbn [lf_state] in HSP.
  assert (ET : etriple segs (SPJ segs (J_free_preT segs C A Kc) (S1 c) rhoE) QF).
  { refine (slow_main (etriple segs) (fun _ => True) (etriple_pre segs) _ (etriple_skip segs) etriple_inhP (@etriple_seq segs) _ (fun _ _ => I) (call_completeP segs) _
              (J_nt_preR segs C [] U0 A1 Kc) (JL_ntR segs C [] U0 A1 Kc) _ JIN_R JOUT_R rhoE Hag).
    - intros P Q Q' H HT. eapply etriple_conseq; [intros w Hw; exact Hw | exact H | exact HT].
    - intros K S fuel leaves rhoX Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (fs_cutsX c) S leaves K rhoX Q' Hrun Hlen Hc).
    - intros K K' S rhoX Hi H17 _ HJ. exact (etriple_munmapJ segs (liftK K) (liftK K') S rhoX Hi H17 HJ).
    - intros rho1. exact (NTC [] U0 A1 Kc rho1 HVI). }
  destruct (ET w1 HSP) as (w2 & Hst2 & HQ). exists w2. split; [eapply wsteps_trans; [exact Hst | exact Hst2] | exact HQ].
Qed.

Hypothesis JOUT_RY : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S143Vsegs;VC;Vg;Vi;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2VKc;R4R3R2R1AcS115Vsegs;VC;Vs;VL;Vg;Vam;Vi;VKc;VXP;R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").
Theorem free_drv_slow_ex : ltac2:(tb__ "0|0|
SabS1bS8S73A1S72R4R3R2R1A3Se6Vsegs;VC;S99Vs;VL;A2VKc;R4R3R2A7F_;Fmd;Ftr;FrhoX;SacS7eR2A2S14cS96Vsegs;Sa9Vsegs;R4Se4VE;A1Vrho;A4S113A3F_;F_;F_;FJ;").
Proof using HP12 HP13 Hslow JLX_shift JOUT_RY KcM MKPOST RSV XF0 XF1.
  intros J HJimp HstJ NTC w0 Hw0.
  destruct (sym_run_completeJ segs 2 [ff_entry (fs_ff c)] (Pre_freeI E) [mkLeaf (S1 c) RsCut] J rho w0 eq_refl HstJ FP.run_entry Hw0)
    as (Lf & rhoE & w1 & HinL & Hst & Hag & HSP). destruct HinL as [<-|[]]. cbn [lf_state] in HSP.
  assert (ET : etriple segs (SPJ segs (J_free_preT segs C A Kc) (S1 c) rhoE) QF).
  { refine (slow_main (etriple segs) (fun _ => True) (etriple_pre segs) _ (etriple_skip segs) etriple_inhP (@etriple_seq segs) _ (fun _ _ => I) (call_completeP segs) _
              (J_nt_preRG segs C g i [] U0 A1 Kc) (JL_ntRY segs C g i [] U0 A1 Kc) _ JIN_RG JOUT_RY rhoE Hag).
    - intros P Q Q' H HT. eapply etriple_conseq; [intros w Hw; exact Hw | exact H | exact HT].
    - intros K S fuel leaves rhoX Q' Hrun Hlen _ Hc. exact (erun_tr segs fuel (fs_cutsX c) S leaves K rhoX Q' Hrun Hlen Hc).
    - intros K K' S rhoX Hi H17 _ HJ. exact (etriple_munmapJ segs (liftK K) (liftK K') S rhoX Hi H17 HJ).
    - intros rho1. exact (NTC g i [] U0 A1 Kc rho1). }
  destruct w1 as [tr1 [ms1 md1]]. destruct HSP as [Hsm1 HJ1].
  destruct (ET (tr1, mkCfg ms1 md1) (conj Hsm1 (HJimp _ _ _ HJ1))) as (w2 & Hst2 & HQ). exists w2. split; [eapply wsteps_trans; [exact Hst | exact Hst2] | exact HQ].
Qed.

Theorem free_drv_slow_d : ltac2:(tb__ "0|1|
S95OF_;SabS8S73A1M0S72OF_;F_;G0S72R3R2R1A2VKc;R3R2A2F_;Fmd;Ftr;S114R4R2A2F_;FK;S1bG0S72R5R3R2R1A3Se6Vsegs;VC;S99Vs;VL;A2VKc;R4R3R2A7F_;Fmd;Ftr;FrhoX;SacS7eR3A2S148S97Vsegs;R6Sa9Vsegs;R5Se4VE;A1Vrho;A4S113A4F_;F_;F_;F_;FJ;Fok;").
Proof using HP12 HP13 Hslow JLX_shift JOUT_RY KcM MKPOST RSV XF0 XF1.
  intros ok J okK_of HJimp HstJ NTC. pose proof (okK_of Kc (fun _ _ H => H)) as [Hok Hokp].

  eapply triple_seq.
  { apply triple1_triple.
    apply (sym_run_soundJ_strict segs 2 [ff_entry (fs_ff c)] (Pre_freeI E) [mkLeaf (S1 c) RsCut] ok J rho eq_refl FP.run_entry).
    - intros rho0 tr ms md ms' HJ0. pose proof (HJimp _ _ _ HJ0) as (_ & _ & HK & _). exact (Hok tr ms md ms' HK).
    - exact HstJ. }
  intros n Hg [tr [ms md]] (Lf & rhoE & HinL & Hag & Hsm' & HJ'). destruct HinL as [<-|[]]. cbn [lf_state] in Hsm'.
  refine (slow_main (triple segs ok) (okKs ok) _ _ (triple_skip segs ok) (triple_inhP ok) (@triple_seq segs ok) _ okK_of (call_soundP segs ok) _
            (J_nt_preRG segs C g i [] U0 A1 Kc) (JL_ntRY segs C g i [] U0 A1 Kc) _ JIN_RG JOUT_RY rhoE Hag n Hg (tr, mkCfg ms md) (conj Hsm' (HJimp _ _ _ HJ'))).
  - intros P P' Q' H HT. eapply triple_conseq; [exact H | intros w Hw; exact Hw | exact HT].
  - intros P Q Q' H HT. eapply triple_conseq; [intros w Hw; exact Hw | exact H | exact HT].
  - intros K S fuel leaves rhoX Q' Hrun Hlen [HokK _] Hc. exact (run_tr segs ok fuel (fs_cutsX c) S leaves K rhoX Q' Hrun Hlen HokK Hc).
  - intros K K' S rhoX Hi H17 [HK1 HK2] HJ. apply triple1_triple.
    exact (triple1_munmapJ segs ok (liftK K) (liftK K') S rhoX (ok_frame_liftK segs ok K HK1) (ok_pframe_liftK ok K HK2) Hi H17 HJ).
  - intros rho1. apply (NTC ok g i [] U0 A1 Kc rho1 Hok).
Qed.
End Main.

Section ContractInst.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame) (Kc : list event -> Model -> Prop) (rho : valuation).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S1S6S81VL;Sc9Vam;Vi;Vfr;A3A2S7aQ40S1eVrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S1S6S54Vfr;A1S7aQ40S1eVrho;PdA2A2A3").
Let XPt : MA -> option (nat * region) -> Prop := fun _ _ => True.
Let XFt : MA -> Prop := fun _ => True.
Lemma XF0t : ltac2:(tb__ "0|0|
S9aVXPt;R1S13SaSeS4fA2A1A2VXFt;R2A1F_;FA';"). Proof using . intros; exact I. Qed.
Lemma XF1t : ltac2:(tb__ "0|0|
S51SeS4fVXPt;S99R3VL;A2S11SaSeS4fA2S9SeS4fR2R1A4A2A2S1SdS4fA1ScaR4R3A2S11S4fR2A2A3S1S58S56R3A1S55A3S1SbS57R4A1ScA3VXFt;S99S154R7R6R5A3VL;A2A1F_;F_;F_;F_;Frg;Fkr;Fs';").
Proof using . intros; exact I. Qed.
Lemma MKPOSTt : ltac2:(tb__ "0|3|
S1bS24S7eVrho;R1A3S9aS1bS8S73A1S72S8SaS6S6A2M0A1M1G1SecS7dS80R6R5R3A5S1SbS53S98R7A1A1ScA3S1Sc8S9bR8A1VL;A3S1G1S9cS99Vs;VL;A2M2A1S12G0R5SfG0S9S6S6Sd9VL;Vam;Vi;Vfr;A4Sf4Vfr;A1A4R4A3A3A3S1G1S9cRaA1S12G0R6R5A3A3SeaS7dS80G2RbS21RdA1S21RaA1A6VKc;RaR9A2VXFt;RdA1Se8S7dS80G2VKc;R10RdRcRbA8F_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmdx;Ftr;Frho';FA';F_;FrhoE;").
Proof using HP12 HP13.
  intros rhoE (EW & EL & EM) A' rho' tr mdx l1 l2 HM Hini HL EB EB' HK HKc _. exists A', l1, l2.
  split; [exact HM|]. split; [rewrite <- (EW 12%positive), <- (EW 13%positive), <- HP12, <- HP13 by (cbv; reflexivity); exact EB|]. split; [exact EB'|].
  split; [exact HK|]. split; [split; [intros _; exact Hini | unfold top_kept; rewrite HL; reflexivity] | exact HKc].
Qed.
Lemma JLshift_t : ltac2:(tb__ "0|1|
S1bS1bS8S73A1S72S24S7eVrho;R4A3Se8S7dS80S99Vs;VL;A2M0VKc;R5R4R3R2A8Se8S7dS80G0VKc;Vrho;R5R4R3A8F_;F_;Fmdx;Ftr;Frho';FrhoE;").
Proof using .
  intros rhoE rho' tr mdx (EW & EL & EM) (A' & l1 & l2 & HM & HB & HB' & HK & HI & HKc). exists A', l1, l2.
  rewrite (EW 12%positive), (EW 13%positive) by (cbv; reflexivity).
  assert (Erm : rm rho = rm rhoE) by (apply functional_extensionality; exact EM). rewrite Erm. repeat (split; [assumption|]). exact HKc.
Qed.
Lemma JOUT_Rt : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S144S7dS80S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2VKc;R4R3R2R1AaS115S7dS80Vs;VL;Vg;Vam;Vi;VKc;VXPt;R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").
Proof using .
  intros rho0 rho' tr mdx (A' & mv' & HM & Hmg & _ & HL' & Hini & Hcorr & Hub & Hreach & Hres & Hkept & HK). unfold U.Mal_fslow__G3.Mal_fslow_C.nt_out_facts.
  assert (Emv : mv' = rm rho') by (apply functional_extensionality; intros a0; exact (magree_nil _ _ _ Hmg a0)).
  exists A'. subst mv'. cbn [ma_s ma_L] in *. split; [exact HM|]. split; [exact HL'|]. split; [exact Hcorr|]. split; [exact Hub|]. split; [exact Hreach|]. split; [exact Hini|].
  split; [| split; [exact Hkept | exact HK]].
  destruct Hres as [[H1 H2] | (H0 & kr & rg & H1 & H2 & H3 & H4 & H5 & H6)]; [left; split; [exact H1 | split; [exact H2 | exact I]] | right].
  split; [exact H0|]. exists kr, rg. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6 | exact I].
Qed.
End ContractInst.

Theorem free_contract_slow_P : ltac2:(tb__ "0|2|
S95OF_;S9aS8S73A1S72OF_;F_;S1bS4eS50S6S52S146S142S80A1SeeS7dRaR8A3Sf6S98RaA1R7R6R5R4A5S1S6S81S9bRbA1Sc9R7R6R5A3A2S7aQ40M0S1eR9PcA2A2A3S1S6S54R6A1S7aG0S1eRaPdA2A2A3S97S7dReSa9S7dSe6S7dS80RdRcA4Se4Se5A1RbA4Sa0S7dS7eRbSfSaS1dS9fA2M1S9S1dS9fSe7Se5A1Se8S7dS80RdRcA4A4S10G1A1A3A4A4F_;F_;F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;Fok;").
Proof.
  intros ok [s L] Kc rho g am i fr NTC RSV HS Hslow HP12 HP13.
  exact (free_contract_slow s L g am i fr Kc rho (vm_insensitive_munmap Kc (proj2 (proj2 HS))) Hslow HP12 HP13 RSV
           (fun _ _ => True) (fun _ => True) (JL_free segsU C_U (mkMA s L) Kc) XF0t (XF1t L) (MKPOSTt s L am i fr Kc rho HP12 HP13) (JLshift_t s L Kc rho)
           (JOUT_Rt s L g am i Kc) ok HS NTC).
Qed.
Theorem free_contract_slow_ex_P : ltac2:(tb__ "0|2|
S9aS8S73A1S72OF_;F_;S1bS4eS50S6S52S14aS142S80A1SebR8A1Sf6S98RaA1R7R6R5R4A5S1S6S81S9bRbA1Sc9R7R6R5A3A2S7aQ40M0S1eR9PcA2A2A3S1S6S54R6A1S7aG0S1eRaPdA2A2A3S96S7dSa9S7dSe6S7dS80RdRcA4Se4Se5A1RbA4Sa0S7dS7eRbSfSaS1dS9fA2M1S9S1dS9fSe7Se5A1Se8S7dS80RdRcA4A4S10G1A1A3A4A3F_;F_;F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FA;").
Proof.
  intros [s L] Kc rho g am i fr NTC RSV HVI Hslow HP12 HP13.
  exact (free_contract_slow_ex s L g am i fr Kc rho (vm_insensitive_munmap Kc HVI) Hslow HP12 HP13 RSV
           (fun _ _ => True) (fun _ => True) (JL_free segsU C_U (mkMA s L) Kc) XF0t (XF1t L) (MKPOSTt s L am i fr Kc rho HP12 HP13) (JLshift_t s L Kc rho)
           (JOUT_Rt s L g am i Kc) HVI NTC).
Qed.

Section DrvInst.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame) (Kc : list event -> Model -> Prop) (rho : valuation) (k X : Z).
Hypothesis HVI : vm_insensitive Kc.
Hypothesis Hslow : ltac2:(tb__ "0|0|
Sf6Vs;Vg;Vam;Vi;Vfr;A5").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S1S6S81VL;Sc9Vam;Vi;Vfr;A3A2S7aQ40S1eVrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S1S6S54Vfr;A1S7aQ40S1eVrho;PdA2A2A3").
Hypothesis HW : WF s.
Hypothesis HdrvN : ltac2:(tb__ "0|0|
S135S80Vk;S99Vs;VL;A2A3").
Hypothesis Hk : 0 < k.
Definition KcD : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S8S73A1S72S0VKc;R2R1A2S136R1VX;A2A2Lmd;Ltr;").
Definition XPd : MA -> option (nat * region) -> Prop := ltac2:(tb__ "0|4|
S9aSdSaSeS4fA2M0A1S0S1Sc8S9bR2A1VL;A3S3S8SaS62S6A2A1M1G1ScfSaSdSaSeS6A2M2A1M3S51A2S64S63Vg;Vi;Sf2Vs;Vg;Vam;Vi;A4A4R1S9G3S51S19G0G2G0S9SeS6S15SeS4fR1A3S5aS16SeS4fR1A3A1A4Lkr_rg;R2A4S98R3A1A4A4Lktr;A2A2Lr;LA';").
Definition XFd : MA -> Prop := ltac2:(tb__ "0|1|
S9aS0S1Sc8S9bR1A1VL;A3S3S8SaS62S6A2A1M0G0ScfSaS17S51A2S6eS11S4eSc9Vam;Vi;Vfr;A3A2Vs;A2R1S9S17S51S1aS98R2A1A4A4Ltrm;A2A2LA';").
Lemma KcD_M : ltac2:(tb__ "0|1|
S8S73A1S72S7bQ40A1M0G0S130R4R3A2S130R5S117R4R3R2A3A2F_;Fkk;Fa;Fmd;Ftr;").
Proof using HVI. intros tr md a kk [HK HR]. split; [exact (vm_insensitive_munmap Kc HVI tr md a kk HK) | exact (vm_room_munmap md X a kk HR)]. Qed.
Lemma XF0d : ltac2:(tb__ "0|0|
S9aS132R1S13SaSeS4fA2A1A2S131R2A1F_;FA';").
Proof using HW Hslow.
  intros A' [HL (ktr & HY)]. split; [exact HL|]. exists ktr. cbn [option_map] in HY.
  exact (free_slow_yields_none s g am i fr HW (proj1 Hslow) (proj2 (proj2 Hslow)) ktr (ma_s A') HY).
Qed.
Lemma XF1d : ltac2:(tb__ "0|0|
S51SeS4fS132S99R3VL;A2S11SaSeS4fA2S9SeS4fR2R1A4A2A2S1SdS4fA1ScaR4R3A2S11S4fR2A2A3S1S58S56R3A1S55A3S1SbS57R4A1ScA3S131S99S154R7R6R5A3VL;A2A1F_;F_;F_;F_;Frg;Fkr;Fs';").
Proof using HW Hslow.
  intros s' kr rg [_ (ktr & HY)] Hrg _ _. split; [reflexivity|]. exists (ktr ++ [(KMunmap kr (rg_len rg), 1)]). cbn [option_map fst snd ma_s] in HY |- *.
  pose proof (free_slow_yields_some s g am i fr HW (proj1 Hslow) (proj2 (proj2 Hslow)) ktr kr (rg_len rg) s' 1 HY) as Y.
  rewrite (region_of_nth s' kr rg Hrg) in Y. unfold km_s', km_n. exact Y.
Qed.
Lemma MKPOSTd : ltac2:(tb__ "0|3|
S1bS24S7eVrho;R1A3S9aS1bS8S73A1S72S8SaS6S6A2M0A1M1G1SecS7dS80R6R5R3A5S1SbS53S98R7A1A1ScA3S1Sc8S9bR8A1VL;A3S1G1S9cS99Vs;VL;A2M2A1S12G0R5SfG0S9S6S6Sd9VL;Vam;Vi;Vfr;A4Sf4Vfr;A1A4R4A3A3A3S1G1S9cRaA1S12G0R6R5A3A3SeaS7dS80G2RbS21RdA1S21RaA1A6S130RaR9A2S131RdA1S134S7dS80G2S46Vk;Z1A2VX;VKc;R10RdRcRbAaF_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmdx;Ftr;Frho';FA';F_;FrhoE;").
Proof using HP12 HP13 HdrvN Hk Hslow.
  intros rhoE (EW & EL & EM) A' rho' tr mdx l1 l2 HM Hini HL EB EB' HK [HKc HR] [_ (trm & HY)]. exists A', l1, l2.
  split; [exact HM|]. split; [split; [exact Hini | unfold top_kept; rewrite HL; reflexivity]|]. split.
  { destruct HdrvN as (j & Hr & H0 & Hj). exists (Datatypes.S j). split; [| split; [lia | rewrite Nat2Z.inj_succ; lia]].
    apply (DR_free C_U j (mkMA s L) (BlockView.zP L am i fr) trm A' Hr). right. exists (frame_ptr am i fr), (fr_n fr). cbn [ma_s ma_L].
    split; [exact (user_block_of_frame s g am i fr (proj1 Hslow) (proj1 (proj2 Hslow)))|]. split; [reflexivity|]. split; [exact HY|].
    destruct A' as [s'' L'']. cbn [ma_s ma_L] in HL |- *. subst L''. apply layout_extends_refl. }
  split; [exact HR|]. split; [rewrite <- (EW 12%positive), <- (EW 13%positive), <- HP12, <- HP13 by (cbv; reflexivity); exact EB|]. split; [exact EB'|].
  split; [exact HK | exact HKc].
Qed.
Lemma JLshift_d : ltac2:(tb__ "0|2|
S1bS1bS8S73A1S72S24S7eVrho;R4A3S134S7dS80S99Vs;VL;A2M0S46Vk;Z1A2M1VX;VKc;R5R4R3R2AaS134S7dS80G0G1VX;VKc;Vrho;R5R4R3AaF_;F_;Fmdx;Ftr;Frho';FrhoE;").
Proof using .
  intros rhoE rho' tr mdx (EW & EL & EM) (A' & l1 & l2 & HM & HI & HD & HR & HB & HB' & HK & HKc). exists A', l1, l2.
  rewrite (EW 12%positive), (EW 13%positive) by (cbv; reflexivity).
  assert (Erm : rm rho = rm rhoE) by (apply functional_extensionality; exact EM). rewrite Erm. repeat (split; [assumption|]). exact HKc.
Qed.
Lemma JOUT_RYd : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S143S7dS80Vg;Vi;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2S130R4R3R2R1AcS115S7dS80Vs;VL;Vg;Vam;Vi;S130S132R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").
Proof using .
  intros rho0 rho' tr mdx (A' & mv' & HM & Hmg & _ & HL' & Hini & Hcorr & Hub & Hreach & (ktr & mres & HY & Hres) & Hkept & HK). unfold U.Mal_fslow__G3.Mal_fslow_C.nt_out_facts.
  assert (Emv : mv' = rm rho') by (apply functional_extensionality; intros a0; exact (magree_nil _ _ _ Hmg a0)).
  exists A'. subst mv'. cbn [ma_s ma_L] in *. split; [exact HM|]. split; [exact HL'|]. split; [exact Hcorr|]. split; [exact Hub|]. split; [exact Hreach|]. split; [exact Hini|].
  split; [| split; [exact Hkept | exact HK]].
  destruct Hres as [(H1 & H2 & H3) | (kr & rg & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left | right].
  - split; [exact H2|]. split; [exact H3|]. split; [exact HL'|]. exists ktr. subst mres. exact HY.
  - split; [exact H1|]. exists kr, rg. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
    split; [exact HL'|]. exists ktr. subst mres. exact HY.
Qed.
Lemma stableJ_free_drv : ltac2:(tb__ "0|0|
SacS7eS163S99Vs;VL;A2Vk;VX;VKc;A4A2").
Proof using .
  intros rho1 rho2 tr md Hag [HJ HD]. split; [exact (U.Mal_free__G2.Mal_free_quick2.stableJ_free_pre (mkMA s L) Kc rho1 rho2 tr md Hag HJ) | exact HD].
Qed.
End DrvInst.

Section DrvInstS.
Variables (s : astate) (L : layout) (g : sptr) (am : ameta) (i : Z) (fr : frame) (Kc : list event -> Model -> Prop) (rho : valuation) (k X : Z).
Hypothesis HVI : vm_insensitive Kc.
Hypothesis Hslow : ltac2:(tb__ "0|0|
Sf6Vs;Vg;Vam;Vi;Vfr;A5").
Hypothesis HP12 : ltac2:(tb__ "0|0|
S1S6S81VL;Sc9Vam;Vi;Vfr;A3A2S7aQ40S1eVrho;PcA2A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S1S6S54Vfr;A1S7aQ40S1eVrho;PdA2A2A3").
Hypothesis HW : WF s.
Hypothesis HdrvN : ltac2:(tb__ "0|0|
S135S80Vk;S99Vs;VL;A2A3").
Hypothesis Hk : 0 < k.
Definition KcS : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S8S73A1S72S0VKc;R2R1A2S162R1VX;A2A2Lmd;Ltr;").
Lemma KcS_M : ltac2:(tb__ "0|1|
S8S73A1S72S7bQ40A1M0G0S133R4R3A2S133R5S117R4R3R2A3A2F_;Fkk;Fa;Fmd;Ftr;").
Proof using HVI. intros tr md a kk [HK HR]. split; [exact (vm_insensitive_munmap Kc HVI tr md a kk HK) | exact (vm_roomS_munmap md X a kk HR)]. Qed.
Lemma MKPOSTdS : ltac2:(tb__ "0|3|
S1bS24S7eVrho;R1A3S9aS1bS8S73A1S72S8SaS6S6A2M0A1M1G1SecS7dS80R6R5R3A5S1SbS53S98R7A1A1ScA3S1Sc8S9bR8A1VL;A3S1G1S9cS99Vs;VL;A2M2A1S12G0R5SfG0S9S6S6Sd9VL;Vam;Vi;Vfr;A4Sf4Vfr;A1A4R4A3A3A3S1G1S9cRaA1S12G0R6R5A3A3SeaS7dS80G2RbS21RdA1S21RaA1A6S133RaR9A2S150Vs;VL;Vam;Vi;Vfr;RdA6S141S7dS80G2S46Vk;Z1A2VX;VKc;R10RdRcRbAaF_;F_;F_;F_;F_;F_;F_;F_;Fl2;Fl1;Fmdx;Ftr;Frho';FA';F_;FrhoE;").
Proof using HP12 HP13 HdrvN Hk Hslow.
  intros rhoE (EW & EL & EM) A' rho' tr mdx l1 l2 HM Hini HL EB EB' HK [HKc HR] [_ (trm & HY)]. exists A', l1, l2.
  split; [exact HM|]. split; [split; [exact Hini | unfold top_kept; rewrite HL; reflexivity]|]. split.
  { destruct HdrvN as (j & Hr & H0 & Hj). exists (Datatypes.S j). split; [| split; [lia | rewrite Nat2Z.inj_succ; lia]].
    apply (DR_free C_U j (mkMA s L) (BlockView.zP L am i fr) trm A' Hr). right. exists (frame_ptr am i fr), (fr_n fr). cbn [ma_s ma_L].
    split; [exact (user_block_of_frame s g am i fr (proj1 Hslow) (proj1 (proj2 Hslow)))|]. split; [reflexivity|]. split; [exact HY|].
    destruct A' as [s'' L'']. cbn [ma_s ma_L] in HL |- *. subst L''. apply layout_extends_refl. }
  split; [exact HR|]. split; [rewrite <- (EW 12%positive), <- (EW 13%positive), <- HP12, <- HP13 by (cbv; reflexivity); exact EB|]. split; [exact EB'|].
  split; [exact HK | exact HKc].
Qed.
Lemma JLshift_dS : ltac2:(tb__ "0|2|
S1bS1bS8S73A1S72S24S7eVrho;R4A3S141S7dS80S99Vs;VL;A2M0S46Vk;Z1A2M1VX;VKc;R5R4R3R2AaS141S7dS80G0G1VX;VKc;Vrho;R5R4R3AaF_;F_;Fmdx;Ftr;Frho';FrhoE;").
Proof using .
  intros rhoE rho' tr mdx (EW & EL & EM) (A' & l1 & l2 & HM & HI & HD & HR & HB & HB' & HK & HKc). exists A', l1, l2.
  rewrite (EW 12%positive), (EW 13%positive) by (cbv; reflexivity).
  assert (Erm : rm rho = rm rhoE) by (apply functional_extensionality; exact EM). rewrite Erm. repeat (split; [assumption|]). exact HKc.
Qed.
Lemma JOUT_RYdS : ltac2:(tb__ "0|0|
S1bS1bS8S73A1S72S143S7dS80Vg;Vi;S10S4eA1Sc7S99Sf2Vs;Vg;Vam;Vi;A4VL;A2S133R4R3R2R1AcS115S7dS80Vs;VL;Vg;Vam;Vi;S133S151Vs;VL;Vg;Vam;Vi;A5R5R4R3R2AdF_;Fmdx;Ftr;Frho';Frho0;").
Proof using .
  intros rho0 rho' tr mdx (A' & mv' & HM & Hmg & _ & HL' & Hini & Hcorr & Hub & Hreach & (ktr & mres & HY & Hres) & Hkept & HK). unfold U.Mal_fslow__G3.Mal_fslow_C.nt_out_facts.
  assert (Emv : mv' = rm rho') by (apply functional_extensionality; intros a0; exact (magree_nil _ _ _ Hmg a0)).
  exists A'. subst mv'. cbn [ma_s ma_L] in *. split; [exact HM|]. split; [exact HL'|]. split; [exact Hcorr|]. split; [exact Hub|]. split; [exact Hreach|]. split; [exact Hini|].
  split; [| split; [exact Hkept | exact HK]].
  destruct Hres as [(H1 & H2 & H3) | (kr & rg & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left | right].
  - split; [exact H2|]. split; [exact H3|]. split; [exact HL'|]. exists ktr. subst mres. exact HY.
  - split; [exact H1|]. exists kr, rg. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
    split; [exact HL'|]. exists ktr. subst mres. exact HY.
Qed.

Definition J_free_drvST : jpred := ltac2:(tb__ "0|1|
S1bS8S73A1S72S0Se6S7dS80S99Vs;VL;A2M0VKc;R3R2R1A7S0S135S80Vk;G0A3S0S45Z0Vk;A2S162R1VX;A2A2A2A2Lmd;Ltr;LrhoX;").
Lemma stableJ_free_drvS : stableJ NF J_free_drvST.
Proof using .
  intros rho1 rho2 tr md Hag [HJ HD]. split; [exact (U.Mal_free__G2.Mal_free_quick2.stableJ_free_pre (mkMA s L) Kc rho1 rho2 tr md Hag HJ) | exact HD].
Qed.
End DrvInstS.

Theorem free_drv_slow_ex_P : ltac2:(tb__ "0|2|
S9aS6S6S8S73A1S72OF_;F_;S1bS4eS50S6S52S14cS142S80A1SebR8A1Sf6S98RcA1R7R6R5R4A5S1S6S81S9bRdA1Sc9R7R6R5A3A2S7aQ40M0S1eR9PcA2A2A3S1S6S54R6A1S7aG0S1eRaPdA2A2A3S96S7dSa9S7dS163RfReRdRcA4Se4Se5A1RbA4Sa0S7dS7eRbSfSaS1dS9fA2M1S9S1dS9fSe7Se5A1S134S7dS80RfS46ReZ1A2RdRcA6A4S10G1A1A3A4A3F_;F_;F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FX;Fk;FA;").
Proof.
  intros [s L] Kc0 X Kc rho g am i fr NTC RSV HVI Hslow HP12 HP13 w0 Hw0. rename Kc0 into k.
  pose proof Hw0 as [_ ((HMI & _) & HdrvN & Hk & _)]. pose proof (proj1 HMI) as HW. cbn [ma_s] in HW, Hslow.
  refine (free_drv_slow_ex s L g am i fr (KcD Kc X) rho (KcD_M Kc X HVI) Hslow HP12 HP13 RSV
            (XPd s L g am i) (XFd s L am i fr) (JLd_free segsU C_U (mkMA s L) (k - 1) X Kc)
            (XF0d s L g am i fr Hslow HW) (XF1d s L g am i fr Hslow HW) (MKPOSTd s L g am i fr Kc rho k X Hslow HP12 HP13 HdrvN Hk) (JLshift_d s L Kc rho k X)
            (JOUT_RYd s L g am i Kc X) (U.Mal_free__G2.Mal_free_quickE.J_free_drvT (mkMA s L) k X Kc) _ (stableJ_free_drv s L Kc k X) NTC w0 Hw0).
  intros rhoX tr md ((HM & HB & HKc & Htp & Hini & HT) & _ & _ & HR). split; [exact HM|]. split; [exact HB|]. split; [split; [exact HKc | exact HR]|]. split; [exact Htp|]. split; [exact Hini | exact HT].
Qed.

Theorem free_drv_slow_S_P : ltac2:(tb__ "0|2|
S95OF_;S9aS6S6S8S73A1S72OF_;F_;S1bS4eS50S6S52S148S142S80A1SeeS7dRcR8A3Sf6S98RcA1R7R6R5R4A5S1S6S81S9bRdA1Sc9R7R6R5A3A2S7aQ40M0S1eR9PcA2A2A3S1S6S54R6A1S7aG0S1eRaPdA2A2A3S97S7dR10Sa9S7dS14dS98RfA1S9bRfA1RcReRdA5Se4Se5A1RbA4Sa0S7dS7eRbSfSaS1dS9fA2M1S9S1dS9fSe7Se5A1S141S7dS80RfS46ReZ1A2RdRcA6A4S10G1A1A3A4A4F_;F_;F_;F_;F_;F_;Ffr;Fi;Fam;Fg;Frho;FKc;FX;Fk;FA;Fok;").
Proof.
  intros ok [s L] Kc0 X Kc rho g am i fr NTC RSV HS Hslow HP12 HP13. rename Kc0 into k. cbn [ma_s ma_L].
  pose proof HS as (Hok & Hokp & HVI).
  apply triple_inh. intros w0 Hw0.
  pose proof Hw0 as [_ ((HMI & _) & HdrvN & Hk & _)]. pose proof (proj1 HMI) as HW. cbn [ma_s] in HW, Hslow.
  refine (free_drv_slow_d s L g am i fr (KcS Kc X) rho (KcS_M Kc X HVI) Hslow HP12 HP13 RSV
            (XPd s L g am i) (XFd s L am i fr) (JLdS_free segsU C_U (mkMA s L) (k - 1) X Kc)
            (XF0d s L g am i fr Hslow HW) (XF1d s L g am i fr Hslow HW) (MKPOSTdS s L g am i fr Kc rho k X Hslow HP12 HP13 HdrvN Hk) (JLshift_dS s L Kc rho k X)
            (JOUT_RYdS s L g am i Kc X) ok (J_free_drvST s L Kc k X) _ _ (stableJ_free_drvS s L Kc k X) NTC).
  - intros K HK. split; [eapply ok_frame_imp; [| exact Hok] | eapply ok_pframe_imp; [| exact Hokp]]; intros tr md H; exact (proj1 (HK tr md H)).
  - intros rhoX tr md ((HM & HB & HKc & Htp & Hini & HT) & _ & _ & HR). split; [exact HM|]. split; [exact HB|]. split; [split; [exact HKc | exact HR]|]. split; [exact Htp|]. split; [exact Hini | exact HT].
Qed.
End Mal_fslow.
