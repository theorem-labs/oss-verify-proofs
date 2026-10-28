(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "option"; "list"; "bool"; "prod"; "true"; "nil"; "app"; "Some"; "fst"; "None"; "nat"; "snd"; "false"; "andb"; "length"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "pre_fregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "reg_sv"; "SLit"; "cell"; "SVar"; "rm"; "mkCell"; "obj_range"; "sprop"; "ss_objs"; "smatch"; "ss_next"; "rw"; "ss_pc"; "obj_holds"; "eval"; "sstate"; "valuation"; "agree_below"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "mkSS"; "ss_lenient"; "ss_regs"; "SPUle"; "holds"; "rl"; "ranges_disjoint"; "sv_below"; "SAlu"; "odefault"; "swf"; "soff"; "DUnknown"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "c_width"; "mkObj"; "mkVal"; "ob_dflt"; "obj_wf"; "outside_all"; "ro_addr"; "tfact"; "c_off"; "c_val"; "enc_bytes"; "fcsr_match"; "freg_sv"; "fregs_match"; "ob_base"; "ob_cells"; "regs_match"; "resv_match"; "sfcsr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "leb"; "modulo"; "to_nat"; "sub"; "of_N"; "opp"; "eqb"; "ltb"; "mul"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "st_avail_meta_area_count"; "st_free_meta_head"; "st_area_tail"; "st_init_done"; "astate"; "st_areas"; "st_avail_meta_count"; "brkst"; "st_brk"; "alloc_meta"; "padd"; "st_active"; "st_bounces"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_regions"; "st_seq"; "st_unmap_seq"; "st_usage"; "BrkDead"; "PGSZ"; "RkMap"; "kreq"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_area_head"; "BrkCur"; "METAS_PER_AREA"; "META_SIZE"; "mslot"; "prid"; "st_avail_meta"; "st_avail_meta_areas"; "st_metas"; "KMprotect"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "topL"; "mc_chk_guard"; "blocks"; "holds"; "mc_auxv"; "mc_errno"; "mc_tp"; "mc_chk_guard_got"; "range_in_maps"; "addr_of"; "mc_img_hi"; "mc_img_lo"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "AM_P"; "v"; "Pre_am"; "AM_NEXT"; "O_stk"; "O_tail"; "Posts_am_P"; "add_facts"; "A78_res"; "A78_area_ok"; "O_auxvp"; "O_brk"; "O_ctxB"; "O_errno"; "O_got"; "O_guard"; "O_pgsz"; "O_sec"; "A2e4_first"; "A2e4_next"; "A78_area"; "AC_brk_ok"; "M64"; "A78_area_fail"; "AC_brk_fail"; "AE_area"; "AE_brk"; "AE_nobrk"; "AM_D"; "nz_fact"; "ptr_facts"; "res_facts"; "ctx_facts"; "ne_req"; "am_ctx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK.InstX.BK.Granted"; "LC"; "GRb"; "pageK"; "md2"; "subC"; "O_brkC"; "O_ctxC"; "srcF"; "srcN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR.InstX.Cut78a"; "LC"; "UNCH_R"; "L78"; "LRF"; "CHG_R"; "valC"; "GRa"; "md2"; "pageK"; "subC"; "OBJ_R"; "memC"; "stkR_cells"; "zeroC"; "O_brkA"; "O_ctxA"; "srcF"; "srcN"; "stk78_cells"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "map_contains"; "vm_maps"; "page_round_up_Z"; "vm_noaccess"; "vm_brk"; "vm_reserved"; "vm_start_brk"; "with_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_s"; "MA"; "layout_extends"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "rho1"; "D0"; "sp0"; "Kexact"; "zA"; "brkZ"; "rw1v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk"; "pz"; "sd"; "tB"; "bm"; "bp"; "vmB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "guards"; "safe"; "triple"; "w_cfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK.InstX.BK"; "LBF"; "UNCH_F"; "valC"; "CHG_F"; "LBE"; "stkE_cells"; "N_BK"; "subBF"; "FAILC"; "O_ctxD"; "R_BK"; "memC"; "zeroC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR.InstX"; "LAR"; "subAR"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB.InstX"; "LNB"; "subNB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea"; "pz"; "tA"; "am"; "ap"; "vmA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK.InstX.BK.FailCut"; "mC"; "rhoX"; "touched"; "rhoEF"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "firstn"; "skipn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "Posts_am"; "Pre_am"; "J_am_pre"; "L_am_null"; "JL_am_ok"; "JL_am_null"; "L_am_ok"; "am_post_common"; "AM_D"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "mcell"; "loc_addr"; "footprint"; "image"; "region_of"; "yields"; "keys"; "ly_reg"; "Inv"; "ly_ctx"; "LMem"; "MT"; "alloc_owned"; "cell_holds"; "ly_sec"; "mc_loc"; "mc_w"; "memb"; "sval_num"; "user_blocks"; "CTX_SIZE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR.InstX.Cut78a.FailLeaf"; "mF"; "touched"; "rho'"; "rw'"; "@Corelib.Init.Peano"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "liftK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "add"; "eqb"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "client_addr"; "top_high"; "vm_insensitive"; "alloc_static"; "errno_range"; "V_DEPTH"; "mem_kept"; "stack_win"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size";
"@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "BC_EQ"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "ok_pframeJ"; "S_after"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_pc"; "ms_svc_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "S_ret_fresh"; "enomem_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "s0"; "ar_p"; "tr_BK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E"; "brk_sval"; "valF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR.InstX.Cut78a.AtCut"; "rhoE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_AR.InstX.EntryAR"; "N_AR"; "R_AR"; "ar_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_BK.InstX.BK.Granted.AtCut"; "rhoE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB.InstX.EntryNB"; "N_NB"; "R_NB"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_grow_ok"; "brk_model_next"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "in_range"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.
Require LinuxProcessSemantics.LinuxProcessSem.Specs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require Stdlib.Logic.FunctionalExtensionality.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_AR.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := first [slia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; slia].
Local Ltac nia := first [snia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; snia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S143VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S16dS94VX;VR;VU;Sf5Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§1§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HMW := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HMW).
Local Abbreviation HLG := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§1§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Abbreviation secZ := (@U.Mal_ameta__G1.Mal_ameta_I.secZ s L).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation areasZ := (@U.Mal_ameta__G1.Mal_ameta_I.areasZ s L).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Abbreviation rw1v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb).
Local Notation "§2§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§3§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§3§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev183 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev183).
Local Abbreviation ev184 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;Vrd0;Se4S1bVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S90Q40A1SdF_;Vwok0;Se5S1bVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S99S95Vrd0;S90Q40A1SfL_;A2S97S94A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S15S154R1U4A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9bS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vevb;S91G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S15S154R1U8A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9aS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vavb;S91G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bVmW;A2Se5S1bVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Abbreviation cell_rw0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_rw0 s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok).
Local Abbreviation cell_view0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_view0 s L X R U rho rd0 wok0 vm HMI gd evb avb mW Erd Ewok).
Local Notation "§4§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S90Q40M0A1S2dVrho;P18A2S91G0S9cS94A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Abbreviation hold_sec := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Notation "§5§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation rng_stk := (§5§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§5§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2bS1bVrho;S132Sf2A1SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S166Sf5Vs;VL;A2Vrho;A2").
Local Abbreviation agree1 := (@U.Mal_ameta__G1.Mal_ameta_I.agree1 s L rho gd evb avb Hgd Hev Hav mW EmW).
Local Notation "§6§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§6§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Notation "§7§ h__" := (h__ s L rho gd evb avb mW) (at level 10, h__ global).
Local Abbreviation holds1 := (§7§ U.Mal_ameta__G1.Mal_ameta_I.holds1).
Local Abbreviation zr1_var := (§2§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (§7§ U.Mal_ameta__G1.Mal_ameta_I.rw1_v).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Section Cut78a.
  Hypothesis Hhd : st_free_meta_head s = None.
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : 0 < st_avail_meta_area_count s.
  Hypothesis Hinit : st_init_done s = true.
  Variable msC : machine_state.
  Hypothesis HsmC : ltac2:(tb__ "0|0|
S2bS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sa4S1bSa2Sb6A3SaScSe6A1Sf9Vtr;SfaVmsC;Vmd;A2A4A4").
  Variable Kc : ltac2:(tb__ "0|0|
ScSe6A1Se7OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3Se9Vvm;Se8Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S164S1bVok;VKc;A3").
  Hypothesis STK : ltac2:(tb__ "0|3|
S4S5bZ0S5cSfeVrho;A1M0SfdVrho;A1M1A2M2A2S4S5bS96VL;A1G2A2S4S5bG0S5eZ2Z40A2A2S5bG1S65SbeA1A2A2A2A2").

  Hypothesis HVI : vm_insensitive Kc.

  Lemma HIRv : img_reserved C_U vm. Proof using HMI. exact (mig_img HMI). Qed.

Local Abbreviation A_rr := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.rr s).
Local Abbreviation A_ap := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ap s).
Local Abbreviation A_am := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am s).
Local Abbreviation A_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.tA s).
Local Abbreviation A_ar := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ar s).
Local Abbreviation A_ao := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ao s).
Local Abbreviation A_rg0 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.rg0 s).
Local Abbreviation A_rgA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.rgA s).
Local Abbreviation A_s0_t := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.s0_t X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Notation "§8§ h__" := (h__ X R U s HI Hac) (at level 10, h__ global).
Local Abbreviation A_ap_facts := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ap_facts).
Local Abbreviation A_SPECA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.SPECA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_HIA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.HIA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_tA_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.tA_fields X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_region_of_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.region_of_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_C_tn := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.C_tn s).
Local Abbreviation A_am_prid := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am_prid).
Local Abbreviation A_fresh_slot := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.fresh_slot).
Local Abbreviation A_ap_fresh := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ap_fresh).
Local Abbreviation A_tApre := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.tApre s).
Local Abbreviation A_tA_upd := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.tA_upd X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_tApre_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.tApre_fields X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_am_fresh := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am_fresh).
Local Abbreviation A_area_cells_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.area_cells_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_old_noctx_loc := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.old_noctx_loc X R U s HI HXr).
Local Abbreviation A_image_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.image_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_ctx_cells_tAC := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ctx_cells_tAC X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_fp_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.fp_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_ub_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ub_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_footers_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.footers_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_pz := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.pz s L).
Local Abbreviation A_vmA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.vmA s L vm).
Local Notation "§9§ h__" := (h__ X R U s L HI Hac) (at level 10, h__ global).
Local Abbreviation A_pz_eq := (§9§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.pz_eq).
Local Abbreviation A_am_addr := (§9§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am_addr).
Local Abbreviation A_res_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.res_facts X R U s L HI Hac HL vm HV).
Local Abbreviation A_in_maps := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.in_maps X R U s L HI Hac vm HV).
Local Abbreviation A_page_vs_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.page_vs_image X R U s L HI Hac HL C_U vm HV HLG).
Local Abbreviation A_page_vs_footprint := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.page_vs_footprint X R U s L HI Hac HL C_U vm Hctx statics_in_image_U HV HLG).
Local Abbreviation A_fp_size := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.fp_size s L vm HV).
Local Abbreviation A_map_region_vs_page := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.map_region_vs_page X R U s L HI Hac HL C_U vm Hctx statics_in_image_U HV HLG).
Local Abbreviation A_layout_ok_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.layout_ok_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL C_U vm Hctx statics_in_image_U HV HLG).
Local Abbreviation A_region_live_t := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.region_live_t X R U s HI).
Local Abbreviation A_vm_ok_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.vm_ok_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL vm HV).
Local Abbreviation A_ledger_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.ledger_tA s L C_U vm HLG HIRv).
Local Abbreviation A_maps_wf_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.maps_wf_tA s L vm HMW).
Local Abbreviation A_xraw_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.xraw_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_am_notX := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am_notX X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_keys_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.keys_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_am_frame_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.am_frame_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_bounded_tA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.bounded_tA X R U s L HI HXr Hhd Hcnt Hac Hinit HL C_U vm Hctx statics_in_image_U HV HLG HIRv HB).
Local Abbreviation A_cell_whereA := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.cell_whereA X R U s L HI HXr Hhd Hcnt Hac Hinit HL).
Local Abbreviation A_block_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.block_where X R U s L HI HXr).
Local Abbreviation A_page_vs_block := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.page_vs_block X R U s L HI HXr Hac HL C_U vm Hctx statics_in_image_U HV HLG).
Local Abbreviation A_fp_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea.fp_where s L C_U vm HV HLG).

  Lemma areasZ_pz : areasZ = A_pz.
  Proof using HI Hac Hav Hev Hgd.
    unfold U.Mal_ameta__G1.Mal_ameta_I.areasZ. replace (st_avail_meta_area_count s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Bool.andb_false_r. rewrite <- A_pz_eq. unfold U.Mal_ameta__G1.Mal_ameta_I.zA, AllocMetaArea.ap, AllocMetaPost.ar_p, addr_of, loc_addr. destruct (st_avail_meta_areas s); reflexivity.
  Qed.
  Lemma pz_facts : ltac2:(tb__ "0|3|
S4S3S0S61S123Vs;VL;A2M0Z1000M1A2Z0M2A3S4S5bG1G0A2S4S5bS5cG0G1A2S96VL;A1A2S4S5bG2G0A2S5dG0S5eZ2Z40A2A2A2A2A2A2").
  Proof using HI HMI Hac Hav Hev Hgd. pose proof A_res_facts as (_ & _ & _ & _ & _ & R6 & R7 & R8 & R9). unfold PGSZ in *. repeat split; assumption || lia. Qed.
  Lemma acount_range : ltac2:(tb__ "0|1|
S4S5bZ1S6bVs;A1M0A2S5dG0S5eZ2Z23A2A2A2").
  Proof using HI HMI Hac Hav Hev Hgd.
    pose proof A_res_facts as (R1 & R2 & _ & R4 & _). pose proof A_ap_facts as (_ & _ & _ & _ & _ & _ & Hlen & _).
    top_ranges. unfold PGSZ in *. lia.
  Qed.

  Definition L78 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2Sb6A3S158A2Sa8Sb6A1A3A1").
  Definition LRF : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2Sb9A3S158A2Sa8Sb9A1A3A1").
  Lemma Pre_fail_eq : ltac2:(tb__ "0|0|
S3S31Sa4S1bSa2Sb9A3S180Sd0S182A2A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma Pre_ok_eq : ltac2:(tb__ "0|0|
S3S31Sa4S1bSa2SabA3S180Sd0Z0A2A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma L78_misc : ltac2:(tb__ "0|0|
S4S3S0S2eSd0A1Z21ef8A3S4S3S21S22Sd0Z11A2S23Ze2A1A3S4S3S21S22Sd0ZaA2S25Pb1A1A3S4S3S21S22Sd0ZbA2S23Z1000A1A3S4S3S21S22Sd0ZcA2S23Z3A1A3S3S1S2cSd0A1Sa5A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma L78_ecall : ltac2:(tb__ "0|0|
S3SbS173A1S15cS1bS2eSd0A1A2S12S173S175A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.

  Definition O_ctxA : sobj := ltac2:(tb__ "0|1|
SaeSa2S23Z0A1M0Sa3Pb0A1G0Sa3Pb7A1Sa3Pb8A1Sa3Pb9A1Sa3PbaA1Sa3Pb1A1A9").
  Definition O_brkA : sobj := O_brk AM_P (v 187).
  Definition O_errF : sobj := ltac2:(tb__ "0|1|
S49S25P18A1S23Na4A1M0S23Na0A1S9S24S27G0Z4S23ZcA1A3S10S24A1A3S44A5").
  Definition UNCH_R : list sobj := ltac2:(tb__ "0|0|
S9S20Sb0Sa2A1S9S20Sb1S9S20SacSa2A1S9S20Sb2Sa2A1S9S20Sb3Sa2Sa3PafA1Z1A3S9S20SddS9S20SdcS10S20A1A3A3A3A3A3A3A3").
  Definition CHG_R : list sobj := [O_errF].
  Definition stkR_cells : list cell := ltac2:(tb__ "0|1|
S9S24S27S23N60A1Z8M0S23Z1000A1A3S9S24S27S23N58A1G0S23Z21f00A1A3S9S24S27S23N48A1G0S23Z20edcA1A3S9S24S27S23N8A1G0S25PbA1A3S9S24S27S23N10A1G0S25P1cA1A3S9S24S27S23N18A1G0S25P1dA1A3S9S24S27S23N20A1G0S25P26A1A3S9S24S27S23N28A1G0S25P27A1A3S9S24S27S23N30A1G0S25P28A1A3S9S24S27S23N38A1G0Sa3PaeA1A3S10S24A1A3A3A3A3A3A3A3A3A3A3").
  Definition OBJ_R : list sobj := ltac2:(tb__ "0|1|
S9S20Sa6SdaA1S11S20S12fS20U4M0ScfA3S11S20Sd2S130S20G0ScfA3A3A3A3").
  Lemma LRF_objs : ltac2:(tb__ "0|0|
S3ScS20A1S2aSd1A1Sd8A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LRF_misc : ltac2:(tb__ "0|0|
S4S3S0S2eSd1A1Z20ec8A3S4S3S1S2cSd1A1Sa5A3S4S3ScS21A1S36Sd1A1S1fA3S4S3S5aS35Sd1A1S45A3S4S3SbS21A1S37Sd1A1S14S21A1A3S3S21S22Sd1ZaA2S23Z0A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LRF_cs : ltac2:(tb__ "0|0|
S0S4S5bZ1R1A2S5bR1Z1fA2A2S3SdS1dS62R2A1A1SfA3S3S21S22Sd1R3A2S1eS62R3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LRF z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Lemma block_vs_ctxR b n a : ltac2:(tb__ "0|1|
Se1SeS0S0A2SaS0S0Vb;Vn;A4S98VL;Vs;A2A3S4S5bVb;Va;A2S5dVa;S5cVb;Vn;A2A2A2S5S4S5bS144VL;A1M0Va;A2S5dVa;S5cG0S14fA2A2A2A1F_;F_;").
  Proof using HI HMI HXr Hav Hev Hgd.
    intros Hin Ha Hc. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4).
    cbn [fst snd] in B1, B2, B3, B4.
    destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4).
    pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold UNIT, IB in *. lia.
  Qed.

  Section FailLeaf.
    Variables (msF : machine_state) (rhoF : valuation).
    Hypothesis HagF : ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
    Hypothesis HsmF : ltac2:(tb__ "0|0|
S2bS1bVrhoF;Sd1SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").

    Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
    Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
    Lemma HOF : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3Sd8A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. rewrite LRF_objs in Hall. exact Hall. Qed.
    Lemma HfrF : ltac2:(tb__ "0|0|
S90Q40A1S4dVrhoF;Sd8R1A3S3SbS90Q8A1A1S17bVmsF;R2A2S26VrhoF;R2A2A3F_;Fa;").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. rewrite LRF_objs in Hfr. exact Hfr. Qed.
    Lemma rmF a : ltac2:(tb__ "0|0|
S3SbS90Q8A1A1S26VrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.
    Lemma F_pc : ltac2:(tb__ "0|1|
S3S90Q40M0A1S17cVmsF;A1S91G0Z20ec8A2A3").
    Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LRF_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
    Lemma F_pend : ltac2:(tb__ "0|1|
S3SbS90Q40A1M0A1S17dVmsF;A1S14G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
    Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
    Lemma F_regs : ltac2:(tb__ "0|0|
S58VrhoF;Sd1VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
    Lemma F_fregs : ltac2:(tb__ "0|0|
S55VrhoF;Sd1VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
    Lemma F_fcsr : ltac2:(tb__ "0|0|
S53VrhoF;S45VmsF;A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LRF_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
    Lemma F_resv : ltac2:(tb__ "0|0|
S59VrhoF;S14S21A1VmsF;A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LRF_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

    Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S187VrhoF;VmsF;ScfSd2A4").

    Lemma KU_entry : ltac2:(tb__ "0|0|
S12cS20S2fS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2A3ScfA3").
    Proof using Erd Ewok HMI Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom.
      unfold UNCH_R. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
      constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
      constructor; [exact HS|].
      constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
      constructor; [apply hold_brk|]. constructor.
    Qed.
    Lemma KU_leaf : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3ScfA3").
    Proof using HsmF.
      pose proof HOF as H. unfold OBJ_R in H. apply Forall_inv_tail in H.
      apply Forall_app in H as [H1 H]. apply Forall_app in H as [_ H2]. unfold UNCH_R. cbn [firstn skipn UNCH_R] in H1, H2.
      repeat (apply Forall_cons_iff in H1 as [? H1]). repeat (apply Forall_cons_iff in H2 as [? H2]). repeat (constructor; [assumption|]). constructor.
    Qed.
    Lemma KC_leaf : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3Sd2A3").
    Proof using HsmF. pose proof HOF as H. unfold OBJ_R in H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [H _]. exact H. Qed.
    Lemma Kvars : ltac2:(tb__ "0|0|
S3SdSe2S20S4cSa5A1S11S20ScfSd2A3A3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kcov : ltac2:(tb__ "0|0|
S3SdSe2S20S186ScfA3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Klits : ltac2:(tb__ "0|0|
S3SdSe2S20S188S11S20ScfSd2A3A3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdSe2S20S20S41SdLx;S4bR1A1SfS17S17S1S17Ll;M0G0S0S21ScSeS0S0A2A1ScS4fA1S17Ltmpl;Lflds;Lcnt;Lesz;X41x6Lo;S11S20ScfSd2A3A3SfA3"). Proof using . reflexivity. Qed.

    Lemma KIT_unch : ltac2:(tb__ "0|2|
S20S0Se1S20R2ScfA3S4S5bS13S0S0S28VrhoF;R3A2M0A3R2A2S5dR2S16S0S0G0A3A2A2S4S3SbS90Q8A1A1Se4S1bS150S91Q40R3A2M1A3Se4S1bVmW;G1A3A3S3SdSe5S1bS150G1A3Se5S1bVmW;G1A3A3A2F_;F_;Fx;Fo;").
    Proof using Erd Ewok HMI HagF Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_R CHG_R KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
    Lemma KIT_chgb : ltac2:(tb__ "0|3|
S20S0Se1S20R2Sd2A3S4S5bS13S0S0S28VrhoF;R3A2M0A3R2A2S5dR2S16S0S0G0A3A2A2S4S3SdSe5S1bS150S91Q40M1R3A2A3SfA3S6S90Q8A1M2G2S3SbG2A1Se4S1bS150S91G1R4A2A3S12G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
    Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_R CHG_R KC_leaf Kdunk). Qed.

    Definition touched (x : Z) : Prop := 237612 <= x < 237616.
    Lemma touched_dec x : ltac2:(tb__ "0|1|
S16eS151Vx;A1M0S5G0A1A2"). Proof using . unfold touched. apply range_dec. Qed.
    Lemma evF_lit z : ltac2:(tb__ "0|1|
S3S90Q40M0A1S30VrhoF;S23Vz;A1A2S91G0Vz;A2A3"). Proof using . reflexivity. Qed.
    Lemma CHG_ranges : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28VrhoF;A1Sd2A4S9G0SaS0S0Z3a02cZ3a030A4S10G0A1A3A3").
    Proof using HagF Hav Hev Hgd Htp.
      cbn [map CHG_R]. unfold O_errF. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.
    Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28VrhoF;A1ScfA4S9G0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3").
    Proof using HagF Hav Hev Hgd.
      cbn [map UNCH_R]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_sec, O_ctxA, O_ctxB, O_brkA, O_brk. cbn [am_got am_libc am_ctx AM_P].
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
      rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.
    Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S5bZ0Vx;A2S5dVx;S5eZ2Z40A2A2A2S17eVrhoF;S11S20ScfSd2A3S91Q40Vx;A2A3S7S6S20S20S4Se1S20R1ScfA3S4S5bS13S0S0S28VrhoF;R1A2M0A3Vx;A2S5dVx;S16S0S0G0A3A2A2A2Lo;A2S151Vx;A1A2F_;F_;").
    Proof using HagF Hav Hev Hgd Htp.
      intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
      pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
      destruct M as [E|[]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
    Qed.
    Lemma touched_in x : ltac2:(tb__ "0|1|
S151Vx;A1S6S20S20S4Se1S20R1Sd2A3S4S5bS13S0S0S28VrhoF;R1A2M0A3Vx;A2S5dVx;S16S0S0G0A3A2A2A2Lo;A2F_;").
    Proof using HagF Hav Hev Hgd Htp.
      intros T. unfold touched in T. exists O_errF. split; [left; reflexivity|].
      pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR. cbn [nth map CHG_R] in CR. rewrite CR. cbn [fst snd]. lia.
    Qed.

    Let bv1 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bS150A2Se5S1bS150A2A2").
    Let rv1 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bS150A2S90Q40A1SfL_;A2").
    Let rv0 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bVmW;A2S90Q40A1SfL_;A2").

    Theorem V1 : ltac2:(tb__ "0|1|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S5S151R2A1A1S4S3SbS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
    Proof using Erd Ewok HMI HagF Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp.
      intros x Hx NT.
      assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
      { destruct (in_ranges_dec rhoF (UNCH_R ++ CHG_R) (Z_to_bv 64 x)) as [IN|OUT].
        - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
        - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_R CHG_R _ OUT), rmF. auto. }
      destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
    Qed.
    Theorem VM : ltac2:(tb__ "0|0|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S151R2A1S147VL;Vs;R3A3S5S3SbS0A1Vbv1;R4A1S14S0A1A3A1F_;F_;F_;Fx;").
    Proof using HagF Hav Hev Hgd HsmF Htp.
      intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
      unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, Hb. discriminate.
    Qed.

    Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.
    Theorem VIN : ltac2:(tb__ "0|0|
S13bSe1S13bR1S11S13bS13eVs;A1S15eVs;A1A3A3S179VL;S151R2A3S148VL;Vbv1;R3A3F_;F_;Fc;").
    Proof using HI HMI HXr Hav Hev Hgd msF rhoF.
      intros c Hc (k & Hk & T). exfalso. pose proof Hctx' as HCX. unfold touched in T.
      destruct (cell_cases X R U s HI HXr c Hc) as [Hcc | [(a & next & Ha & Hca) | (g & am & Hu & Hcg)]].
      - pose proof (ctx_cell_in s L c Hcc) as RI. unfold range_incl, crange, e_ctx, cell_range in RI. cbn [fst snd loc_addr] in RI. rewrite HCX in RI.
        unfold CTX_SIZE in RI. lia.
      - pose proof (area_cell_in s L a next c Hca) as RI. pose proof (area_R a Ha) as (A1 & A2 & A3). top_ranges.
        unfold range_incl, crange, e_area, cell_range in RI. cbn [fst snd] in RI. unfold PGSZ in RI.
        assert (EA : zA a = loc_addr L (LMem a)) by (unfold zA, addr_of, loc_addr; destruct a; reflexivity). rewrite EA in A1, A2, A3. lia.
      - destruct (group_cell_in X R U s L HI g am c Hu Hcg) as (rg & _ & _ & _ & ER & RI & RI2).
        destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4). cbn [mc_img_lo mc_img_hi C_U] in G3.
        destruct RI2 as (d & Ed & Hd0 & Hd1). rewrite Ed in T. cbn [loc_addr] in T.
        assert (EA : addr_of L (am_mem am) = loc_addr L (LMem (am_mem am))) by (unfold addr_of, loc_addr; destruct (am_mem am); reflexivity).
        rewrite EA in G1, G2, G3. revert T G3 Hd0 Hd1 Hk. clear. cbn [loc_addr]. destruct (am_mem am) as [pr po]. cbn [padd]. intros. lia.
    Qed.

    Theorem minvI' : ltac2:(tb__ "0|0|
S16dS94VX;VR;VU;Sf5Vs;VL;A2Se4S1bS150A2Se5S1bS150A2Vvm;A8").
    Proof using Erd Ewok HI HMI HXr HagF Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp bv0 rv0.
      unfold MInvI. pose proof Hctx' as HCX.
      refine (minv_postG C_U (Inv X R U) (Inv X R U) s s L (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm
                HMI0 HI HB HL eq_refl eq_refl HV touched touched_dec V1 VIN VM (fun c Hc _ => Hc) _ _ _ statics_in_image_U _ _ _).
      - intros c Hc. exact (cell_spanI X R U s L HI HXr HL c Hc).
      - intros x Hx. exact (owned_spanI s L HL x Hx).
      - intros c Hc. exact (cell_w_posI s c Hc).
      - intros x T _. right. unfold touched in T. unfold mc_errno. cbn [mc_tp C_U]. lia.
      - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
        unfold CTX_SIZE in Hx. clear - Hx. lia.
      - intros Hf. exfalso. rewrite Hinit in Hf. discriminate.
    Qed.

    Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SdS90Q40A1L_;S18S60Z64M0S2Vj;A1M1A2S67G1Z84A2A2S30VrhoF;S22Sd1S63G1G0A2A2A2S2dVrho;Vj;A2Xdx2").
    Definition rho' : valuation := ltac2:(tb__ "0|0|
S4aS153S3dVrhoF;A1S150A3").
    Lemma rw'_low j : ltac2:(tb__ "0|0|
S15fVj;P64A2S3S90Q40A1S153Vj;A1S2dVrho;Vj;A2A3F_;").
    Proof using Hav Hev Hgd. intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity. Qed.
    Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S11eS1cVrho;S152A3").
    Proof using HagF Hav Hev Hgd.
      split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
      intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
    Qed.
    Lemma rwF_low j : ltac2:(tb__ "0|0|
S15fVj;PaaA2S3S90Q40A1S2dVrhoF;Vj;A2S2dVrho;Vj;A2A3F_;").
    Proof using HagF Hav Hev Hgd. intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj. Qed.
    Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S5bZ1Vz;A2S5bVz;Z1fA2A2S3SdS1dS62Vz;A1M0A1SfA3S6S1S1S4S3S21S1eG0A1S25R1A1A3S15fR1P64A2A2Lvv;A2F_;F_;").
    Proof using Hav Hev Hgd.
      intros Hr Hcs.
      pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
      cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
      destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
    Qed.
    Lemma reg_sv_null z : ltac2:(tb__ "0|2|
S4S5bZ1Vz;A2S5bVz;Z1fA2A2S3S21S22S134Sf2A1Vz;A2SdS21L_;M0S66Vz;ZaA2S23Z0A1G0S1dS62Vz;A1M1A1S1eG1A1S25S161P64S163G1A1A2A1Xdx2Xdx2A3F_;").
    Proof using Hav Hev Hgd.
      intros Hz.
      pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_null IEC_U) z)
                     (if (z =? 10) then SLit 0 else if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
      apply sv_eqb_sound in H. exact H.
    Qed.
    Lemma freg_sv_null z : ltac2:(tb__ "0|2|
S4S5bZ0M0Vz;A2S5bVz;Z1fA2A2S6S1S1S4S3S21S54S134Sf2A1Vz;A2S25R1A1M1A3S4S3S21S12dS21S62Vz;A1S1fS23G0A1A4G1A3S4S160P3cR1A2S15fR1P64A2A2A2A2Lvv;A2F_;").
    Proof using Hav Hev Hgd.
      intros Hz.
      pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
      unfold freg_sv. change (ss_fregs (L_am_null IEC_U)) with pre_fregs.
      destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
      apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
    Qed.
    Lemma EBs : ltac2:(tb__ "0|1|
S3S90Q40A1S30S152S25PaA1M0A2S30VrhoF;G0A2A3").
    Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
    Lemma ELs : ltac2:(tb__ "0|0|
S3S0S43S152S25S16aA1A2S43VrhoF;S25PfA1A2A3").
    Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
    Lemma RSF : ltac2:(tb__ "0|1|
S3SeS0S0A2S28VrhoF;Sa6SdaA1A2SaS0S0S5cSfeVrho;A1M0SfdVrho;A1A2G0A4A3").
    Proof using HagF Hav Hev Hgd.
      rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkR_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkR_cells) ltac:(left; reflexivity)).
      apply rng_stk.
    Qed.
    Lemma RS' : ltac2:(tb__ "0|1|
S3SeS0S0A2S28S152S16cS139A1A2SaS0S0S5cSfeVrho;A1M0SfdVrho;A1A2G0A4A3").
    Proof using HagF Hav Hev Hgd. rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity. Qed.

    Theorem smatch_null : ltac2:(tb__ "0|0|
S2bS1bS152S134Sf2A1SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").
    Proof using EmW HagF Hav Hev Hgd HsmC HsmF STK.
      pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
      unfold smatch. cbn [fst snd cfg_ms cfg_model].
      split; [vm_compute; reflexivity|].
      split; [exact F_pc|].
      split; [exact F_pend|]. split; [exact F_halt|]. split; [exact HromF|]. split; [exact HroF|].
      split.
      {   intros r Hr0. rewrite (F_regs r Hr0).
        assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
        rewrite reg_sv_null by lia.
        destruct (bv_unsigned r =? 10) eqn:E10.
        - apply Z.eqb_eq in E10. destruct LRF_misc as (_ & _ & _ & _ & _ & Ma0).
          replace r with (Z_to_bv 5 10) by (apply bv_eq; rewrite E10; reflexivity). change (bv_unsigned (Z_to_bv 5 10)) with 10. rewrite Ma0. reflexivity.
        - destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
          + destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100).
            rewrite (LRF_cs (bv_unsigned r) ltac:(lia) CS), E.
            cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; lia.
          + cbn [eval rho' rw]. unfold rw'.
            replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
              by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
            replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
            reflexivity. }
      split.
      {   intros r. rewrite (F_fregs r).
        assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
        destruct (freg_sv_null (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
        unfold freg_sv. destruct LRF_misc as (_ & _ & Mfr & _). rewrite Mfr, E2.
        cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
      split; [exact F_fcsr|].
      split; [exact F_resv|].
      split.
      {
        assert (HOS : obj_holds segsU rhoF msF (O_stk stkR_cells)) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
        split; [|split].
        - constructor; [|constructor].
          apply obj_holds_drop_cells in HOS.
          destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
          cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
          rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
          intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
        - cbn [pairwise_disjoint]. split; [constructor|exact I].
        - intros a Ha. cbn [rm rho'].
          destruct (in_ranges_dec rhoF (UNCH_R ++ CHG_R) a) as [IN|OUT].
          + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
          + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
            apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS. rewrite RS' in HaS.
            unfold OBJ_R. constructor; [cbn zeta; rewrite RSF; exact HaS|].
            apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [|exact RR].
            revert Ho. clear. unfold UNCH_R, CHG_R. cbn [firstn skipn app In]. tauto. }

      unfold L_am_null. cbn [ss_facts].
      assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
      { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
      pose proof (smatch_facts_hold segsU _ _ _ HsmC) as HF1.
      assert (AGR1 : forall f, sprop_below NF f = true -> SymState.holds (rho1 mW) f -> SymState.holds rho f).
      { intros f Hb Hh. exact (proj2 (SymState.holds_agree NF rho (rho1 mW) f agree1 Hb) Hh). }
      repeat (constructor; [apply AGR; [reflexivity|]; apply AGR1; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF1); vm_compute; tauto|]). constructor.
    Qed.

    Theorem kept : ltac2:(tb__ "0|1|
S16bS1bS94Sf5Vs;VL;A2M0G0S26Vrho;A1S150A6").
    Proof using EmW HI HMI HXr HagF Hav Hev Hgd Htp.
      intros a Ha CA _ NE NS. pose proof Hctx' as HCX. rewrite <- EmW.
      destruct (in_ranges_dec rhoF (UNCH_R ++ CHG_R) (Z_to_bv 64 a)) as [IN|OUT].
      2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). rewrite rmF. reflexivity. }
      exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
      assert (RNG : In (obj_range rhoF o) [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (369616, 369628); (369632, 369696); (370536, 370544)]
                    \/ In (obj_range rhoF o) [(237612, 237616)]).
      { apply in_app_iff in Ho as [Ho|Ho]; [left; rewrite <- UNCH_rangesF | right; rewrite <- CHG_ranges]; apply in_map; exact Ho. }
      unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_tp C_U] in NS, NE.
      assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
      { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
        - top_ranges. unfold CTX_SIZE in Hc. lia.
        - apply (block_vs_ctxR b n a); [exact Hin | exact Hr | rewrite HCX; exact Hc].
        - apply H. cbn [mc_ctx C_U]. exact Hc. }
      unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX.
      destruct RNG as [M|M]; repeat (destruct M as [M|M]; [rewrite <- M in RR; cbn [fst snd] in RR; lia|]); destruct M.
    Qed.

    Theorem maps_keptR : ltac2:(tb__ "0|0|
Sf4Sf5Vs;VL;A2S26Vrho;A1S150A3").
    Proof using EmW HI HMI HagF Hav Hev Hgd Htp.
      intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
      destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI.
      destruct (in_ranges_dec rhoF (UNCH_R ++ CHG_R) (Z_to_bv 64 x)) as [IN|OUT].
      2:{ unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply rmF. }
      exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia.
      pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite map_app, UNCH_rangesF, CHG_ranges in RNG. cbn [app In] in RNG.
      clear - RNG RR NI.
      repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; lia|]). destruct RNG.
    Qed.
    Theorem canaryR : ltac2:(tb__ "0|0|
Sf3S1bS94S26Vrho;A1S150A4").
    Proof using EmW Erd Ewok HMI HagF Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF.
      intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
      pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_R] in R0, R1.
      destruct Hx as [Hx|Hx].
      - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
      - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
    Qed.

    Theorem post_null : ltac2:(tb__ "0|0|
S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A5").
    Proof using EmW Erd Evm Ewok HI HKc HMI HXr Hac HagF Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC HsmF Htp STK bv0 bv1 rv0 rv1.
      exists (L_am_null IEC_U), (JL_am_null segsU C_U X R U (mkMA s L) Kc), rho'.
      split; [left; reflexivity|]. split; [exact agree_vals_rho'|]. split; [exact smatch_null|].
      cbn [w_tr w_cfg fst snd cfg_model].
      exists (mkMA s L). cbn [ma_s ma_L].
      split; [unfold MInvIR; cbn [rm rho']; rewrite <- Evm; exact minvI'|].
      split.
      { split; [exact HXr|]. split; [exact Hinit|]. split; [apply am_frame_refl|]. split; [apply am_fields_same_refl|].
        split; [intros g am; tauto|]. split; [apply ub_same_refl|]. split; [intros q Hq; exact Hq | apply layout_extends_refl]. }
      split; [exact kept|]. split; [exact maps_keptR|]. split; [exact canaryR|].
      split; [|exact HKc].
      exists [(KMprotect (ar_p s), 0)]. pose proof (yields_AR s Hhd Hcnt Hac 0) as Y. cbn [Z.eqb] in Y. rewrite A_s0_t in Y. exact Y.
    Qed.
  End FailLeaf.

  Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S177S1bVok;S157SffVtr;Vmd';A2A1A3F_;").
  Proof using HOK. intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho). Qed.

  Lemma map_contains_of_range l a n : ltac2:(tb__ "0|2|
S5bZ0M0Va;A2S5bG0Vn;A2S5dS5cVa;Vn;A2S5eZ2Z40A2A2S9eVl;Va;Vn;A3S3SdSeaVl;S91Q40M1Va;A2S91G1Vn;A2A3SfA3F_;F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros Ha Hn Han (e & He & H1 & H2). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite !u64 by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
  Qed.

  Lemma page_noaccess : ltac2:(tb__ "0|0|
S9eSedVvm;A1S123Vs;VL;A2S7fA3").
  Proof using HI HMI Hac Hav Hev Hgd.
    pose proof A_ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT). pose proof HV as (_ & V2 & _).
    destruct (V2 A_ar A_rg0 Hr Hk) as (W1 & W2 & W3).
    assert (EO : A_ao = PGSZ * (A_ao / PGSZ)) by (unfold PGSZ in *; Z.to_euclidean_division_equations; lia).
    unfold AllocMetaArea.pz. replace (ly_reg L A_ar + A_ao) with (ly_reg L A_ar + PGSZ * (A_ao / PGSZ)) by (clear - EO; lia). apply W2.
    - unfold PGSZ in *. Z.to_euclidean_division_equations; nia.
    - assert (PGSZ * 1 <= PGSZ * st_avail_meta_area_count s) by (apply Z.mul_le_mono_nonneg_l; unfold PGSZ; lia). rewrite Z.mul_add_distr_l, <- EO. lia.
    - rewrite <- EO. intros Hin. pose proof (Hrw _ Hin). lia.
  Qed.
  Lemma page_maps : ltac2:(tb__ "0|0|
S9eSebVvm;A1S123Vs;VL;A2S7fA3").
  Proof using HI HMI Hac.
    pose proof A_ap_facts as (Eap & Hr & Hk & Hl & Ho1 & Ho2 & Hlen & Hrw & LT). pose proof A_res_facts as (R1 & R2 & R3 & R4 & R5 & _).
    exists (wz (ly_reg L A_ar), wz (rg_len A_rg0)). split; [exact A_in_maps|]. cbn [fst snd]. unfold wz.
    top_ranges.
    assert (B1 : 0 <= ly_reg L A_ar < 2 ^ 64) by (clear - R1 R2 R4 R5; unfold PGSZ in *; lia).
    assert (B2 : 0 <= rg_len A_rg0 < 2 ^ 64) by (clear - R1 R2 R4 R5; unfold PGSZ in *; lia).
    rewrite (u64 _ B1), (u64 _ B2). unfold AllocMetaArea.pz. clear - R4 R5. unfold PGSZ in *. lia.
  Qed.
  Lemma page_noaccess_mc : ltac2:(tb__ "0|1|
S3SdSeaSedSe8Vmd;A1A1S91Q40M0S123Vs;VL;A2A2S91G0Z1000A2A3SfA3").
  Proof using Evm HI HMI Hac Hav Hev Hgd.
    pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges. rewrite <- Evm.
    apply map_contains_of_range; [lia | lia | lia | exact page_noaccess].
  Qed.
  Lemma page_maps_mc : ltac2:(tb__ "0|1|
S3SdSeaSebSe8Vmd;A1A1S91Q40M0S123Vs;VL;A2A2S91G0Z1000A2A3SfA3").
  Proof using Evm HI HMI Hac Hav Hev Hgd.
    pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges. rewrite <- Evm.
    apply map_contains_of_range; [lia | lia | lia | exact page_maps].
  Qed.
  Lemma mmap_nZ_4096 : mmap_nZ (Z_to_bv 64 4096) = 4096. Proof using . vm_compute. reflexivity. Qed.
  Lemma mmap_n_4096 : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096. Proof using . unfold mmap_n. rewrite mmap_nZ_4096. reflexivity. Qed.

  Definition valC (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;S26VrhoX;A1A7VrhoX;A3").
  Lemma evC rhoX e : ltac2:(tb__ "0|0|
Sd3VrhoX;A1S3SdS3fSa5Ve;A2SfA3S3S90Q40A1S30VrhoX;Ve;A2S30SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2A3F_;F_;").
  Proof using . intros A He. rewrite <- (eval_agree AM_NEXT (rho1 (rm rhoX)) rhoX e A He). exact (eval_set_rm (rho1 mW) (rm rhoX) e). Qed.
  Lemma evC177 rhoX : ltac2:(tb__ "0|1|
Sd3VrhoX;A1S3S90Q40M0A1S30VrhoX;S25Pb1A1A2S91G0S123Vs;VL;A2A2A3F_;").
  Proof using HI Hac Hav Hev Hgd mW. intros VX. rewrite (evC rhoX (SVar 177) VX eq_refl). rewrite <- areasZ_pz. exact (ev177 mW). Qed.
  Lemma valC_ext rhoX rhoY n : ltac2:(tb__ "0|0|
Sd3VrhoX;A1S160Sa5Vn;A2S33Vn;VrhoX;VrhoY;A3Sd3VrhoY;A1F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros (A1 & A2 & A3) Hn (B1 & B2 & B3). split; [|split].
    - intros i Hi. cbn [rho1 rw]. rewrite <- (B1 i) by lia. rewrite <- (A1 i Hi). reflexivity.
    - intros l. cbn. rewrite <- B2, <- A2. reflexivity.
    - intros x. reflexivity.
  Qed.
  Definition memC (m : word -> option byte) : Prop := ltac2:(tb__ "0|3|
S90Q40M0A1S5S4S5bS123Vs;VL;A2M1S92G0R1A2M2A2S5dG2S5cG1Z1000A2A2A2A1S3SbS90Q8A1A1Vm;R2A1VmW;R2A1A3F_;Fx;").
  Definition zeroC (m : word -> option byte) : Prop := ltac2:(tb__ "0|5|
S90Q40M0A1S4S5bS123Vs;VL;A2M1S92G0R1A2M2A2S5dG2S5cG1Z1000A2A2A2S3SbS90Q8M3A1M4A1Vm;R2A1S12G4S91G3Z0A2A2A3F_;Fx;").

  Definition stk78_cells : list cell := ltac2:(tb__ "0|1|
S9S24S27S23N48A1Z8M0S23Z20edcA1A3S9S24S27S23N8A1G0S25PbA1A3S9S24S27S23N10A1G0S25P1cA1A3S9S24S27S23N18A1G0S25P1dA1A3S9S24S27S23N20A1G0S25P26A1A3S9S24S27S23N28A1G0S25P27A1A3S9S24S27S23N30A1G0S25P28A1A3S9S24S27S23N38A1G0Sa3PaeA1A3S10S24A1A3A3A3A3A3A3A3A3").
  Lemma L78_objs : ltac2:(tb__ "0|1|
S3ScS20A1S2aSd0A1S9S20Sa6Se0A1S11S20S12fS20U4M0ScfA3S11S20S9S20SafS10S20A1A3S130S20G0ScfA3A3A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma L78_ranges (rhoL : valuation) : ltac2:(tb__ "0|2|
Sd3VrhoL;A1S3ScSeS0S0A2M0A1S12eS20G0S28VrhoL;A1S2aSd0A1A4S9G0SaS0S0S5cSfeVrho;A1M1SfdVrho;A1A2G1A4S9G0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3A3A3F_;").
  Proof using Hav Hev Hgd Htp mW.
    intros HagL. rewrite L78_objs. cbn [map firstn skipn app UNCH_R].
    rewrite (ReabKit.range_ag (rho1 (rm rhoL)) rhoL [O_stk stk78_cells] [] AM_NEXT HagL ltac:(vm_compute; reflexivity) (O_stk stk78_cells) ltac:(left; reflexivity)).
    change (obj_range (rho1 (rm rhoL)) (O_stk stk78_cells)) with (obj_range (rho1 mW) (O_stk stk78_cells)). rewrite rng_stk.
    unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxA, O_ctxB, O_brkA, O_brk. cbn [am_got am_libc am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    assert (EL0 : forall z, eval rhoL (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evC rhoL (v 173) HagL eq_refl), ev173.
    rewrite (evC rhoL (SVar 24) HagL eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.
  Lemma segs_inside : ltac2:(tb__ "0|1|
S3SdSe2S16fS16fS18S60Z10000S64S170R1A1A1M0A2S60S5cG0S64S171R1A1A1A2Z5b000A2A2Lseg;S1bA3SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma ro_addr_page (x : word) : ltac2:(tb__ "0|2|
S4S5bS123Vs;VL;A2M0S92Q40Vx;A2M1A2S5dG1S5cG0Z1000A2A2A2S3SdS4eS1bVx;A2S17A3F_;").
  Proof using HI HMI Hac Hav Hev Hgd.
    intros Hx. apply ro_addr_false_of_no_segment.
    destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
    destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
    pose proof (proj1 (forallb_forall _ _) segs_inside seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
    apply (A_page_vs_image (bv_unsigned x)); [cbn [mc_img_lo mc_img_hi C_U]; lia|]. unfold PGSZ. exact Hx.
  Qed.
  Lemma L78_objs_miss rhoL : ltac2:(tb__ "0|1|
Sd3VrhoL;A1S20Se1S20R1S2aSd0A1A3S3eS28VrhoL;R2A2SaS0S0S123Vs;VL;A2M0S5cG0Z1000A2A4A2F_;Fo;F_;").
  Proof using HI HMI Hac Hav Hev Hgd Htp STK mW.
    intros HagL o Ho. pose proof (in_map (obj_range rhoL) _ _ Ho) as RO. rewrite (L78_ranges rhoL HagL) in RO.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof pz_facts as (P1 & P2 & P3 & P4). pose proof A_page_vs_image as MISS.
    cbn [mc_img_lo mc_img_hi C_U] in MISS. unfold PGSZ in MISS. clear - RO MISS P2 P3 S2. top_ranges.
    assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (A_pz, A_pz + 4096)).
    { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
      destruct (Z_le_dec hi A_pz); [lia|]. destruct (Z_le_dec (A_pz + 4096) lo); [lia|]. exfalso.
      destruct (Z_le_dec A_pz lo); [apply (MISS lo); lia | apply (MISS A_pz); lia]. }
    destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
    repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
  Qed.

  Definition md2 : Model := ltac2:(tb__ "0|1|
S194Vmd;S91Q40M0S123Vs;VL;A2A2S91G0Z1000A2A3").
  Lemma K2 : Kc tr md2.
  Proof using HKc HOK. destruct HOK as (_ & _ & [VI _]). unfold md2, mprotect_model_next. apply VI. exact HKc. Qed.

  Lemma K2x : Kc tr md2.
  Proof using HKc HVI. unfold md2, mprotect_model_next. apply HVI. exact HKc. Qed.
  Lemma vm2_eq : ltac2:(tb__ "0|0|
S3Se9Se8Sd5A1S127Vs;VL;Vvm;A3A3").
  Proof using Evm HI HMI Hac Hav Hev Hgd.
    unfold md2, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. rewrite <- Evm. unfold AllocMetaArea.vmA.
    pose proof pz_facts as (_ & _ & _ & P4). rewrite (u64 A_pz P4). change (bv_unsigned (Z_to_bv 64 4096)) with 4096. unfold PGSZ. reflexivity.
  Qed.

  Definition LC0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2SabA3S158A2Sa8SabA1A3A1").
  Definition LC : sstate := ltac:(let x := eval vm_compute in LC0 in exact x).
  Lemma LC_eq : LC0 = LC. Proof using . vm_cast_no_check (@eq_refl sstate LC). Qed.
  Definition pageK : sobj := O_page (SVar 177).
  Definition subC : list (positive * sv) := ltac2:(tb__ "0|1|
S9SeS1S21A2M0SaS1S21Pc9S22SceZ9A2A4S9G0SaS1S21PccS22SceZ1A2A4S9G0SaS1S21PcdS22SceZ5A2A4S9G0SaS1S21PceS22SceZ6A2A4S9G0SaS1S21PcfS22SceZ7A2A4S9G0SaS1S21Pd0S22SceZ8A2A4S9G0SaS1S21Pd2S22SceZaA2A4S9G0SaS1S21Pd3S22SceZbA2A4S9G0SaS1S21Pd4S22SceZcA2A4S9G0SaS1S21Pd5S22SceZdA2A4S9G0SaS1S21Pd6S22SceZeA2A4S9G0SaS1S21Pd7S22SceZfA2A4S9G0SaS1S21Pd8S22SceZ10A2A4S9G0SaS1S21Pd9S22SceZ11A2A4S9G0SaS1S21PdcS22SceZ14A2A4S9G0SaS1S21Pe4S22SceZ1cA2A4S9G0SaS1S21Pe5S22SceZ1dA2A4S9G0SaS1S21Pe6S22SceZ1eA2A4S9G0SaS1S21Pe7S22SceZ1fA2A4S10G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Definition srcF : sstate := ltac2:(tb__ "0|0|
Sa9S38S2eSceA1S3aSceA1S36SceA1S35SceA1S37SceA1S11S20S2aSceA1S9S20Sd6S10S20A1A3A3S34SceA1S2cSceA1S39SceA1A9S9S29S47S174Sa3PbaA1S23Z0A1A3S10S29A1A3A2").
  Definition srcN : sstate := ltac2:(tb__ "0|2|
Sa9S38S2eSceA1S3aSceA1S36SceA1S35SceA1S37SceA1S11S20S2aSceA1S9S20Sd6S9S20Sa7S10S20A1A3A3A3S34SceA1S2cSceA1S39SceA1A9S9S29SbfPbaM0A1S9S29S46G0Z3A2S9S29S3bS25G0A1M1S23S5eZ2Z2fA2A1A2S9S29S3bS23Z1000A1G1A2S10S29A1A3A3A3A3A2").
  Lemma entF : ltac2:(tb__ "0|0|
S3SdS15dSdeSa4S1bSa2Sb4A3Sd7A3SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma entN : ltac2:(tb__ "0|0|
S3SdS15dSdfSa4S1bSa2Sb5A3Sd7A3SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma LC_misc : ltac2:(tb__ "0|1|
S4S3S0S2eSceA1Z20e3cA3S4S3S1S2cSceA1Sa5A3S4S3S21S22SceZ9A2S25Pb1A1A3S4S3ScS20A1S2aSceA1S2aSd0A1A3S3SdSe2SeS1S21A2M0G0S60Zc8S2S13S1S21R1A3A1A2Lp;Sd7A3SfA3A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma swfF : ltac2:(tb__ "0|0|
S3SdS42S38S2eSceA1S3aSceA1S36SceA1S35SceA1S37SceA1S11S20S2aSceA1S9S20Sd6S10S20A1A3A3S34SceA1S2cSceA1S39SceA1A9A1SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma swfN : ltac2:(tb__ "0|0|
S3SdS42S38S2eSceA1S3aSceA1S36SceA1S35SceA1S37SceA1S11S20S2aSceA1S9S20Sd6S9S20Sa7S10S20A1A3A3A3S34SceA1S2cSceA1S39SceA1A9A1SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

  Section AtCut.
    Variables (msK : machine_state) (rhoC : valuation).
    Hypothesis VC : valC rhoC.
    Hypothesis MC : memC (rm rhoC).
    Hypothesis ZC : zeroC (rm rhoC).
    Hypothesis HsmK : ltac2:(tb__ "0|0|
S2bS1bVrhoC;SceSaScSe6A1Sf9Vtr;SfaVmsK;Sd5A2A4A4").

    Lemma HromC : rom_ok segsU msK. Proof using HsmK. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmK))))). Qed.
    Lemma pageK_range : ltac2:(tb__ "0|1|
S3SeS0S0A2S28VrhoC;Sd6A2SaS0S0S123Vs;VL;A2M0S5cG0Z40A2A4A3").
    Proof using HI HMI Hac Hav Hev Hgd VC mW.
      clear HsmK ZC MC. unfold obj_range, obj_lo_of, obj_hi_of, pageK, O_page. cbn [ob_base ob_lo ob_hi]. rewrite (evC177 rhoC VC). rewrite !soff_lit_small by lia.
      pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges. rewrite u64 by lia. f_equal; lia.
    Qed.
    Lemma hold_pageK : ltac2:(tb__ "0|0|
S2fS1bVrhoC;S155VmsK;S26VrhoC;A1A2Sd6A4").
    Proof using HI HMI Hac Hav Hev Hgd HsmK VC ZC mW.
      pose proof HromC as HromC. clear HsmK. pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges.
      change pageK with (carved (SVar 177) 0 64
        [(0, 8%nat, SLit 0); (8, 8%nat, SLit 0); (16, 4%nat, SLit 0); (20, 4%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0); (40, 8%nat, SLit 0); (48, 4%nat, SLit 0); (52, 4%nat, SLit 0); (56, 8%nat, SLit 0)]).
      assert (B : bv_unsigned (eval rhoC (SVar 177)) = A_pz) by (rewrite (evC177 rhoC VC); apply u64; lia).
      assert (ZB : forall off, 0 <= off < 64 -> rm rhoC (Z_to_bv 64 (A_pz + off)) = Some (Z_to_bv 8 0)).
      { intros off Hoff. apply ZC. rewrite u64 by lia. lia. }
      apply obj_holds_frame_lit; rewrite ?B; try exact HromC; try lia.
      - cells_inside_tac.
      - intros off Hoff. unfold Glue.wok_of, Glue.rd_of. rewrite (ZB off Hoff). split; [reflexivity | eexists; reflexivity].
      - unfold cells_in_view. apply Forall_forall. intros [[off k] vv] Hin j Hj.
        assert (HH : vv = SLit 0 /\ 0 <= off /\ off + Z.of_nat k <= 64 /\ (k <= 8)%nat).
        { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <- <-; (split; [reflexivity|cbn; lia]). }
        destruct HH as (-> & O1 & O2 & K8). unfold Glue.rd_of. cbn [eval]. rewrite <- Z.add_assoc, (ZB (off + Z.of_nat j) ltac:(lia)). rewrite nth_enc_bytes by lia. f_equal. f_equal. symmetry. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
    Qed.

    Lemma views_at (m1 m2 : word -> option byte) x : ltac2:(tb__ "0|1|
S3SbS90Q8A1A1M0Vm1;Vx;A1Vm2;Vx;A1A3S4S3SdSe5S1bVm1;Vx;A3Se5S1bVm2;Vx;A3A3S3G0Se4S1bVm1;Vx;A3Se4S1bVm2;Vx;A3A3A2F_;").
    Proof using . intros E. unfold Glue.wok_of, Glue.rd_of. rewrite E. auto. Qed.

    Lemma hold_tailK T : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S2fS1bVrhoC;S155VmsK;S26VrhoC;A1A2Sa7A4F_;").
    Proof using Erd Ewok HI HMI Hac Hav Hev Hgd HsmK MC VC.
      pose proof HromC as HromC. clear HsmK ZC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
      assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
      assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
      assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
      pose proof (area_R T HinT) as (RT1 & RT2 & RT3). top_ranges.
      assert (B : bv_unsigned (eval rhoC (v 186)) = zA T) by (rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT; cbn [optrZ]; apply u64; lia).
      assert (NG : forall off, 8 <= off < 16 -> ~ (A_pz <= zA T + off < A_pz + 4096)).
      { intros off Hoff G.
        apply (A_page_vs_footprint (LMem T, PGSZ) (zA T + off) (e_area_In s T HinT)); [|unfold PGSZ; exact G]. cbn [fst snd]. unfold zA, addr_of in *. unfold PGSZ. clear - Hoff. lia. }
      assert (MEQ : forall off, 8 <= off < 16 -> rm rhoC (Z_to_bv 64 (zA T + off)) = mW (Z_to_bv 64 (zA T + off))).
      { intros off Hoff. apply MC. rewrite u64 by lia. exact (NG off Hoff). }
      assert (C0 : In (MCell (LMem (padd T 8)) 8 (optr None)) (image s)).
      { unfold image. apply in_app_iff. right. apply in_app_iff. left.
        rewrite ET. clear - Hne. induction (st_areas s) as [|a0 t0 IH]; [exfalso; exact (Hne eq_refl)|].
        cbn [areas_cells last]. destruct t0 as [|b0 t'].
        - apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. right. left. reflexivity.
        - apply in_app_iff. right. apply IH. discriminate. }
      assert (A0 : loc_addr L (mc_loc (MCell (LMem (padd T 8)) 8 (optr None))) = zA T + 8) by (cbn [mc_loc]; unfold zA, addr_of, loc_addr; destruct T; cbn [padd]; lia).
      change O_tail with (carved (v 186) 8 16 [(8, 8%nat, SLit 0)]).
      apply obj_holds_frame_lit; rewrite ?B; try exact HromC; try lia.
      - cells_inside_tac.
      - intros off Hoff. destruct (views_at (rm rhoC) mW (Z_to_bv 64 (zA T + off)) (MEQ off Hoff)) as [-> ->].
        exact (cell_rw0 _ 0 (zA T) 8 8 C0 eq_refl eq_refl A0 (zA T + off) ltac:(lia)).
      - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
        replace (zA T + 8 + Z.of_nat j) with (zA T + (8 + Z.of_nat j)) by lia.
        destruct (views_at (rm rhoC) mW (Z_to_bv 64 (zA T + (8 + Z.of_nat j))) (MEQ (8 + Z.of_nat j) ltac:(lia))) as [_ ->].
        replace (zA T + (8 + Z.of_nat j)) with (zA T + 8 + Z.of_nat j) by lia.
        apply (cell_view0 _ 0 (zA T) 8 8 (SLit 0) C0 eq_refl eq_refl ltac:(lia) A0); [reflexivity | exact Hj].
    Qed.

    Definition rhoE : valuation := rho_sub rhoC subC.

    Lemma LC_objs_miss o : ltac2:(tb__ "0|1|
Se1S20Vo;S2aSceA1A3S3eS28VrhoC;Vo;A2SaS0S0S123Vs;VL;A2M0S5cG0Z1000A2A4A2F_;").
    Proof using HI HMI Hac Hav Hev Hgd Htp STK VC mW. intros Ho. pose proof LC_misc as (_ & _ & _ & EO & _). rewrite EO in Ho. exact (L78_objs_miss rhoC VC o Ho). Qed.

    Lemma enter_first : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S14S69A1A3S2bS1bS18bSa4S1bSa2Sb4A3SaScSe6A1Sf9Vtr;SfaVmsK;Sd5A2A4A4F_;").
    Proof using HI HMI Hac Hav Hev Hgd HsmK Htp STK VC ZC mW.
      intros HT. unfold rhoE. apply (entails_sound segsU srcF _ subC rhoC _ entF).
      unfold srcF. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [| |vm_compute; reflexivity].
      - apply (smatch_extend_objs segsU rhoC LC tr msK md2 [pageK] (ss_next LC) HsmK swfF).
        + constructor; [apply hold_pageK | constructor].
        + constructor; [|constructor]. apply Forall_forall. intros o' Ho'. rewrite pageK_range.
          pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
        + cbn. split; [constructor | exact I].
      - constructor; [|constructor]. cbn [SymState.holds]. unfold branch_taken, bv_eqb. rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ eval]. reflexivity.
    Qed.

    Lemma area_aligned a0 : ltac2:(tb__ "0|0|
Se1S69Va0;S70Vs;A1A3S3S0S61S100VL;Va0;A2Z1000A2Z0A3F_;").
    Proof using HI HMI.
      clear HsmK ZC MC VC. intros Ha. pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a0 Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
      pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
      subst a0. unfold zA, addr_of, loc_addr. cbn [padd prid poff]. clear - Hoo RA. unfold PGSZ in *. Z.to_euclidean_division_equations; lia.
    Qed.
    Lemma tail_range T : ltac2:(tb__ "0|3|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S4S3SeS0S0A2S28VrhoC;Sa7A2SaS0S0S5cS100VL;VT;A2M0Z8M1A2S5cG0Z10A2A4A3S4Se1S69VT;S70Vs;A1A3S4S5bZ1000M2G0A2S4S5bS5cG0G2A2S96VL;A1A2S3S0S61G0G1A2Z0A3A2A2A2A2F_;").
    Proof using HI HMI Hav Hev Hgd VC mW.
      clear HsmK ZC MC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
      assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
      assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
      assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
      pose proof (area_R T HinT) as (RT1 & RT2 & RT3 & _). top_ranges. pose proof (area_aligned T HinT) as AL.
      split; [|split; [exact HinT|split; [exact RT1|split; [exact RT2|clear - AL; Z.to_euclidean_division_equations; lia]]]].
      unfold obj_range, obj_lo_of, obj_hi_of, O_tail. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ]. rewrite u64 by lia. reflexivity.
    Qed.

    Lemma enter_next T : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S2bS1bS18bSa4S1bSa2Sb5A3SaScSe6A1Sf9Vtr;SfaVmsK;Sd5A2A4A4F_;").
    Proof using Erd Ewok HI HMI Hac Hav Hev Hgd HsmK Htp MC STK VC ZC.
      pose proof HsmK as SMC. pose proof (hold_tailK T) as HTK. pose proof hold_pageK as HPK. clear HsmK ZC. intros HT. pose proof (tail_range T HT) as (RT & HinT & T1 & T2 & T3).
      pose proof pz_facts as (P1 & P2 & P3 & P4).
      unfold rhoE. apply (entails_sound segsU srcN _ subC rhoC _ entN).
      unfold srcN. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [| |vm_compute; reflexivity].
      - apply (smatch_extend_objs segsU rhoC LC tr msK md2 [pageK; O_tail] (ss_next LC) SMC swfN).
        + constructor; [apply HPK | constructor; [exact (HTK HT) | constructor]].
        + constructor; [|constructor; [|constructor]]; apply Forall_forall; intros o' Ho'.
          * rewrite pageK_range. pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
          *
            rewrite RT. pose proof LC_misc as (_ & _ & _ & EO & _). rewrite EO in Ho'. pose proof (in_map (obj_range rhoC) _ _ Ho') as RO. rewrite (L78_ranges rhoC VC) in RO.
            pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
            assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
            destruct (A_fp_where (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as [[E _]|(pp & _ & _ & NI)]; [discriminate|].
            cbn [mc_img_lo mc_img_hi C_U] in NI. clear - RO S2 T1 T2 NI. top_ranges.
            unfold SymState.ranges_disjoint. cbn [fst snd].
            destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|].
            repeat (destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|]). destruct RO.
        + cbn. split; [constructor; [|constructor]|split; [constructor|exact I]].
          rewrite pageK_range, RT. unfold SymState.ranges_disjoint. cbn [fst snd].
          assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
          pose proof (A_page_vs_footprint (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as NG. unfold PGSZ in NG. cbn [fst snd] in NG.
          pose proof (area_aligned T HinT) as AT. clear - NG AT P1. unfold U.Mal_ameta__G1.Mal_ameta_I.zA, addr_of in *. Z.to_euclidean_division_equations; lia.
      - pose proof (evC rhoC (v 186) VC eq_refl) as E186. rewrite ev186, HT in E186. cbn [optrZ] in E186. change (v 186) with (SVar 186) in E186. cbn [eval] in E186.
        assert (U186 : bv_unsigned (Z_to_bv 64 (zA T)) = zA T) by (apply u64; clear - T1 T2; top_ranges; lia).
        clear MC.
        unfold nz_fact. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds eval v]; rewrite ?E186, ?U186.
        + unfold branch_taken, bv_eqb. rewrite ?U186. change (bv_unsigned (Z_to_bv 64 0)) with 0. replace (zA T =? 0) with false by (symmetry; apply Z.eqb_neq; clear - T1; lia). discriminate.
        + split; [clear; lia|]. change (2 ^ 3) with 8. exact T3.
        + change (bv_unsigned (Z_to_bv 64 (2 ^ 47))) with (2 ^ 47). clear - T2. top_ranges. lia.
        + change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact T1.
    Qed.
  End AtCut.

  Local Abbreviation W183 := (st_avail_meta_area_count s).
  Local Abbreviation W184 := (st_meta_alloc_shift s).
  Local Abbreviation VALF := (U.Mal_ameta__G2.Mal_ameta_C2E.valF s L rho gd evb avb mW A_pz W183 W184 brkZ).
  Definition GRa (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S5bS123Vs;VL;A2M0Vx;A2S5dVx;S5cG0Z1000A2A2A2").

  Lemma valF_enter rhoC : ltac2:(tb__ "0|0|
Sd3VrhoC;A1S18aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;S123Vs;VL;A2S6bVs;A1S78Vs;A1S101Vs;VL;A2S17fVrhoC;Sd7A2AcF_;").
  Proof using HI Hac Hav Hev Hgd Hinit.
    intros VC. pose proof VC as (A1 & A2 & A3). pose proof LC_misc as (_ & _ & E9 & _ & SUBOK).
    assert (LOW : forall j, (Z.pos j < 200) -> rw (rho_sub rhoC subC) j = rw rhoC j).
    { intros j Hj. cbn [rho_sub rw]. rewrite (wsub_get_low subC 200 j); [reflexivity | | exact Hj].
      exact SUBOK. }
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - intros j Hj. rewrite LOW by lia. rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
    - intros j Hj. cbn in Hj.
      assert (Hj' : (Z.pos j < 200)) by (repeat (destruct Hj as [<-|Hj]; [reflexivity|]); destruct Hj).
      rewrite (LOW j Hj'). rewrite <- (A1 j) by (unfold AM_NEXT; lia). reflexivity.
    -   rewrite LOW by lia. rewrite <- (A1 175%positive) by (unfold AM_NEXT; lia). transitivity (Z_to_bv 64 secZ); [exact (rw1_v 175 _ eq_refl) | unfold U.Mal_ameta__G1.Mal_ameta_I.secZ; rewrite Hinit; reflexivity].
    - unfold rho_sub. cbn [rw]. change (wsub_get subC 201) with (reg_sv LC 9). rewrite E9. exact (evC177 rhoC VC).
    - rewrite LOW by lia. rewrite <- (A1 183%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. exact (rw1_v 183 _ eq_refl).
    - rewrite LOW by lia. rewrite <- (A1 184%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. exact (rw1_v 184 _ eq_refl).
    - rewrite LOW by lia. rewrite <- (A1 187%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. exact (rw1_v 187 _ eq_refl).
    - intros l. unfold rho_sub. cbn [rl]. rewrite <- A2. reflexivity.
  Qed.

  Lemma R_HF : ltac2:(tb__ "0|6|
S4S3ScS69A1S70S124Vs;A1M0A1S11S69S70Vs;A1S9S69S126Vs;A1M1S10S69A1A3A3A3S4S3SdS6eG0A1SfA3S4S3SbS69A1M2S6cG0A1S14S69A1A3S4S3S69S8cG0A1S75S125Vs;A1S89A2A3S4S3S0S71G0A1S63S88Z1M3A2A3S4S3S0S6bG0A1S63S6bVs;A1G3A2A3S4S3S0S78G0A1S78Vs;A1A3S4S3G2S86G0A1G2G2Lx;S86Vs;A1S69S12S69R1A2Ls0;S12S69G1A2M4Xbx2A3S4S3G2S6dG0A1G4A3S4S3S69S8dG0A1S75G1Z1000A2A3S4S3ScG2A1S76G0A1S76Vs;A1A3S4S3ScS0A1M5S7dG0A1S7dVs;A1A3S4S3G5S7cG0A1S7cVs;A1A3S4S3G5S77G0A1S77Vs;A1A3S4S3S0S7bG0A1S7bVs;A1A3S3S0S79G0A1S79Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using HI HMI HXr Hac Hcnt Hhd Hinit. pose proof A_tA_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). repeat split; assumption. Qed.
  Lemma R_brk2 : ltac2:(tb__ "0|0|
S3S0S14dVL;S189S124Vs;A1A1A2S101Vs;VL;A2A3").
  Proof using HI HMI HXr Hac Hcnt Hhd Hinit.
    unfold U.Mal_ameta__G2.Mal_ameta_C2E.brk_sval, U.Mal_ameta__G1.Mal_ameta_I.brkZ. pose proof A_tA_fields as (_ & _ & _ & F4 & _). rewrite F4.
    destruct (st_brk s); reflexivity.
  Qed.
  Lemma R_V183 : 1 <= W183 < 2 ^ 62. Proof using HI HMI Hac Hav Hev Hgd. pose proof acount_range. lia. Qed.
  Lemma R_V184 : 0 <= W184 < 2 ^ 62. Proof using HMI Hav Hev Hgd. pose proof HB as (_ & SH & _). lia. Qed.
  Lemma R_mnew : ltac2:(tb__ "0|0|
S3S69S125Vs;A1S75S126Vs;A1Z18A2A3"). Proof using . reflexivity. Qed.
  Lemma R_Lext : ltac2:(tb__ "0|0|
Sf8VL;VL;S19S6aS7aVs;A1A2A3"). Proof using . apply layout_extends_refl. Qed.
  Lemma R_Lctx : ltac2:(tb__ "0|1|
S3S0S144VL;A1M0G0A3"). Proof using . reflexivity. Qed.
  Lemma R_Lsec : ltac2:(tb__ "0|1|
S3S0S149VL;A1M0G0A3"). Proof using . reflexivity. Qed.
  Lemma R_Lfp : ltac2:(tb__ "0|2|
SeS13aS0A2M0Se1G0R1S13dVs;A1A3S3S0S13cVL;S13S13aS0R2A3A2M1G1A3F_;Fe;"). Proof using . reflexivity. Qed.
  Lemma R_Lub : ltac2:(tb__ "0|2|
SeS69S0A2M0Se1G0R1S14eVs;A1A3S3S0S13cVL;S145S13S69S0R2A3A1A2M1G1A3F_;Fb;"). Proof using . reflexivity. Qed.
  Lemma R_Lold : ltac2:(tb__ "0|1|
S69S154S8bR1A1S19S6aS7aVs;A1A2A2S3S0S9fVL;R2A2M0G0A3F_;Fq;"). Proof using . reflexivity. Qed.
  Lemma R_pzR : ltac2:(tb__ "0|3|
S4S5bZ1000M0S123Vs;VL;A2M1A2S4S5bS5cG1G0A2S96VL;A1A2S4S3S0S61G1G0A2Z0M2A3S4S5bG2G1A2S5dG1S5eZ2Z40A2A2A2A2A2A2").
  Proof using HI HMI Hac Hav Hev Hgd. pose proof pz_facts as (P1 & P2 & P3 & P4). repeat split; lia. Qed.
  Lemma R_cw2 c x : ltac2:(tb__ "0|5|
Se1S13bVc;S11S13bS13eS124Vs;A1M0A1S15eG0A1A3A3S4S5bS13cVL;S14aVc;A1A2M1Vx;A2S5dVx;S5cG1S5fS14bVc;A1A1A2A2A2S7S6SeS13aS0A2M2G2S4Se1G2R1S13dVs;A1A3S4S5bS13cVL;S13S13aS0R1A3A2M3Vx;A2S5dVx;S5cG3S16S13aS0R1A3A2A2A2A2Le;A2S4S5bS123Vs;VL;A2M4Vx;A2S5dVx;S5cG4Z1000A2A2A2A2F_;F_;").
  Proof using HI HMI HXr Hac Hav Hcnt Hev Hgd Hhd Hinit. intros Hc Hx. destruct (A_cell_whereA c x Hc Hx) as [H|H]; [left; exact H | right; unfold PGSZ in H; lia]. Qed.
  Lemma R_GRdec x : ltac2:(tb__ "0|1|
S16eSd4Vx;A1M0S5G0A1A2"). Proof using . unfold GRa. apply range_dec. Qed.
  Lemma R_GRpage x : ltac2:(tb__ "0|1|
S4S5bS123Vs;VL;A2M0Vx;A2S5dVx;S5cG0Z1000A2A2A2Sd4Vx;A1F_;"). Proof using . intros H. exact H. Qed.
  Lemma R_GRimg x : ltac2:(tb__ "0|0|
Sd4Vx;A1S5S4S5bSa1S94A1Vx;A2S5dVx;Sa0S94A1A2A2A1F_;").
  Proof using HI HMI Hac. intros G Hi. apply (A_page_vs_image x Hi). unfold PGSZ. exact G. Qed.
  Lemma R_GRfp e x : ltac2:(tb__ "0|1|
Se1SeS13aS0A2Ve;S13dVs;A1A3S4S5bS13cVL;S13S13aS0Ve;A3A2M0Vx;A2S5dVx;S5cG0S16S13aS0Ve;A3A2A2A2S5Sd4Vx;A1A1F_;F_;").
  Proof using HI HMI Hac. intros He Hx G. apply (A_page_vs_footprint e x He Hx). unfold PGSZ. exact G. Qed.
  Lemma R_GRceil x : ltac2:(tb__ "0|0|
Sd4Vx;A1S4S5bZ1000Vx;A2S5dVx;S96VL;A1A2A2F_;").
  Proof using HI HMI Hac Hav Hev Hgd. pose proof pz_facts as (P1 & P2 & P3 & P4). unfold GRa. intros G. lia. Qed.
  Lemma R_GRmaps k rg x : ltac2:(tb__ "0|1|
S3SbS6aA1S13fVs;Vk;A2S12S6aVrg;A2A3S3SdS84Vrg;A1SfA3S3S85S82Vrg;A1S80A3S4S5bS142VL;Vk;A2M0Vx;A2S5dVx;S5cG0S83Vrg;A1A2A2A2S5Sd4Vx;A1A1F_;F_;F_;F_;").
  Proof using HI HMI Hac. intros Hk Hl Hkd Hx G. apply (A_map_region_vs_page k rg x Hk Hl Hkd Hx). unfold PGSZ. exact G. Qed.
  Lemma R_GRblock b n x : ltac2:(tb__ "0|0|
Se1SeS0S0A2SaS0S0Vb;Vn;A4S98VL;Vs;A2A3S4S5bVb;Vx;A2S5dVx;S5cVb;Vn;A2A2A2S5Sd4Vx;A1A1F_;F_;").
  Proof using HI HMI HXr Hac. intros Hin Hx G. apply (A_page_vs_block b n x Hin Hx). unfold PGSZ. exact G. Qed.
  Lemma R_notX : ltac2:(tb__ "0|1|
S4S3SdS14cS125Vs;A1M0VX;A2S17A3Se1S69G0S141S124Vs;A1A1A3A2"). Proof using HI HMI HXr Hac Hcnt Hhd Hinit. pose proof A_am_notX as (A & B & _). auto. Qed.
  Lemma R_Y : ltac2:(tb__ "0|2|
S140SeSbS69A1M0S6fA2S74Vs;A1S9SeS81S0A2M1SaS81S0S8fS184Vs;A1A1Z1A4S10G1A1A3SaG0S6fS12S69S125Vs;A1A2S124Vs;A1A4A4").
  Proof using Hac Hcnt Hhd. pose proof (yields_AR s Hhd Hcnt Hac 1) as Y. cbn [Z.eqb] in Y. exact Y. Qed.

  Local Ltac c2e_args tac :=
    tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_sound s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
           Kc ok md2 A_vmA HOK K2 vm2_eq STK (smatch_facts_hold segsU _ _ _ Hsm_pre) A_tA L A_ap A_am A_pz W183 W184 brkZ [(KMprotect (ar_p s), 1)]
           A_HIA A_xraw_tA A_layout_ok_tA A_vm_ok_tA (proj1 A_ledger_tA) (proj2 (proj2 A_ledger_tA)) A_bounded_tA A_maps_wf_tA
           R_HF R_brk2 R_V183 R_V184 A_image_tA A_ctx_cells_tAC A_area_cells_tA A_fresh_slot A_ap_fresh R_mnew A_fp_tA A_ub_tA
           R_Lext R_Lctx R_Lsec R_Lfp R_Lub R_Lold A_pz_eq A_am_addr R_pzR R_cw2
           GRa R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock A_block_where A_fp_where
           R_notX A_keys_tA A_am_frame_tA R_Y).

  Theorem okc_sound : ltac2:(tb__ "0|0|
S15S109S32S10bS1bVok;R3S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw';A4Sd3R2A1Sd9S26R3A1A1SdbS26R4A1A1S156S1bS157SffVtr;Sd5A2A1Sa4S1bSa2SabA3R5R6A5S10cS1bVok;R8R7A4F_;F_;F_;F_;F_;FrhoZ;Fw;Fn;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp STK.
    intros n w rhoZ HQ VZ MZ ZZ Hw.
    pose proof (alloc_meta_run_P A78_area_ok ok (Kexact tr md2) rhoZ (ok_frame_exact ok Kc tr md2 HOK K2)) as RUN1.
    refine (RUN1 n _ w Hw).
    intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC' & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_area_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area_ok) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagC.
    pose proof (valC_ext rhoZ rhoC AM_NEXT VZ ltac:(lia) HagC) as VC.
    assert (MC : memC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
    assert (ZC : zeroC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
    pose proof (valF_enter rhoC VC) as VE.
    assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2) ->
                 Safety.safe segsU ok n (tr, mkCfg ms1 md2)).
    { intros HE. c2e_args ltac:(fun t => apply (t n ms1 (rho_sub rhoC subC) HQ VE)); [| |exact HE].
      - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
      - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
    apply GO. unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
    - exact (enter_next ms1 rhoC VC MC ZC HsmC' T HT).
    - exact (enter_first ms1 rhoC VC ZC HsmC' HT).
  Qed.

  Local Ltac c2e_ex_args tac :=
    tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_ex s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
           Kc md2 A_vmA K2x vm2_eq STK (smatch_facts_hold segsU _ _ _ Hsm_pre) A_tA L A_ap A_am A_pz W183 W184 brkZ [(KMprotect (ar_p s), 1)]
           A_HIA A_xraw_tA A_layout_ok_tA A_vm_ok_tA (proj1 A_ledger_tA) (proj2 (proj2 A_ledger_tA)) A_bounded_tA A_maps_wf_tA
           R_HF R_brk2 R_V183 R_V184 A_image_tA A_ctx_cells_tAC A_area_cells_tA A_fresh_slot A_ap_fresh R_mnew A_fp_tA A_ub_tA
           R_Lext R_Lctx R_Lsec R_Lfp R_Lub R_Lold A_pz_eq A_am_addr R_pzR R_cw2
           GRa R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock A_block_where A_fp_where
           R_notX A_keys_tA A_am_frame_tA R_Y).

  Theorem okc_ex : ltac2:(tb__ "0|1|
S109S32Sd3R1A1Sd9S26R2A1A1SdbS26R3A1A1S156S1bS157SffVtr;Sd5A2A1Sa4S1bSa2SabA3R4R5A5S10aS1bS109S3S109R1R7A3Lw';S109S4S11cS1bS1cVrho;S9SeS31S11dA2M0SaS31S11dS137Sf2A1S135S1bS94VX;VR;VU;Sf5Vs;VL;A2VKc;A7A4S10G0A1A3R1A5S3Se7SfbS10eR1A1A1Sd5A3A2Lw';A3F_;F_;F_;F_;FrhoZ;Fw;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp STK.
    intros w rhoZ VZ MZ ZZ Hw w0 ->.
    destruct (alloc_meta_run_ex_P A78_area_ok (Kexact tr md2) rhoZ w Hw)
      as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoC & HinL & HagC & HsmC' & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_area_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area_ok) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagC.
    pose proof (valC_ext rhoZ rhoC AM_NEXT VZ ltac:(lia) HagC) as VC.
    assert (MC : memC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
    assert (ZC : zeroC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
    pose proof (valF_enter rhoC VC) as VE.
    assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2) ->
                 etriple segsU (fun w' => w' = (tr, mkCfg ms1 md2))
                   (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2)).
    { intros HE. c2e_ex_args ltac:(fun t => apply (t ms1 (rho_sub rhoC subC) VE)); [| |exact HE].
      - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
      - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
    assert (HE : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2)).
    { unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
      - exact (enter_next ms1 rhoC VC MC ZC HsmC' T HT).
      - exact (enter_first ms1 rhoC VC ZC HsmC' HT). }
    destruct (GO HE (tr, mkCfg ms1 md2) eq_refl) as (w3 & ST3 & HQ3).
    exists w3. split; [eapply wsteps_trans; [exact ST1 | exact ST3] | exact HQ3].
  Qed.

  Theorem cut78a_sound : ltac2:(tb__ "0|0|
S15S10bS1bVok;R1S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw;A4S10cS1bVok;R2SaScSe6A1Sf9Vtr;SfaVmsC;Vmd;A2A4A4F_;Fn;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC Hsm_pre Htop Htp STK bv0.
    intros n HQ.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof pz_facts as (P1 & P2 & P3 & P4).
    pose proof (alloc_meta_run_P A78_area ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1]] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_area) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    destruct n as [|m]; [exact I|].
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    pose proof (evC177 rhoL VL) as E177.
    refine (triple1_mprotect_exposeJ segsU ok (liftK (Kexact tr md)) (liftK (Kexact tr md)) (liftK (Kexact tr md2))
              L78 rhoL (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) L78_ecall M17 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      rewrite M10, E177 in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
      pose proof (L78_objs_miss rhoL VL) as MISS. pose proof ro_addr_page as ROG. pose proof page_noaccess_mc as PNA. pose proof page_maps_mc as PMA.
      clear Hsp HsmL RUN1 HQ ELF EP.
      rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
      assert (U1 : bv_unsigned (Z_to_bv 64 A_pz) = A_pz) by (apply u64; exact P4).
      assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
      rewrite ?U1, ?U2, ?U3.
      split; [reflexivity|]. split; [unfold page_size; exact P1|].
      split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
      split; [unfold two_pow_64; clear - P3; top_ranges; lia|].
      split; [exact PNA|]. split; [exact PMA|].
      split; [split; reflexivity|].
      intros _. split; [exact MISS|]. split; [intros x Hx; apply ROG; exact Hx|].
      split; reflexivity.
    -
      intros w2 [HF2 | HO2].
      +
        change (SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2) in HF2. rewrite <- Pre_fail_eq in HF2.
        pose proof (alloc_meta_run_P A78_area_fail ok (Kexact tr md) rhoL (ok_frame_exact ok Kc tr md HOK HKc)) as RUN2.
        refine (RUN2 m _ w2 HF2).
        intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
        destruct (Posts_am_P_shape A78_area_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
        assert (ELF3 : lf_state L3 = LRF) by (unfold LRF; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
        apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HQ.
        assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area_fail) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in Hag3.
        exact (post_null ms3 rhoF (agree_below_trans AM_NEXT _ _ _ HagL Hag3) Hsm3).
      +
        rewrite M10, M11, E177 in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. rewrite <- Pre_ok_eq in HO2.
        refine (okc_sound m w2 _ _ _ _ _ HO2).
        * exact (@Safety.guards_mono segsU ok (S m) m _ (Nat.le_succ_diag_r m) HQ).
        * destruct HagL as (A1 & A2 & A3). split; [|split; [exact A2 | intros x; reflexivity]].
          intros i Hi. cbn [set_rm rw rm rho1]. rewrite <- (A1 i Hi). reflexivity.
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          destruct (SysStep.in_range (Z_to_bv 64 A_pz) (Z_to_bv 64 4096) x) eqn:E.
          -- exfalso. apply in_range_spec in E. rewrite (u64 A_pz P4) in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. exact (Hx E).
          -- destruct HagL as (_ & _ & M). rewrite <- (M x). reflexivity.
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          replace (SysStep.in_range (Z_to_bv 64 A_pz) (Z_to_bv 64 4096) x) with true; [reflexivity|].
          symmetry. apply in_range_spec. rewrite (u64 A_pz P4). change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
  Qed.

  Theorem cut78a_ex : ltac2:(tb__ "0|0|
S10aS1bS109S3S109R1SaScSe6A1Sf9Vtr;SfaVmsC;Vmd;A2A4A3Lw;S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw;A3").
  Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac Hav Hav_rd Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC Hsm_pre Htop Htp STK bv0.
    intros w ->. pose proof pz_facts as (P1 & P2 & P3 & P4).
    destruct (alloc_meta_run_ex_P A78_area (Kexact tr md) (rho1 mW) (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl)))
      as ([tr1 [ms1 md1]] & ST1 & Lf & rhoL & HinL & HagL & HsmL & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_area) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    pose proof (evC177 rhoL VL) as E177. pose proof page_noaccess_mc as PNA. pose proof page_maps_mc as PMA.
    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) L78 rhoL)
                    (fun w2 => SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2
                               \/ SPJ segsU (liftK (Kexact tr md2)) (S_ret_lit L78 0)
                                    (set_rm rhoL (zero_range (rm rhoL) (eval rhoL (reg_sv L78 10)) (mmap_n (eval rhoL (reg_sv L78 11))))) w2)).
    { apply (HeapEx.etriple_mprotect_expose_anyJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md)) (liftK (Kexact tr md2)) L78 rhoL L78_ecall M17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      rewrite M10, E177 in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
      pose proof (L78_objs_miss rhoL VL) as MISS. pose proof ro_addr_page as ROG.
      clear Hsp HsmL. rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
      assert (U1 : bv_unsigned (Z_to_bv 64 A_pz) = A_pz) by (apply u64; exact P4).
      assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
      rewrite ?U1, ?U2, ?U3.
      split; [reflexivity|]. split; [unfold page_size; exact P1|].
      split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
      split; [unfold two_pow_64; clear - P3; top_ranges; lia|].
      split; [exact PNA|]. split; [exact PMA|]. split; [intros _; split; reflexivity|].
      intros _. split; [exact MISS|]. split; [intros x Hx; apply ROG; exact Hx|]. split; reflexivity. }
    destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as (w2 & ST2' & [HF2 | HO2]).
    -
      change (SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2) in HF2. rewrite <- Pre_fail_eq in HF2.
      destruct (alloc_meta_run_ex_P A78_area_fail (Kexact tr md) rhoL w2 HF2) as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
      destruct (Posts_am_P_shape A78_area_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
      assert (ELF3 : lf_state L3 = LRF) by (unfold LRF; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area_fail) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in Hag3.
      exists (tr, mkCfg ms3 md). split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
      exact (post_null ms3 rhoF (agree_below_trans AM_NEXT _ _ _ HagL Hag3) Hsm3).
    -
      rewrite M10, M11, E177 in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. rewrite <- Pre_ok_eq in HO2.
      unshelve (epose proof (okc_ex w2 _ _ _ _ HO2 w2 eq_refl) as OK3).
      + destruct HagL as (A1 & A2 & A3). split; [|split; [exact A2 | intros x; reflexivity]].
        intros i Hi. cbn [set_rm rw rm rho1]. rewrite <- (A1 i Hi). reflexivity.
      + intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        destruct (SysStep.in_range (Z_to_bv 64 A_pz) (Z_to_bv 64 4096) x) eqn:E.
        * exfalso. apply in_range_spec in E. rewrite (u64 A_pz P4) in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. exact (Hx E).
        * destruct HagL as (_ & _ & M). rewrite <- (M x). reflexivity.
      + intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        replace (SysStep.in_range (Z_to_bv 64 A_pz) (Z_to_bv 64 4096) x) with true; [reflexivity|].
        symmetry. apply in_range_spec. rewrite (u64 A_pz P4). change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
      + destruct OK3 as (w3 & ST3 & HQ3 & _). exists w3. split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
        destruct HQ3 as (Lq & JLq & rho' & Hin0 & Hrest). destruct Hin0 as [E0|[]].
        exists Lq, JLq, rho'. split; [right; left; exact E0 | exact Hrest].
  Qed.
End Cut78a.

Section EntryAR.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SbS69A1S6cVs;A1S14S69A1A3").
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : 0 < st_avail_meta_area_count s.
  Hypothesis Hinit : st_init_done s = true.

  Definition N_AR : list sobj := ltac2:(tb__ "0|1|
S9S20Sb0Sa2A1S9S20Sb1S9S20SacSa2A1S9S20Sb2Sa2A1S9S20SafS9S20Sb3Sa2Sa3PafA1Z1A3S9S20SaeSa2S23Z0A1M0Sa3Pb0A1G0Sa3Pb7A1Sa3Pb8A1Sa3Pb9A1Sa3PbaA1Sa3Pb1A1A9S9S20SadSa2Sa3PbbA1A2S10S20A1A3A3A3A3A3A3A3A3").
  Definition R_AR : list (Z * Z) := ltac2:(tb__ "0|1|
S9SeS0S0A2M0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3").

  Lemma N_AR_ranges : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S18cA4S18dA3").
  Proof using Hav Hev Hgd Htp.
    cbn [map N_AR R_AR]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    unfold R_AR. reflexivity.
  Qed.

  Lemma N_AR_hold : ltac2:(tb__ "0|0|
S12cS20S2fS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2A3S18cA3").
  Proof using Erd Ewok HMI Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Htp.
    unfold N_AR. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | apply ev183 | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor.
  Qed.

  Lemma acount_rangeE : ltac2:(tb__ "0|1|
S4S5bZ1S6bVs;A1M0A2S5dG0S5eZ2Z23A2A2A2").
  Proof using HI HMI Hac Hav Hev Hgd.
    pose proof (AllocMetaArea.res_facts X R U s L HI Hac HL vm HV) as (R1 & R2 & _ & R4 & _).
    pose proof (AllocMetaArea.ap_facts X R U s HI Hac) as (_ & _ & _ & _ & _ & _ & Hlen & _).
    top_ranges. unfold PGSZ in *. lia.
  Qed.
  Lemma AR_facts_hold : ltac2:(tb__ "0|0|
S12cS29S3cSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S11S29S9S29SbfPb7A1S10S29A1A3Sc2A3A3").
  Proof using HI HMI Hac Hav Hev Hgd Htp.
    pose proof acount_rangeE as AR. apply Forall_app. split; [|apply ctx_facts_hold].
    unfold nz_fact. constructor; [|constructor].
    apply holds1; [reflexivity|]. cbn [zholds zeval zcond v]. rewrite (zr1_var 183 _ eq_refl). zlit. rewrite Z.eqb_eq. lia.
  Qed.

  Theorem entry_AR : ltac2:(tb__ "0|0|
S2bS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sa4S1bSa2SbbA3SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_AR AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AR) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_AR_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_AR R_AR N_AR_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_AR. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_AR R_AR N_AR_ranges).
        cbn [pw R_AR]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AR)
                  ([nz_fact 183] ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_AR)
            (([nz_fact 183] ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply AR_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition ar_facts : list sprop := ltac2:(tb__ "0|0|
S11S29Sc0Pb1ZcA2S9S29S3bS25Pb7A1S23S5eZ2Z28A2A1A2S10S29A1A3A3").
  Lemma ar_facts_hold rhoX : ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoX;A3S12cS29S3cVrhoX;A1S18eA3F_;").
  Proof using HI HMI Hac Hav Hev Hgd.
    intros HagX.
    pose proof (AllocMetaArea.res_facts X R U s L HI Hac HL vm HV) as (_ & _ & _ & _ & _ & R6 & R7 & R8 & R9).
    pose proof (AllocMetaArea.ap_facts X R U s HI Hac) as (_ & _ & _ & _ & _ & _ & Hlen & _).
    pose proof (AllocMetaArea.res_facts X R U s L HI Hac HL vm HV) as (R1 & R2 & _ & R4 & _).
    top_ranges. unfold PGSZ in *.
    assert (EPZ : U.Mal_ameta__G1.Mal_ameta_I.areasZ s L = AllocMetaArea.pz s L).
    { unfold U.Mal_ameta__G1.Mal_ameta_I.areasZ. replace (st_avail_meta_area_count s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Bool.andb_false_r. rewrite <- (AllocMetaArea.pz_eq X R U s L HI Hac). unfold U.Mal_ameta__G1.Mal_ameta_I.zA, AllocMetaArea.ap, AllocMetaPost.ar_p, addr_of, loc_addr. destruct (st_avail_meta_areas s); reflexivity. }
    assert (E177 : bv_unsigned (eval rhoX (v 177)) = AllocMetaArea.pz s L).
    { rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoX (v 177) HagX eq_refl). rewrite ev177, EPZ. apply u64. lia. }
    assert (E183 : bv_unsigned (eval rhoX (SVar 183)) = st_avail_meta_area_count s).
    { rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoX (SVar 183) HagX eq_refl). change (SVar 183) with (v 183). rewrite ev183. apply u64. lia. }
    unfold ar_facts, ptr_facts. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds].
    - change (v 177) with (SVar 177%positive) in E177. cbn [eval] in E177. rewrite E177. split; [lia|]. change (2 ^ 12) with 4096. exact R6.
    - rewrite E177. change (bv_unsigned (eval rhoX (SLit (2 ^ 47)))) with (2 ^ 47). lia.
    - rewrite E177. change (bv_unsigned (eval rhoX (SLit 4096))) with 4096. lia.
    - rewrite E183. change (bv_unsigned (eval rhoX (SLit (2 ^ 40)))) with (2 ^ 40). lia.
  Qed.
End EntryAR.

Definition LAR0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2SbbA3S158A2Sa8SbbA1A3A1").
Definition LAR : sstate := ltac:(let x := eval vm_compute in LAR0 in exact x).
Lemma LAR_eq : LAR0 = LAR. Proof using . vm_cast_no_check (@eq_refl sstate LAR). Qed.
Definition subAR : list (positive * sv) := ltac2:(tb__ "0|1|
S9SeS1S21A2M0SaS1S21PccS22S11fZ1A2A4S9G0SaS1S21PcdS22S11fZ5A2A4S9G0SaS1S21PceS22S11fZ6A2A4S9G0SaS1S21PcfS22S11fZ7A2A4S9G0SaS1S21Pd1S22S11fZ9A2A4S9G0SaS1S21Pd3S22S11fZbA2A4S9G0SaS1S21Pd4S22S11fZcA2A4S9G0SaS1S21Pd5S22S11fZdA2A4S9G0SaS1S21Pd6S22S11fZeA2A4S9G0SaS1S21Pd7S22S11fZfA2A4S9G0SaS1S21Pd8S22S11fZ10A2A4S9G0SaS1S21Pd9S22S11fZ11A2A4S9G0SaS1S21PdcS22S11fZ14A2A4S9G0SaS1S21Pe4S22S11fZ1cA2A4S9G0SaS1S21Pe5S22S11fZ1dA2A4S9G0SaS1S21Pe6S22S11fZ1eA2A4S9G0SaS1S21Pe7S22S11fZ1fA2A4S10G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma entAR : ltac2:(tb__ "0|0|
S3SdS15dSa9S11fS11S29Sc0Pb1ZcA2S9S29S3bS25Pb7A1S23S5eZ2Z28A2A1A2S10S29A1A3A3A2Sa4S1bSa2Sb6A3S120A3SfA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LAR_misc : ltac2:(tb__ "0|1|
S4S3S1S2cS11fA1Sa5A3S3SdSe2SeS1S21A2M0G0S18S60Zc8S2S13S1S21R1A3A1A2S3fPaaS16S1S21R1A3A2A2Lp;S120A3SfA3A2").
Proof using . vm_compute. split; reflexivity. Qed.

End InstX.

Theorem am_AR_sound : ltac2:(tb__ "0|1|
S109OF_;ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S164S1bR7R2A3S3SbS69A1S6cSf6R4A1A1S14S69A1A3S3S0S71Sf6R5A1A1Z0M0A3S5dG0S6bSf6R6A1A1A2S3SdS6eSf6R7A1A1SfA3S10dS1bRcS156S1bS133S1bS94RbRaR9R8R7A7S132Sf2A1R6A4S11cS1bS1cR6S131S1bS94Sf2RbRaR9R8R7A8A4A4F_;F_;F_;F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK Hhd Hcnt Hac Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_AR s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit) as ENTRY.
  pose proof (alloc_meta_run_P AE_area ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n); [|split; [exact ENTRY | split; reflexivity]].
  intros [tr' [msC md']] (Lf & rhoL & HinL & HagL & HsmL & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
  destruct (Posts_am_P_shape AE_area) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LAR) by (rewrite <- LAR_eq; unfold LAR0; rewrite EP; reflexivity). rewrite ELF in HsmL.
  assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_area) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
  pose proof LAR_misc as [LNX SUBOK].

  set (rhoX := rho_sub rhoL subAR).
  assert (HsmX : smatch segsU rhoX (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) (tr, mkCfg msC md)).
  { apply (entails_sound segsU (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LAR (ptr_facts 177 12 ++ [SPUle (SVar 183) (SLit (2 ^ 40))])) _ subAR rhoL _ entAR).
    apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmL | | rewrite LNX; vm_compute; reflexivity].
    exact (ar_facts_hold s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW Hac rhoL HagL). }
  assert (RXlow : forall j, (Z.pos j < 200) -> rw rhoX j = rw rhoL j).
  { intros j Hj. subst rhoX. cbn [rho_sub rw].
    rewrite (wsub_get_low subAR 200 j); [reflexivity | | exact Hj].
    apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) SUBOK p Hp) as Q. apply andb_prop in Q as [Q _]. exact Q. }
  destruct HagL as (AG1 & AG2 & AG3). unfold AM_NEXT in AG1.
  assert (RX1 : forall j z, rw1v s L gd evb avb j = Some z -> rw rhoX j = Z_to_bv 64 z).
  { intros j z E.
    assert (Hj : (Z.pos j < 200)).
    { unfold rw1v in E. clear - E.
      repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
    rewrite (RXlow j Hj), <- (AG1 j) by lia. exact (rw1_v s L rho gd evb avb mW j z E). }
  assert (EmX : mW = rm rhoX) by (subst rhoX; cbn [rho_sub rm]; apply FunctionalExtensionality.functional_extensionality; intros a; exact (AG3 a)).
  assert (AGX : forall k, agree_below k rhoX (rho1 s L rhoX gd evb avb mW)) by (intros k; apply rho1_self; [exact RX1 | symmetry; exact EmX]).
  assert (HsmC : smatch segsU (rho1 s L rhoX gd evb avb mW) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) (tr, mkCfg msC md)).
  { exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) _ (AGX _) HsmX). }
  assert (AG0 : agree_below NF rho rhoX).
  { split; [|split].
    - intros i Hi. unfold NF in Hi. rewrite (RXlow i) by lia. rewrite <- (AG1 i) by lia. cbn [rho1 rw]. symmetry. apply (rw1_low s L rho gd evb avb Hgd Hev Hav). lia.
    - intros l. subst rhoX. cbn [rho_sub rl]. rewrite <- (AG2 l). reflexivity.
    - intros a. rewrite <- EmX. reflexivity. }
  assert (Hsm_preX : smatch segsU rhoX (ContractAM.Pre_am IEC_U) (tr, mkCfg ms md)) by exact (smatch_agree segsU rho rhoX (ContractAM.Pre_am IEC_U) _ AG0 Hsm).
  assert (HtpX : rw rhoX 24%positive = Z_to_bv 64 (mc_tp C_U)) by (destruct AG0 as (A0 & _); rewrite <- (A0 24%positive) by (unfold NF; lia); exact Htp').
  assert (HtopX : top_high (mkMA s L) rhoX) by (unfold top_high; cbn [ma_L]; destruct AG0 as (A0 & _); rewrite <- (A0 10%positive) by (unfold NF; lia); rewrite <- (A0 V_DEPTH) by (unfold NF, V_DEPTH; lia); exact Htop).
  pose proof (stk_facts s L rhoX gd evb avb Hgd Hev Hav mW ms tr md EmX Hsm_preX HtopX) as STKX.
  assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [symmetry; exact EmX | exact (agree_below_vals _ _ _ AG0)]. }
  apply (cut78a_sound s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX Hsm_preX HtopX
           Hhd Hcnt Hac Hinit msC HsmC Kc HKc eq_refl ok HOK STKX n).
  intros w HL. apply HQ. exact (REB w HL).
Qed.

Theorem am_AR_ex : ltac2:(tb__ "0|1|
ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S167R2A1S3SbS69A1S6cSf6R4A1A1S14S69A1A3S3S0S71Sf6R5A1A1Z0M0A3S5dG0S6bSf6R6A1A1A2S3SdS6eSf6R7A1A1SfA3S10aS1bS156S1bS133S1bS94RbRaR9R8R7A7S132Sf2A1R6A4S11cS1bS1cR6S131S1bS94Sf2RbRaR9R8R7A8A4A3F_;F_;F_;F_;F_;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho HVI Hhd Hcnt Hac Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_AR s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit) as ENTRY.
  destruct (alloc_meta_run_ex_P AE_area (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msC md']] & ST0 & Lf & rhoL & HinL & HagL & HsmL & HK).
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
  destruct (Posts_am_P_shape AE_area) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LAR) by (rewrite <- LAR_eq; unfold LAR0; rewrite EP; reflexivity). rewrite ELF in HsmL.
  assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_area) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
  pose proof LAR_misc as [LNX SUBOK].

  set (rhoX := rho_sub rhoL subAR).
  assert (HsmX : smatch segsU rhoX (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) (tr, mkCfg msC md)).
  { apply (entails_sound segsU (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LAR (ptr_facts 177 12 ++ [SPUle (SVar 183) (SLit (2 ^ 40))])) _ subAR rhoL _ entAR).
    apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmL | | rewrite LNX; vm_compute; reflexivity].
    exact (ar_facts_hold s L X R U rho HI (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW Hac rhoL HagL). }
  assert (RXlow : forall j, (Z.pos j < 200) -> rw rhoX j = rw rhoL j).
  { intros j Hj. subst rhoX. cbn [rho_sub rw].
    rewrite (wsub_get_low subAR 200 j); [reflexivity | | exact Hj].
    apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) SUBOK p Hp) as Q. apply andb_prop in Q as [Q _]. exact Q. }
  destruct HagL as (AG1 & AG2 & AG3). unfold AM_NEXT in AG1.
  assert (RX1 : forall j z, rw1v s L gd evb avb j = Some z -> rw rhoX j = Z_to_bv 64 z).
  { intros j z E.
    assert (Hj : (Z.pos j < 200)).
    { unfold rw1v in E. clear - E.
      repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
    rewrite (RXlow j Hj), <- (AG1 j) by lia. exact (rw1_v s L rho gd evb avb mW j z E). }
  assert (EmX : mW = rm rhoX) by (subst rhoX; cbn [rho_sub rm]; apply FunctionalExtensionality.functional_extensionality; intros a; exact (AG3 a)).
  assert (AGX : forall k, agree_below k rhoX (rho1 s L rhoX gd evb avb mW)) by (intros k; apply rho1_self; [exact RX1 | symmetry; exact EmX]).
  assert (HsmC : smatch segsU (rho1 s L rhoX gd evb avb mW) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) (tr, mkCfg msC md)).
  { exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_area) _ (AGX _) HsmX). }
  assert (AG0 : agree_below NF rho rhoX).
  { split; [|split].
    - intros i Hi. unfold NF in Hi. rewrite (RXlow i) by lia. rewrite <- (AG1 i) by lia. cbn [rho1 rw]. symmetry. apply (rw1_low s L rho gd evb avb Hgd Hev Hav). lia.
    - intros l. subst rhoX. cbn [rho_sub rl]. rewrite <- (AG2 l). reflexivity.
    - intros a. rewrite <- EmX. reflexivity. }
  assert (Hsm_preX : smatch segsU rhoX (ContractAM.Pre_am IEC_U) (tr, mkCfg ms md)) by exact (smatch_agree segsU rho rhoX (ContractAM.Pre_am IEC_U) _ AG0 Hsm).
  assert (HtpX : rw rhoX 24%positive = Z_to_bv 64 (mc_tp C_U)) by (destruct AG0 as (A0 & _); rewrite <- (A0 24%positive) by (unfold NF; lia); exact Htp').
  assert (HtopX : top_high (mkMA s L) rhoX) by (unfold top_high; cbn [ma_L]; destruct AG0 as (A0 & _); rewrite <- (A0 10%positive) by (unfold NF; lia); rewrite <- (A0 V_DEPTH) by (unfold NF, V_DEPTH; lia); exact Htop).
  pose proof (stk_facts s L rhoX gd evb avb Hgd Hev Hav mW ms tr md EmX Hsm_preX HtopX) as STKX.
  assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [symmetry; exact EmX | exact (agree_below_vals _ _ _ AG0)]. }
  destruct (cut78a_ex s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX Hsm_preX HtopX
           Hhd Hcnt Hac Hinit msC HsmC Kc HKc eq_refl STKX HVI (tr, mkCfg msC md) eq_refl) as (w' & ST1 & HL).
  exists w'. split; [eapply wsteps_trans; [exact ST0 | exact ST1]|]. exact (REB w' HL).
Qed.
End Mal_ameta_AR.

Module Mal_ameta_NB.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := first [slia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; slia].
Local Ltac nia := first [snia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; snia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S143VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S16dS94VX;VR;VU;Sf5Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§10§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§10§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HB := (§10§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Abbreviation rw1v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb).
Local Abbreviation rho1 := (@U.Mal_ameta__G1.Mal_ameta_I.rho1 s L rho gd evb avb).
Local Notation "§11§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§11§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev184 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§11§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;Vrd0;Se4S1bVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S90Q40A1SdF_;Vwok0;Se5S1bVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S99S95Vrd0;S90Q40A1SfL_;A2S97S94A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S15S154R1U4A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9bS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vevb;S91G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S15S154R1U8A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9aS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vavb;S91G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bVmW;A2Se5S1bVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§12§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§12§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§12§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S90Q40M0A1S2dVrho;P18A2S91G0S9cS94A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Abbreviation hold_sec := (§12§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brkE := (§12§ U.Mal_ameta__G1.Mal_ameta_I.hold_brkE).
Local Abbreviation hold_ctxB := (§12§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Notation "§13§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation rng_stk := (§13§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§13§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2bS1bVrho;S132Sf2A1SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S166Sf5Vs;VL;A2Vrho;A2").
Local Notation "§14§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§14§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§14§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Abbreviation rw1_v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1_v s L rho gd evb avb mW).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).

Section EntryNB.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SbS69A1S6cVs;A1S14S69A1A3").
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : st_avail_meta_area_count s = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S3S72S73Vs;A1S7eA3").
  Hypothesis Hinit : st_init_done s = true.

  Definition N_NB : list sobj := ltac2:(tb__ "0|1|
S9S20Sb0Sa2A1S9S20Sb1S9S20SacSa2A1S9S20Sb2Sa2A1S9S20SafS9S20Sb3Sa2Sa3PafA1Z1A3S9S20SaeSa2S23Z0A1M0Sa3Pb0A1G0G0Sa3Pb8A1Sa3Pb9A1Sa3PbaA1Sa3Pb1A1A9S9S20SadSa2S23Sb8A1A2S10S20A1A3A3A3A3A3A3A3A3").
  Definition R_NB : list (Z * Z) := ltac2:(tb__ "0|1|
S9SeS0S0A2M0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3").

  Lemma N_NB_ranges : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S190A4S191A3").
  Proof using Hav Hev Hgd Htp.
    cbn [map N_NB R_NB]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    unfold R_NB. reflexivity.
  Qed.

  Lemma evM64 : ltac2:(tb__ "0|1|
S3S90Q40M0A1S30SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S23Sb8A1A2S91G0S101Vs;VL;A2A2A3").
  Proof using Hbrk. unfold brkZ. rewrite Hbrk. apply bv_eq. reflexivity. Qed.

  Lemma N_NB_hold : ltac2:(tb__ "0|0|
S12cS20S2fS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2A3S190A3").
  Proof using Erd Ewok HMI Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Htp.
    unfold N_NB. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brkE; apply evM64|]. constructor.
  Qed.

  Theorem entry_NB : ltac2:(tb__ "0|0|
S2bS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sa4S1bSa2SbdA3SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HMI Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_NB AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_NB) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_NB_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_NB R_NB N_NB_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_NB. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_NB R_NB N_NB_ranges).
        cbn [pw R_NB]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_NB)
                  ([] ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_NB)
            (([] ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - cbn [app]. apply ctx_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Lemma res_facts_hold rhoX : ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoX;A3S12cS29S3cVrhoX;A1Sc1A3F_;").
  Proof using HMI Hav Hev Hgd.
    intros HagX. pose proof HB as (_ & SH & _).
    pose proof (U.Mal_ameta__G2.Mal_ameta_R78.lenZ_range s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav) as [LR _].
    assert (E184 : bv_unsigned (eval rhoX (v 184)) = st_meta_alloc_shift s).
    { rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoX (v 184) HagX eq_refl). rewrite ev184. apply u64. lia. }
    assert (ELX : bv_unsigned (eval rhoX LENX) = U.Mal_ameta__G2.Mal_ameta_R78.lenZ s).
    { rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoX LENX HagX eq_refl). rewrite (U.Mal_ameta__G2.Mal_ameta_R78.LENX_val s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW). apply u64. lia. }
    unfold res_facts. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds].
    - rewrite E184. change (bv_unsigned (eval rhoX (SLit 34))) with 34. lia.
    - rewrite ELX. change (bv_unsigned (eval rhoX (SLit (2 ^ 48)))) with (2 ^ 48). lia.
    - rewrite ELX. change (bv_unsigned (eval rhoX (SLit 8192))) with 8192. lia.
  Qed.
End EntryNB.

Definition LNB0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2SbdA3S158A2Sa8SbdA1A3A1").
Definition LNB : sstate := ltac:(let x := eval vm_compute in LNB0 in exact x).
Lemma LNB_eq : LNB0 = LNB. Proof using . vm_cast_no_check (@eq_refl sstate LNB). Qed.
Definition subNB : list (positive * sv) := ltac2:(tb__ "0|1|
S9SeS1S21A2M0SaS1S21PccS22S121Z1A2A4S9G0SaS1S21PcdS22S121Z5A2A4S9G0SaS1S21PceS22S121Z6A2A4S9G0SaS1S21PcfS22S121Z7A2A4S9G0SaS1S21Pd1S22S121Z9A2A4S9G0SaS1S21Pd3S22S121ZbA2A4S9G0SaS1S21Pd4S22S121ZcA2A4S9G0SaS1S21Pd5S22S121ZdA2A4S9G0SaS1S21Pd6S22S121ZeA2A4S9G0SaS1S21Pd7S22S121ZfA2A4S9G0SaS1S21Pd8S22S121Z10A2A4S9G0SaS1S21Pd9S22S121Z11A2A4S9G0SaS1S21PdcS22S121Z14A2A4S9G0SaS1S21Pe4S22S121Z1cA2A4S9G0SaS1S21Pe5S22S121Z1dA2A4S9G0SaS1S21Pe6S22S121Z1eA2A4S9G0SaS1S21Pe7S22S121Z1fA2A4S10G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma entNB : ltac2:(tb__ "0|0|
S3SdS15dSa9S121Sc1A2Sa4S1bSa2SaaA3S122A3SfA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma LNB_misc : ltac2:(tb__ "0|1|
S4S3S1S2cS121A1Sa5A3S3SdSe2SeS1S21A2M0G0S18S60Zc8S2S13S1S21R1A3A1A2S3fPaaS16S1S21R1A3A2A2Lp;S122A3SfA3A2").
Proof using . vm_compute. split; reflexivity. Qed.

End InstX.

Theorem am_NB_sound : ltac2:(tb__ "0|1|
S109OF_;ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S164S1bR7R2A3S3SbS69A1S6cSf6R4A1A1S14S69A1A3S3S0S71Sf6R5A1A1Z0M0A3S3S0S6bSf6R6A1A1G0A3S3S72S73Sf6R7A1A1S7eA3S3SdS6eSf6R8A1A1SfA3S10dS1bRdS156S1bS133S1bS94RcRbRaR9R8A7S132Sf2A1R7A4S11cS1bS1cR7S131S1bS94Sf2RcRbRaR9R8A8A4A4F_;F_;F_;F_;F_;F_;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho HOK Hhd Hcnt Hac Hbrk Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_NB s L X R U rho (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hbrk Hinit) as ENTRY.
  pose proof (alloc_meta_run_P AE_nobrk ok (Kexact tr md) (rho1 s L rho gd evb avb mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN.
  apply (RUN n); [|split; [exact ENTRY | split; reflexivity]].
  intros [tr' [msC md']] (Lf & rhoL & HinL & HagL & HsmL & HK). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
  destruct (Posts_am_P_shape AE_nobrk) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LNB) by (rewrite <- LNB_eq; unfold LNB0; rewrite EP; reflexivity). rewrite ELF in HsmL.
  assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_nobrk) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
  pose proof LNB_misc as [LNX SUBOK].

  set (rhoX := rho_sub rhoL subNB).
  assert (HsmX : smatch segsU rhoX (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) (tr, mkCfg msC md)).
  { apply (entails_sound segsU (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LNB res_facts) _ subNB rhoL _ entNB).
    apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmL | | rewrite LNX; vm_compute; reflexivity].
    exact (res_facts_hold s L X R U rho (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW rhoL HagL). }
  assert (RXlow : forall j, (Z.pos j < 200) -> rw rhoX j = rw rhoL j).
  { intros j Hj. subst rhoX. cbn [rho_sub rw].
    rewrite (wsub_get_low subNB 200 j); [reflexivity | | exact Hj].
    apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) SUBOK p Hp) as Q. apply andb_prop in Q as [Q _]. exact Q. }
  destruct HagL as (AG1 & AG2 & AG3). unfold AM_NEXT in AG1.
  assert (RX1 : forall j z, rw1v s L gd evb avb j = Some z -> rw rhoX j = Z_to_bv 64 z).
  { intros j z E.
    assert (Hj : (Z.pos j < 200)).
    { unfold rw1v in E. clear - E.
      repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
    rewrite (RXlow j Hj), <- (AG1 j) by lia. exact (rw1_v s L rho gd evb avb mW j z E). }
  assert (EmX : mW = rm rhoX) by (subst rhoX; cbn [rho_sub rm]; apply FunctionalExtensionality.functional_extensionality; intros a; exact (AG3 a)).
  assert (AGX : forall k, agree_below k rhoX (rho1 s L rhoX gd evb avb mW)) by (intros k; apply rho1_self; [exact RX1 | symmetry; exact EmX]).
  assert (HsmC : smatch segsU (rho1 s L rhoX gd evb avb mW) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) (tr, mkCfg msC md)).
  { exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) _ (AGX _) HsmX). }
  assert (AG0 : agree_below NF rho rhoX).
  { split; [|split].
    - intros i Hi. unfold NF in Hi. rewrite (RXlow i) by lia. rewrite <- (AG1 i) by lia. cbn [rho1 rw]. symmetry. apply (rw1_low s L rho gd evb avb Hgd Hev Hav). lia.
    - intros l. subst rhoX. cbn [rho_sub rl]. rewrite <- (AG2 l). reflexivity.
    - intros a. rewrite <- EmX. reflexivity. }
  assert (Hsm_preX : smatch segsU rhoX (ContractAM.Pre_am IEC_U) (tr, mkCfg ms md)) by exact (smatch_agree segsU rho rhoX (ContractAM.Pre_am IEC_U) _ AG0 Hsm).
  assert (HtpX : rw rhoX 24%positive = Z_to_bv 64 (mc_tp C_U)) by (destruct AG0 as (A0 & _); rewrite <- (A0 24%positive) by (unfold NF; lia); exact Htp').
  assert (HtopX : top_high (mkMA s L) rhoX) by (unfold top_high; cbn [ma_L]; destruct AG0 as (A0 & _); rewrite <- (A0 10%positive) by (unfold NF; lia); rewrite <- (A0 V_DEPTH) by (unfold NF, V_DEPTH; lia); exact Htop).
  pose proof (stk_facts s L rhoX gd evb avb Hgd Hev Hav mW ms tr md EmX Hsm_preX HtopX) as STKX.
  pose proof (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI md eq_refl) as HIRX.
  assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [symmetry; exact EmX | exact (agree_below_vals _ _ _ AG0)]. }
  apply (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_sound s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX
           Hhd Hcnt Hac Hbrk Hinit msC HsmC Kc HKc eq_refl ok HOK HIRX STKX n).
  intros w [HL|HO].
  - apply HQ. exact (REB w HL).
  - refine (U.Mal_ameta__G4.Mal_ameta_R2E.resok_sound s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX
              Hhd Hcnt Hac Hbrk Hinit Kc HKc eq_refl ok HOK STKX (smatch_facts_hold segsU _ _ _ Hsm_preX) n _ w HO).
    intros w' HL'. apply HQ. exact (REB w' HL').
Qed.

Theorem am_NB_ex : ltac2:(tb__ "0|1|
ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S167R2A1S3SbS69A1S6cSf6R4A1A1S14S69A1A3S3S0S71Sf6R5A1A1Z0M0A3S3S0S6bSf6R6A1A1G0A3S3S72S73Sf6R7A1A1S7eA3S3SdS6eSf6R8A1A1SfA3S10aS1bS156S1bS133S1bS94RcRbRaR9R8A7S132Sf2A1R7A4S11cS1bS1cR7S131S1bS94Sf2RcRbRaR9R8A8A4A3F_;F_;F_;F_;F_;F_;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho HVI Hhd Hcnt Hac Hbrk Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.

  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (entry_NB s L X R U rho (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
                mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hbrk Hinit) as ENTRY.
  destruct (alloc_meta_run_ex_P AE_nobrk (Kexact tr md) (rho1 s L rho gd evb avb mW) (tr, mkCfg ms md) (conj ENTRY (conj eq_refl eq_refl)))
    as ([tr' [msC md']] & ST0 & Lf & rhoL & HinL & HagL & HsmL & HK).
  cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK. destruct HK as [-> ->].
  cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
  destruct (Posts_am_P_shape AE_nobrk) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
  assert (ELF : lf_state L0 = LNB) by (rewrite <- LNB_eq; unfold LNB0; rewrite EP; reflexivity). rewrite ELF in HsmL.
  assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_nobrk) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
  pose proof LNB_misc as [LNX SUBOK].

  set (rhoX := rho_sub rhoL subNB).
  assert (HsmX : smatch segsU rhoX (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) (tr, mkCfg msC md)).
  { apply (entails_sound segsU (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LNB res_facts) _ subNB rhoL _ entNB).
    apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmL | | rewrite LNX; vm_compute; reflexivity].
    exact (res_facts_hold s L X R U rho (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW rhoL HagL). }
  assert (RXlow : forall j, (Z.pos j < 200) -> rw rhoX j = rw rhoL j).
  { intros j Hj. subst rhoX. cbn [rho_sub rw].
    rewrite (wsub_get_low subNB 200 j); [reflexivity | | exact Hj].
    apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) SUBOK p Hp) as Q. apply andb_prop in Q as [Q _]. exact Q. }
  destruct HagL as (AG1 & AG2 & AG3). unfold AM_NEXT in AG1.
  assert (RX1 : forall j z, rw1v s L gd evb avb j = Some z -> rw rhoX j = Z_to_bv 64 z).
  { intros j z E.
    assert (Hj : (Z.pos j < 200)).
    { unfold rw1v in E. clear - E.
      repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
    rewrite (RXlow j Hj), <- (AG1 j) by lia. exact (rw1_v s L rho gd evb avb mW j z E). }
  assert (EmX : mW = rm rhoX) by (subst rhoX; cbn [rho_sub rm]; apply FunctionalExtensionality.functional_extensionality; intros a; exact (AG3 a)).
  assert (AGX : forall k, agree_below k rhoX (rho1 s L rhoX gd evb avb mW)) by (intros k; apply rho1_self; [exact RX1 | symmetry; exact EmX]).
  assert (HsmC : smatch segsU (rho1 s L rhoX gd evb avb mW) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) (tr, mkCfg msC md)).
  { exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) _ (AGX _) HsmX). }
  assert (AG0 : agree_below NF rho rhoX).
  { split; [|split].
    - intros i Hi. unfold NF in Hi. rewrite (RXlow i) by lia. rewrite <- (AG1 i) by lia. cbn [rho1 rw]. symmetry. apply (rw1_low s L rho gd evb avb Hgd Hev Hav). lia.
    - intros l. subst rhoX. cbn [rho_sub rl]. rewrite <- (AG2 l). reflexivity.
    - intros a. rewrite <- EmX. reflexivity. }
  assert (Hsm_preX : smatch segsU rhoX (ContractAM.Pre_am IEC_U) (tr, mkCfg ms md)) by exact (smatch_agree segsU rho rhoX (ContractAM.Pre_am IEC_U) _ AG0 Hsm).
  assert (HtpX : rw rhoX 24%positive = Z_to_bv 64 (mc_tp C_U)) by (destruct AG0 as (A0 & _); rewrite <- (A0 24%positive) by (unfold NF; lia); exact Htp').
  assert (HtopX : top_high (mkMA s L) rhoX) by (unfold top_high; cbn [ma_L]; destruct AG0 as (A0 & _); rewrite <- (A0 10%positive) by (unfold NF; lia); rewrite <- (A0 V_DEPTH) by (unfold NF, V_DEPTH; lia); exact Htop).
  pose proof (stk_facts s L rhoX gd evb avb Hgd Hev Hav mW ms tr md EmX Hsm_preX HtopX) as STKX.
  pose proof (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI md eq_refl) as HIRX.
  assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  { intros w. apply LQP_am_rebase; [symmetry; exact EmX | exact (agree_below_vals _ _ _ AG0)]. }
  destruct (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_anyex s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX
           Hhd Hcnt Hac Hbrk Hinit msC HsmC Kc HKc eq_refl HIRX STKX (tr, mkCfg msC md) eq_refl) as (w' & ST1 & [HL | HO]).
  - exists w'. split; [eapply wsteps_trans; [exact ST0 | exact ST1]|]. exact (REB w' HL).
  - destruct (U.Mal_ameta__G4.Mal_ameta_R2E.resok_anyex s L X R U rhoX HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav mW eq_refl eq_refl ms Hrom Hgd_rd Hav_rd HtpX tr md EmX
              Hhd Hcnt Hac Hbrk Hinit Kc HKc eq_refl HVI STKX (smatch_facts_hold segsU _ _ _ Hsm_preX) w' HO w' eq_refl) as (w'' & ST2 & HL').
    exists w''. split; [eapply wsteps_trans; [exact ST0 | eapply wsteps_trans; [exact ST1 | exact ST2]]|]. exact (REB w'' HL').
Qed.
End Mal_ameta_NB.

Module Mal_ameta_BK.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaArea OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G5.Mal_ameta_NB.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := first [slia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; slia].
Local Ltac nia := first [snia | OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.top_ranges; snia].

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
S143VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S16dS94VX;VR;VU;Sf5Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§15§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§15§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§15§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HMW := (§15§ U.Mal_ameta__G1.Mal_ameta_I.HMW).
Local Abbreviation HLG := (§15§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§15§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§15§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Abbreviation secZ := (@U.Mal_ameta__G1.Mal_ameta_I.secZ s L).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Abbreviation rw1v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1v s L gd evb avb).
Local Abbreviation rho1 := (@U.Mal_ameta__G1.Mal_ameta_I.rho1 s L rho gd evb avb).
Local Notation "§16§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§16§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev184 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Local Abbreviation ev187 := (§16§ U.Mal_ameta__G1.Mal_ameta_I.ev187).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;Vrd0;Se4S1bVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S90Q40A1SdF_;Vwok0;Se5S1bVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
S99S95Vrd0;S90Q40A1SfL_;A2S97S94A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S15S154R1U4A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9bS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vevb;S91G0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S15S154R1U8A2S3SbS90Q8M0A1M1A1Se4S1bVmW;S91Q40S5cS9aS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vavb;S91G0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bVmW;A2Se5S1bVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Abbreviation cell_rw0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_rw0 s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok).
Local Abbreviation cell_view0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_view0 s L X R U rho rd0 wok0 vm HMI gd evb avb mW Erd Ewok).
Local Notation "§17§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§17§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§17§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S90Q40M0A1S2dVrho;P18A2S91G0S9cS94A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_errno := (@U.Mal_ameta__G1.Mal_ameta_I.hold_errno s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hev_rd Htp).
Local Notation "§18§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW) (at level 10, h__ global).
Local Abbreviation B_ctx := (§18§ U.Mal_ameta__G1.Mal_ameta_I.B_ctx).
Local Abbreviation hold_sec := (§17§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brk := (§17§ U.Mal_ameta__G1.Mal_ameta_I.hold_brk).
Local Abbreviation hold_ctxB := (§17§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (§18§ U.Mal_ameta__G1.Mal_ameta_I.rng_stk).
Local Abbreviation rng_lit := (§18§ U.Mal_ameta__G1.Mal_ameta_I.rng_lit).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S90Q40A1SbS90Q8A1A1F_;VmW;S26Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2bS1bVrho;S132Sf2A1SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S166Sf5Vs;VL;A2Vrho;A2").
Local Notation "§19§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW ms tr md EmW Hsm_pre Htop) (at level 10, h__ global).
Local Abbreviation sm_pre1 := (§19§ U.Mal_ameta__G1.Mal_ameta_I.sm_pre1).
Local Abbreviation stk_facts := (§19§ U.Mal_ameta__G1.Mal_ameta_I.stk_facts).
Local Abbreviation pw := (@U.Mal_ameta__G1.Mal_ameta_I.pw).
Local Abbreviation pairwise_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.pairwise_of_ranges).
Local Abbreviation vs_stack_of_ranges := (@U.Mal_ameta__G1.Mal_ameta_I.vs_stack_of_ranges).
Local Abbreviation rw1_v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1_v s L rho gd evb avb mW).
Local Abbreviation ctx_facts_hold := (@U.Mal_ameta__G1.Mal_ameta_I.ctx_facts_hold s L rho gd evb avb Hgd Hev Hav mW Htp).
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Section RebaseState.
  Variables (t' : astate) (Kc : list event -> Model -> Prop) (rhoX : valuation).
  Hypothesis AGW : ltac2:(tb__ "0|0|
S1S15fR1S1cA2S3S90Q40A1S2dVrhoX;R2A2S2dVrho;R2A2A3F_;Fi;").
  Hypothesis AGL : ltac2:(tb__ "0|0|
S1S3ScS90Q8A1A1S3dVrhoX;R1A2S3dVrho;R1A2A3Fl;").
  Hypothesis MEMC : ltac2:(tb__ "0|1|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S165S1bS94Sf5Vs;VL;A2R2A4S5S169S94R3A2A1S5S168S94R4A2A1S3SbS90Q8A1A1S26VrhoX;S91Q40R5A2M0A2S26Vrho;G0A2A3F_;F_;F_;F_;Fa;").
  Hypothesis MEMM : ltac2:(tb__ "0|2|
S15S6aS0S3SbS6aA1S13fVs;R3A2S12S6aR2A2A3S3S85S82R3A1S80A3S3SdS84R4A1SfA3S4S5bS142VL;R6A2M0R4A2S5dR4S5cG0S83R5A1A2A2A2S3SbS90Q8A1A1S26VrhoX;S91Q40R5A2M1A2S26Vrho;G1A2A3F_;F_;F_;F_;Fa;Frg;Fk;").
  Hypothesis MEMG : ltac2:(tb__ "0|4|
S0S7S4S5bS9dS94A1M0R1A2S5dR1S5cG0Z8M1A2A2A2S4S5bS97S94A1M2R1A2S5dR1S5cG2G1A2A2A2A2S3SbS90Q8A1A1Se4S1bS26VrhoX;A1S91Q40R2A2M3A3Se4S1bS26Vrho;A1G3A3A3F_;Fa;").
  Hypothesis Einit : ltac2:(tb__ "0|0|
S3SdS6eVt';A1S6eVs;A1A3").
  Hypothesis Eact : ltac2:(tb__ "0|0|
S3ScSbS69A1A1S76Vt';A1S76Vs;A1A3").
  Hypothesis Eusage : ltac2:(tb__ "0|0|
S3ScS0A1S7dVt';A1S7dVs;A1A3").
  Hypothesis Ebnc : ltac2:(tb__ "0|0|
S3ScS0A1S77Vt';A1S77Vs;A1A3").
  Hypothesis Eunm : ltac2:(tb__ "0|0|
S3ScS0A1S7cVt';A1S7cVs;A1A3").
  Hypothesis Eseq : ltac2:(tb__ "0|0|
S3S0S7bVt';A1S7bVs;A1A3").
  Hypothesis Emc : ltac2:(tb__ "0|0|
S3S0S79Vt';A1S79Vs;A1A3").
  Hypothesis Ereg : ltac2:(tb__ "0|0|
S3ScS6aA1S7aVt';A1S7aVs;A1A3").
  Hypothesis Emetas : ltac2:(tb__ "0|0|
S3ScSeS69S8aA2A1S8eVt';A1S8eVs;A1A3").
  Hypothesis Eblocks : ltac2:(tb__ "0|0|
S3ScSeS0S0A2A1S98VL;Vt';A2S98VL;Vs;A2A3").
  Hypothesis HY : ltac2:(tb__ "0|2|
ScSeS81S0A2A1M0SeSbS69A1S6fA2M1S140G1S74Vt';A1R2R1A4S6G0G0S140G1S74Vs;A1R1R3A4Lktr';A2F_;Fres;Fktr;").

  Lemma client_addr_same a : ltac2:(tb__ "0|0|
S8S165S1bS94Sf5Vs;VL;A2Va;A4S165S1bS94Sf5Vt';VL;A2Va;A4A2").
  Proof using Eblocks Hgd Kc md tr. unfold client_addr, ma_blocks. cbn [ma_s ma_L]. rewrite Eblocks. tauto. Qed.
  Lemma region_of_same k : ltac2:(tb__ "0|0|
S3SbS6aA1S13fVt';Vk;A2S13fVs;Vk;A2A3"). Proof using Ereg. unfold region_of. rewrite Ereg. reflexivity. Qed.
  Lemma MT_same q : ltac2:(tb__ "0|0|
S3SbS8aA1S146Vt';Vq;A2S146Vs;Vq;A2A3"). Proof using Emetas. unfold MT. rewrite Emetas. reflexivity. Qed.
  Lemma keys_same : ltac2:(tb__ "0|0|
S3ScS69A1S141Vt';A1S141Vs;A1A3"). Proof using Emetas. unfold keys. rewrite Emetas. reflexivity. Qed.

  Lemma post_common_same X' A' : ltac2:(tb__ "0|0|
S138VX;VX';Sf5Vt';VL;A2VA';A4S138VX;VX';Sf5Vs;VL;A2VA';A4F_;").
  Proof using Eact Ebnc Emc Emetas Ereg Eseq Eunm Eusage Hgd Kc md tr.
    intros PC. unfold am_post_common in *. cbn [ma_s ma_L] in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    split; [exact P1|]. split; [exact P2|]. split.
    { destruct P3 as (A1 & A2 & A3 & A4 & A5). unfold am_frame. rewrite <- Eact, <- Eusage, <- Emc, <- Ereg. split; [exact A1|]. split; [exact A2|]. split; [|split; [exact A4 | exact A5]].
      intros k rg Hk Hkd. apply A3; [rewrite region_of_same; exact Hk | exact Hkd]. }
    split; [destruct P4 as (B1 & B2 & B3 & B4 & B5 & B6); unfold am_fields_same; rewrite <- Eact, <- Eusage, <- Ebnc, <- Eunm, <- Eseq, <- Emc; repeat split; assumption|].
    split; [intros g gm; rewrite (P5 g gm); unfold usedX, MTX; rewrite MT_same; tauto|].
    split.
    { destruct P6 as (ext & K1 & K2 & K3). exists ext. rewrite <- keys_same. split; [exact K1|]. split; [exact K2|]. intros g Hg. rewrite <- MT_same. exact (K3 g Hg). }
    split; [rewrite <- keys_same; exact P7 | cbn [ma_L ma_s]; rewrite <- Ereg; exact P8].
  Qed.

  Theorem LQP_rebase_state w : ltac2:(tb__ "0|0|
S11cS1bS1cVrhoX;S131S1bS94Sf2VX;VR;VU;Sf5Vt';VL;A2VKc;A8Vw;A5S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8Vw;A5F_;").
  Proof using AGL AGW Eact Eblocks Ebnc Emc Emetas Ereg Eseq Eunm Eusage HY Hgd MEMC MEMG MEMM md tr.
    intros (Lp & Jp & rho' & Hin & [AV1 AV2] & Hsm & HJ).
    assert (AVr : agree_vals NF rho rho') by (split; [intros i Hi; rewrite <- (AGW i Hi); exact (AV1 i Hi) | intros l; rewrite <- (AGL l); exact (AV2 l)]).
    assert (MK : forall A', mem_kept segsU C_U (mkMA t' L) A' (rm rhoX) (rm rho') -> mem_kept segsU C_U (mkMA s L) A' (rm rho) (rm rho')).
    { intros A' M a Ha CA CA' NE NS. rewrite <- (MEMC a Ha CA NE NS). apply (M a Ha); [apply client_addr_same; exact CA | exact CA' | exact NE | exact NS]. }
    assert (MPK : maps_kept (mkMA t' L) (rm rhoX) (rm rho') -> maps_kept (mkMA s L) (rm rho) (rm rho')).
    { intros M k rg Hk Hkd Hl a Ha. cbn [ma_s ma_L] in *. rewrite <- (MEMM k rg a Hk Hkd Hl Ha). apply (M k rg); [rewrite region_of_same; exact Hk | exact Hkd | exact Hl | exact Ha]. }
    assert (CK : canary_kept segsU C_U (rm rhoX) (rm rho') -> canary_kept segsU C_U (rm rho) (rm rho')).
    { intros M a Ha. pose proof (M a Ha) as E. pose proof (MEMG a Ha) as G. unfold Contract.rd_of, Glue.rd_of in *. cbn beta in *. rewrite E. exact G. }
    unfold Posts_am in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    - exists (L_am_null IEC_U), (JL_am_null segsU C_U X R U (mkMA s L) Kc), rho'. split; [left; reflexivity|]. split; [exact AVr|]. split; [exact Hsm|].
      destruct HJ as (A' & MI & PC & MKx & MPx & CKx & (ktr & Y) & HK). exists A'.
      split; [exact MI|]. split; [exact (post_common_same _ _ PC)|]. split; [exact (MK A' MKx)|]. split; [exact (MPK MPx)|]. split; [exact (CK CKx)|].
      split; [exact (HY ktr _ Y) | exact HK].
    - exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'. split; [right; left; reflexivity|]. split; [exact AVr|]. split; [exact Hsm|].
      destruct HJ as (A' & m & Hm & MI & PC & NX & IK & MKx & MPx & CKx & (ktr & Y) & HK). exists A', m.
      split; [exact Hm|]. split; [exact MI|]. split; [exact (post_common_same _ _ PC)|]. split; [exact NX|]. split; [exact IK|]. split; [exact (MK A' MKx)|]. split; [exact (MPK MPx)|]. split; [exact (CK CKx)|].
      split; [exact (HY ktr _ Y) | exact HK].
  Qed.

  Theorem LQP_rebase_state_ok w : ltac2:(tb__ "0|3|
S11cS1bS1cVrhoX;S9SeS31S11dA2M0SaS31S11dS137Sf2A1M1S135S1bS94VX;VR;VU;Sf5Vt';VL;A2VKc;A7A4S10G0A1M2A3Vw;A5S11cS1bS1cVrho;S9G0SaS31S11dG1S135S1bS94VX;VR;VU;Sf5Vs;VL;A2VKc;A7A4G2A3Vw;A5F_;").
  Proof using AGL AGW Eact Eblocks Ebnc Emc Emetas Ereg Eseq Eunm Eusage HY Hgd MEMC MEMG MEMM md tr.
    intros (Lp & Jp & rho' & Hin & [AV1 AV2] & Hsm & HJ).
    assert (AVr : agree_vals NF rho rho') by (split; [intros i Hi; rewrite <- (AGW i Hi); exact (AV1 i Hi) | intros l; rewrite <- (AGL l); exact (AV2 l)]).
    assert (MK : forall A', mem_kept segsU C_U (mkMA t' L) A' (rm rhoX) (rm rho') -> mem_kept segsU C_U (mkMA s L) A' (rm rho) (rm rho')).
    { intros A' M a Ha CA CA' NE NS. rewrite <- (MEMC a Ha CA NE NS). apply (M a Ha); [apply client_addr_same; exact CA | exact CA' | exact NE | exact NS]. }
    assert (MPK : maps_kept (mkMA t' L) (rm rhoX) (rm rho') -> maps_kept (mkMA s L) (rm rho) (rm rho')).
    { intros M k rg Hk Hkd Hl a Ha. cbn [ma_s ma_L] in *. rewrite <- (MEMM k rg a Hk Hkd Hl Ha). apply (M k rg); [rewrite region_of_same; exact Hk | exact Hkd | exact Hl | exact Ha]. }
    assert (CK : canary_kept segsU C_U (rm rhoX) (rm rho') -> canary_kept segsU C_U (rm rho) (rm rho')).
    { intros M a Ha. pose proof (M a Ha) as E. pose proof (MEMG a Ha) as G. unfold Contract.rd_of, Glue.rd_of in *. cbn beta in *. rewrite E. exact G. }
    destruct Hin as [E|[]]; injection E as <- <-.
    exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'. split; [left; reflexivity|]. split; [exact AVr|]. split; [exact Hsm|].
    destruct HJ as (A' & m & Hm & MI & PC & NX & IK & MKx & MPx & CKx & (ktr & Y) & HK). exists A', m.
    split; [exact Hm|]. split; [exact MI|]. split; [exact (post_common_same _ _ PC)|]. split; [exact NX|]. split; [exact IK|]. split; [exact (MK A' MKx)|]. split; [exact (MPK MPx)|]. split; [exact (CK CKx)|].
    split; [exact (HY ktr _ Y) | exact HK].
  Qed.

  Theorem LQP_rebase_state_null w : ltac2:(tb__ "0|3|
S11cS1bS1cVrhoX;S9SeS31S11dA2M0SaS31S11dS134Sf2A1M1S136S1bS94VX;VR;VU;Sf5Vt';VL;A2VKc;A7A4S10G0A1M2A3Vw;A5S11cS1bS1cVrho;S9G0SaS31S11dG1S136S1bS94VX;VR;VU;Sf5Vs;VL;A2VKc;A7A4G2A3Vw;A5F_;").
  Proof using AGL AGW Eact Eblocks Ebnc Emc Emetas Ereg Eseq Eunm Eusage HY Hgd MEMC MEMG MEMM md tr.
    intros (Lp & Jp & rho' & Hin & [AV1 AV2] & Hsm & HJ).
    assert (AVr : agree_vals NF rho rho') by (split; [intros i Hi; rewrite <- (AGW i Hi); exact (AV1 i Hi) | intros l; rewrite <- (AGL l); exact (AV2 l)]).
    assert (MK : forall A', mem_kept segsU C_U (mkMA t' L) A' (rm rhoX) (rm rho') -> mem_kept segsU C_U (mkMA s L) A' (rm rho) (rm rho')).
    { intros A' M a Ha CA CA' NE NS. rewrite <- (MEMC a Ha CA NE NS). apply (M a Ha); [apply client_addr_same; exact CA | exact CA' | exact NE | exact NS]. }
    assert (MPK : maps_kept (mkMA t' L) (rm rhoX) (rm rho') -> maps_kept (mkMA s L) (rm rho) (rm rho')).
    { intros M k rg Hk Hkd Hl a Ha. cbn [ma_s ma_L] in *. rewrite <- (MEMM k rg a Hk Hkd Hl Ha). apply (M k rg); [rewrite region_of_same; exact Hk | exact Hkd | exact Hl | exact Ha]. }
    assert (CK : canary_kept segsU C_U (rm rhoX) (rm rho') -> canary_kept segsU C_U (rm rho) (rm rho')).
    { intros M a Ha. pose proof (M a Ha) as E. pose proof (MEMG a Ha) as G. unfold Contract.rd_of, Glue.rd_of in *. cbn beta in *. rewrite E. exact G. }
    destruct Hin as [E|[]]; injection E as <- <-.
    exists (L_am_null IEC_U), (JL_am_null segsU C_U X R U (mkMA s L) Kc), rho'. split; [left; reflexivity|]. split; [exact AVr|]. split; [exact Hsm|].
    destruct HJ as (A' & MI & PC & MKx & MPx & CKx & (ktr & Y) & HK). exists A'.
    split; [exact MI|]. split; [exact (post_common_same _ _ PC)|]. split; [exact (MK A' MKx)|]. split; [exact (MPK MPx)|]. split; [exact (CK CKx)|].
    split; [exact (HY ktr _ Y) | exact HK].
  Qed.
End RebaseState.

Section BK.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SbS69A1S6cVs;A1S14S69A1A3").
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : st_avail_meta_area_count s = 0.
  Hypothesis Hinit : st_init_done s = true.
  Variables (rb : nat) (pb : Z).
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S3S72S73Vs;A1S87Vrb;Vpb;A2A3").
  Variable Kc : ltac2:(tb__ "0|0|
ScSe6A1Se7OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3Se9Vvm;Se8Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S164S1bVok;VKc;A3").

  Hypothesis HVI : vm_insensitive Kc.

  Lemma STK : ltac2:(tb__ "0|3|
S4S5bZ0S5cSfeVrho;A1M0SfdVrho;A1M1A2M2A2S4S5bS96VL;A1G2A2S4S5bG0S5eZ2Z40A2A2S5bG1S65SbeA1A2A2A2A2"). Proof using EmW Hav Hev Hgd Hsm_pre Htop L s. exact stk_facts. Qed.
  Lemma HIRv : img_reserved C_U vm. Proof using HMI. exact (mig_img HMI). Qed.
  Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S177S1bVok;S157SffVtr;Vmd';A2A1A3F_;").
  Proof using HOK. intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho). Qed.

  Local Abbreviation PZ := (AllocMetaBrk.pz L rb pb).
  Lemma brkZ_pz : brkZ = PZ.
  Proof using Hbrk. unfold U.Mal_ameta__G1.Mal_ameta_I.brkZ. rewrite Hbrk. unfold U.Mal_ameta__G1.Mal_ameta_I.zA, addr_of, AllocMetaBrk.pz. reflexivity. Qed.
  Lemma pz_pre : ltac2:(tb__ "0|5|
S4S3S0S61S103VL;Vrb;Vpb;A3M0Z1000M1A2Z0M2A3S4S5bS68Z2M3G1A2G0A2S4S5bG0S96VL;A1A2S4S4S5bG2G0A2S5dG0S5eG3Z40A2A2A2S4S3S0S92Q40M4SeeVvm;A1A2G0A3S5bS92G4Sf0Vvm;A1A2G0A2A2A2A2A2A2").
  Proof using HI HMI Hav Hbrk Hev Hgd.
    pose proof (AllocMetaBrk.bk_facts X R U s HI rb pb Hbrk) as (Hbr & Hr & Hk & Hl & Hlen & Hpb & LT & Ebp).
    pose proof HV as (_ & _ & V3 & _ & _ & _ & _ & X4 & _). rewrite Hbrk in V3. destruct V3 as (E0 & Eb & Es & _).
    destruct (X4 rb _ Hr Hl) as [B1 B2]. pose proof HL as (_ & Halign & _). pose proof (Halign rb _ Hr Hl) as AL.
    assert (M1 : PGSZ * 2 <= PGSZ * pb) by (apply Z.mul_le_mono_nonneg_l; unfold PGSZ; lia).
    assert (PZA : PZ mod PGSZ = 0) by (unfold AllocMetaBrk.pz; rewrite Z.add_mod, AL, Z.mul_comm, Z.mod_mul by (unfold PGSZ; lia); reflexivity).
    top_ranges. unfold AllocMetaBrk.pz in *. unfold PGSZ in *. repeat split; try assumption; lia.
  Qed.

  Definition N_BK : list sobj := ltac2:(tb__ "0|1|
S9S20Sb0Sa2A1S9S20Sb1S9S20SacSa2A1S9S20Sb2Sa2A1S9S20SafS9S20Sb3Sa2Sa3PafA1Z1A3S9S20SaeSa2S23Z0A1M0Sa3Pb0A1G0G0Sa3Pb8A1Sa3Pb9A1Sa3PbaA1Sa3Pb1A1A9S9S20SadSa2Sa3PbbA1A2S10S20A1A3A3A3A3A3A3A3A3").
  Definition R_BK : list (Z * Z) := ltac2:(tb__ "0|1|
S9SeS0S0A2M0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3").
  Lemma N_BK_ranges : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S115A4S119A3").
  Proof using Hav Hev Hgd Htp.
    cbn [map N_BK R_BK]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk. cbn [am_got am_libc am_ctx AM_P].
    rewrite !(rng_lit (SLit 167248) _ _ _ _ 167248) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369496) _ _ _ _ 369496) by (try lia; cbn [eval]; apply u64; lia).
    rewrite !(rng_lit (SLit 369608) _ _ _ _ 369608) by (try lia; cbn [eval]; apply u64; lia).
    rewrite (rng_lit (v 173) _ _ _ _ 0x5a338) by (try lia; rewrite ev173; apply u64; cbn; lia).
    rewrite (rng_lit (SVar 24) _ _ _ _ 0x3a0d0) by (try lia; rewrite ev_tp; apply u64; cbn; lia).
    unfold R_BK. reflexivity.
  Qed.
  Lemma N_BK_hold : ltac2:(tb__ "0|0|
S12cS20S2fS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2A3S115A3").
  Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Htp.
    unfold N_BK. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
    constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
    constructor; [apply hold_errno|]. constructor; [exact HS|].
    constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
    constructor; [apply hold_brk|]. constructor.
  Qed.
  Lemma BK_facts_hold : ltac2:(tb__ "0|0|
S12cS29S3cSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7A1S11S29Sc0PbbZcA2Sc2A3A3").
  Proof using HI HMI Hav Hbrk Hev Hgd Htp.
    pose proof pz_pre as (P1 & P2 & P3 & P4 & _). top_ranges. apply Forall_app. split; [|apply ctx_facts_hold].
    assert (E187 : bv_unsigned (eval (rho1 mW) (v 187)) = PZ) by (rewrite ev187, brkZ_pz; apply u64; lia).
    unfold ptr_facts. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds].
    - change (v 187) with (SVar 187%positive) in E187. cbn [eval] in E187. rewrite E187. split; [lia|]. change (2 ^ 12) with 4096. exact P1.
    - rewrite E187. change (bv_unsigned (eval (rho1 mW) (SLit (2 ^ 47)))) with (2 ^ 47). lia.
    - rewrite E187. change (bv_unsigned (eval (rho1 mW) (SLit 4096))) with 4096. lia.
  Qed.
  Theorem entry_BK : ltac2:(tb__ "0|0|
S2bS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sa4S1bSa2SbcA3SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4").
  Proof using EmW Erd Ewok HI HMI Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    pose proof stk_facts as (S1 & S2 & S3 & S4). top_ranges.
    pose proof (smatch_extend_objs segsU (rho1 mW) (ContractAM.Pre_am IEC_U) tr ms md N_BK AM_NEXT sm_pre1) as E1.
    cbn zeta in E1.
    assert (SM1 : smatch segsU (rho1 mW)
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_BK) (ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT (ss_lenient (ContractAM.Pre_am IEC_U)))
      (tr, mkCfg ms md)).
    { apply E1.
      - vm_compute. reflexivity.
      - change (rm (rho1 mW)) with mW. apply N_BK_hold.
      - apply (vs_stack_of_ranges (rho1 mW) (stack_win ContractAM.AM_D) N_BK R_BK N_BK_ranges).
        change (stack_win ContractAM.AM_D) with (O_stk []). rewrite rng_stk.
        unfold R_BK. repeat (apply Forall_cons; [unfold SymState.ranges_disjoint; cbn [fst snd]; lia|]). apply Forall_nil.
      - apply (pairwise_of_ranges (rho1 mW) N_BK R_BK N_BK_ranges).
        cbn [pw R_BK]. repeat match goal with |- _ /\ _ => split | |- True => exact I | |- Forall _ _ => first [apply Forall_nil | apply Forall_cons] | |- SymState.ranges_disjoint _ _ => unfold SymState.ranges_disjoint; cbn [fst snd]; lia end. }
    pose proof (smatch_set_objs_facts_next segsU (rho1 mW) _ (tr, mkCfg ms md) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_BK)
                  (ptr_facts 187 12 ++ ctx_facts) AM_NEXT false SM1) as E2.
    cbn [cfg_ms snd] in E2.
    match goal with |- smatch _ _ ?S _ => change S with
      (mkSS (ss_pc (ContractAM.Pre_am IEC_U)) (ss_regs (ContractAM.Pre_am IEC_U)) (ss_fregs (ContractAM.Pre_am IEC_U)) (ss_fcsr (ContractAM.Pre_am IEC_U))
            (ss_resv (ContractAM.Pre_am IEC_U)) (ss_objs (ContractAM.Pre_am IEC_U) ++ N_BK)
            ((ptr_facts 187 12 ++ ctx_facts) ++ ss_facts (ContractAM.Pre_am IEC_U)) AM_NEXT false) end.
    apply E2.
    - destruct SM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _). exact HM.
    - apply BK_facts_hold.
    - vm_compute. reflexivity.
  Qed.

  Definition stkE_cells : list cell := ltac2:(tb__ "0|1|
S9S24S27S23N38A1Z8M0Sa3PaeA1A3S9S24S27S23N30A1G0S25P28A1A3S9S24S27S23N28A1G0S25P27A1A3S9S24S27S23N20A1G0S25P26A1A3S9S24S27S23N18A1G0S25P1dA1A3S9S24S27S23N10A1G0S25P1cA1A3S9S24S27S23N8A1G0S25PbA1A3S10S24A1A3A3A3A3A3A3A3").
  Definition LBE0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2SbcA3S158A2Sa8SbcA1A3A1").
  Definition LBE : sstate := ltac:(let x := eval vm_compute in LBE0 in exact x).
  Lemma LBE_eq : LBE0 = LBE. Proof using . vm_cast_no_check (@eq_refl sstate LBE). Qed.
  Lemma LBE_misc : ltac2:(tb__ "0|0|
S4S3S0S2eS113A1Z20d50A3S4S3S21S22S113Z11A2S23Zd6A1A3S4S3S21S22S113ZaA2S40S172S25PbbA1S23Z1000A1A3A3S4S3S1S2cS113A1Sa5A3S3ScS20A1S2aS113A1S9S20Sa6S114A1S115A3A3A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LBE_ecall : ltac2:(tb__ "0|0|
S3SbS173A1S15cS1bS2eS113A1A2S12S173S175A2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.
  Lemma Pre_ok_eq : ltac2:(tb__ "0|0|
S3S31Sa4S1bSa2Sb7A3S178S113S22S113ZaA2S2aS113A1S2cS113A1A4A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma Pre_fail_eq : ltac2:(tb__ "0|0|
S3S31Sa4S1bSa2SbaA3Sa9S181S113A1Sc3S113P12cA2A2A3").
  Proof using . vm_compute. reflexivity. Qed.

  Definition valC (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;S26VrhoX;A1A7VrhoX;A3").
  Lemma evC rhoX e : ltac2:(tb__ "0|0|
S111VrhoX;A1S3SdS3fSa5Ve;A2SfA3S3S90Q40A1S30VrhoX;Ve;A2S30SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2A3F_;F_;").
  Proof using . intros A He. rewrite <- (eval_agree AM_NEXT (rho1 (rm rhoX)) rhoX e A He). exact (eval_set_rm (rho1 mW) (rm rhoX) e). Qed.
  Lemma evC187 rhoX : ltac2:(tb__ "0|1|
S111VrhoX;A1S3S90Q40M0A1S30VrhoX;S25PbbA1A2S91G0S103VL;Vrb;Vpb;A3A2A3F_;").
  Proof using Hav Hbrk Hev Hgd mW. intros VX. rewrite (evC rhoX (SVar 187) VX eq_refl). rewrite <- brkZ_pz. exact (ev187 mW). Qed.
  Lemma evC187p rhoX : ltac2:(tb__ "0|2|
S111VrhoX;A1S3S90Q40M0A1S30VrhoX;S40S172S25PbbA1S23Z1000M1A1A3A2S91G0S5cS103VL;Vrb;Vpb;A3G1A2A2A3F_;").
  Proof using HI HMI Hav Hbrk Hev Hgd mW.
    intros VX. pose proof pz_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    pose proof (evC187 rhoX VX) as E. cbn [eval] in E |- *. rewrite E. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (u64 PZ) by lia. rewrite !Z_to_bv_unsigned. change (bv_wrap 64 ?q) with (q mod bv_modulus 64). change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small 4096) by lia. reflexivity.
  Qed.
  Lemma valC_ext rhoX rhoY n : ltac2:(tb__ "0|0|
S111VrhoX;A1S160Sa5Vn;A2S33Vn;VrhoX;VrhoY;A3S111VrhoY;A1F_;F_;F_;").
  Proof using Hav Hev Hgd.
    intros (A1 & A2 & A3) Hn (B1 & B2 & B3). split; [|split].
    - intros i Hi. cbn [rho1 rw]. rewrite <- (B1 i) by lia. rewrite <- (A1 i Hi). reflexivity.
    - intros l. cbn. rewrite <- B2, <- A2. reflexivity.
    - intros x. reflexivity.
  Qed.
  Definition memC (m : word -> option byte) : Prop := ltac2:(tb__ "0|3|
S90Q40M0A1S5S4S5bS103VL;Vrb;Vpb;A3M1S92G0R1A2M2A2S5dG2S5cG1Z1000A2A2A2A1S3SbS90Q8A1A1Vm;R2A1VmW;R2A1A3F_;Fx;").
  Definition zeroC (m : word -> option byte) : Prop := ltac2:(tb__ "0|5|
S90Q40M0A1S4S5bS103VL;Vrb;Vpb;A3M1S92G0R1A2M2A2S5dG2S5cG1Z1000A2A2A2S3SbS90Q8M3A1M4A1Vm;R2A1S12G4S91G3Z0A2A2A3F_;Fx;").

  Lemma statics_ranges rhoL : ltac2:(tb__ "0|1|
S111VrhoL;A1S3ScSeS0S0A2M0A1S12eS20G0S28VrhoL;A1S115A4S9G0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3A3F_;").
  Proof using Hav Hev Hgd Htp mW.
    intros HagL. cbn [map N_BK].
    unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxB, O_brk. cbn [am_got am_libc am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    assert (EL0 : forall z, eval rhoL (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite (evC rhoL (v 173) HagL eq_refl), ev173.
    rewrite (evC rhoL (SVar 24) HagL eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.
  Lemma stk_range rhoL : ltac2:(tb__ "0|1|
S111VrhoL;A1S3SeS0S0A2S28VrhoL;Sa6S114A1A2SaS0S0S5cSfeVrho;A1M0SfdVrho;A1A2G0A4A3F_;").
  Proof using Hav Hev Hgd mW.
    intros HagL.
    rewrite (ReabKit.range_ag (rho1 (rm rhoL)) rhoL [O_stk stkE_cells] [] AM_NEXT HagL ltac:(vm_compute; reflexivity) (O_stk stkE_cells) ltac:(left; reflexivity)).
    change (obj_range (rho1 (rm rhoL)) (O_stk stkE_cells)) with (obj_range (rho1 mW) (O_stk stkE_cells)). apply rng_stk.
  Qed.

  Section Granted.
    Hypothesis HGOK : ltac2:(tb__ "0|1|
S3SdS192Vmd;S91Q40S5cS103VL;Vrb;Vpb;A3Z1000A2A2M0G0A3SfA3").

    Lemma round_pz : ltac2:(tb__ "0|2|
S4S3S0SecS103VL;Vrb;Vpb;A3M0A1G0A3S3S0SecS5cG0Z1000A2M1A1G1A3A2").
    Proof using HI HMI Hav Hbrk Hev Hgd. pose proof pz_pre as (P1 & P2 & _). unfold page_round_up_Z, page_size. clear - P1 P2. Z.to_euclidean_division_equations; lia. Qed.
    Lemma U1 : ltac2:(tb__ "0|2|
S3S0S92Q40M0S91G0S5cS103VL;Vrb;Vpb;A3Z1000A2M1A2A2G1A3").
    Proof using HI HMI Hav Hbrk Hev Hgd. pose proof pz_pre as (P1 & P2 & P3 & P4 & _). top_ranges. apply u64. lia. Qed.
    Lemma G_ceilB : ltac2:(tb__ "0|0|
S5bS5cS103VL;Vrb;Vpb;A3S7fA2S96VL;A1A2").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd.
      pose proof pz_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_pz as [R1 R2]. pose proof HGOK as G. unfold brk_grow_ok in G. rewrite <- Evm, P5, U1 in G.
      replace (0 <? PZ) with true in G by (symmetry; apply Z.ltb_lt; lia). replace (PZ <? PZ + 4096) with true in G by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb] in G. rewrite R1, R2 in G. replace (PZ <? PZ + 4096) with true in G by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in G as [G _]. apply andb_prop in G as [G _]. apply Z.leb_le in G. unfold PGSZ. rewrite (vm_ok_top L s vm HV). exact G.
    Qed.
    Lemma G_freeB : ltac2:(tb__ "0|5|
SeS90Q40M0A1M1G1A2M2Se1G2R1S11G2SefVvm;A1SebVvm;A1A3A3S7S5bS5cS92G0S13G1G1R2A3A2M3S92G0S16G1G1R2A3A2A2S103VL;Vrb;Vpb;A3M4A2S5bS5cG4S7fA2G3A2A2F_;Fe;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd.
      pose proof pz_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_pz as [R1 R2]. pose proof HGOK as G. unfold brk_grow_ok in G. rewrite <- Evm, P5, U1 in G.
      replace (0 <? PZ) with true in G by (symmetry; apply Z.ltb_lt; lia). replace (PZ <? PZ + 4096) with true in G by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb] in G. rewrite R1, R2 in G. replace (PZ <? PZ + 4096) with true in G by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in G as [G _]. apply andb_prop in G as [_ G]. unfold page_size in G. replace (PZ + 4096 + 4096 - PZ) with 8192 in G by lia.
      intros [a sz] Hin. pose proof (region_free_In _ _ _ _ _ G Hin) as OV. unfold iv_overlap in OV. cbn [fst snd].
      rewrite (u64 PZ) in OV by lia. change (bv_unsigned (Z_to_bv 64 8192)) with 8192 in OV. unfold PGSZ.
      apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
    Qed.

Local Abbreviation B_rr := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.rr s).
Local Abbreviation B_bp := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bp rb pb).
Local Abbreviation B_bm := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bm rb pb).
Local Notation "§20§ h__" := (h__ s rb pb) (at level 10, h__ global).
Local Abbreviation B_tB := (§20§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.tB).
Local Abbreviation B_rg0 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.rg0 s rb).
Local Abbreviation B_rgB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.rgB s rb).
Local Abbreviation B_s0_t := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.s0_t X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Notation "§21§ h__" := (h__ X R U s HI rb pb Hbrk) (at level 10, h__ global).
Local Abbreviation B_bk_facts := (§21§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bk_facts).
Local Notation "§22§ h__" := (h__ X R U s HI Hhd Hcnt Hac rb pb Hbrk) (at level 10, h__ global).
Local Abbreviation B_SPECB := (§22§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.SPECB).
Local Abbreviation B_HIB := (§22§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.HIB).
Local Abbreviation B_tB_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.tB_fields X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_region_of_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.region_of_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_C_tn := (§20§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.C_tn).
Local Abbreviation B_bm_prid := (§21§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bm_prid).
Local Abbreviation B_fresh_slot := (§21§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.fresh_slot).
Local Abbreviation B_bp_fresh := (§21§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bp_fresh).
Local Abbreviation B_tBpre := (§20§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.tBpre).
Local Abbreviation B_tB_upd := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.tB_upd X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_tBpre_fields := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.tBpre_fields X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_bm_fresh := (§21§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bm_fresh).
Local Abbreviation B_area_cells_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.area_cells_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_image_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.image_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_ctx_cells_tBC := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.ctx_cells_tBC X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_fp_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.fp_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_ub_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.ub_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_footers_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.footers_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_pz := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.pz L rb pb).
Local Abbreviation B_vmB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.vmB L rb pb vm).
Local Notation "§23§ h__" := (h__ X R U s L HI rb pb Hbrk) (at level 10, h__ global).
Local Abbreviation B_pz_eq := (§23§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.pz_eq).
Local Abbreviation B_bm_addr := (§23§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bm_addr).
Local Abbreviation B_brk_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.brk_facts X R U s L HI rb pb Hbrk HL vm HV G_ceilB).
Local Abbreviation B_page_vs_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.page_vs_image L rb pb C_U vm HIRv G_freeB).
Local Abbreviation B_page_vs_footprint := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.page_vs_footprint s L rb pb C_U vm Hctx statics_in_image_U HV HIRv G_freeB).
Local Abbreviation B_fp_size := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.fp_size s L vm HV).
Local Abbreviation B_map_region_vs_page := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.map_region_vs_page s L rb pb C_U vm Hctx statics_in_image_U HV HIRv G_freeB).
Local Abbreviation B_layout_ok_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.layout_ok_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL C_U vm Hctx statics_in_image_U HV HIRv G_ceilB G_freeB).
Local Abbreviation B_u_pz := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.u_pz X R U s L HI rb pb Hbrk HL vm HV G_ceilB).
Local Abbreviation B_u_pgsz := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.u_pgsz).
Local Abbreviation B_u_brk := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.u_brk X R U s L HI rb pb Hbrk HL vm HV G_ceilB).
Local Abbreviation B_vm_ok_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.vm_ok_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL vm HV G_ceilB G_freeB).
Local Abbreviation B_ledger_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.ledger_tB X R U s L HI rb pb Hbrk HL C_U vm statics_in_image_U HV HLG HIRv G_ceilB G_freeB).
Local Abbreviation B_maps_wf_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.maps_wf_tB X R U s L HI rb pb Hbrk HL vm HV HMW G_ceilB G_freeB).
Local Abbreviation B_xraw_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.xraw_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_bm_notX := (§22§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bm_notX).
Local Abbreviation B_keys_tB := (§22§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.keys_tB).
Local Abbreviation B_am_frame_tB := (§22§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.am_frame_tB).
Local Abbreviation B_bounded_tB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.bounded_tB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL C_U vm Hctx statics_in_image_U HV HLG HIRv HB G_ceilB G_freeB).
Local Abbreviation B_cell_whereB := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.cell_whereB X R U s L HI HXr Hhd Hcnt Hac Hinit rb pb Hbrk HL).
Local Abbreviation B_page_vs_block := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaBrk.page_vs_block X R U s L HI HXr rb pb C_U vm Hctx statics_in_image_U HV HIRv G_freeB).

    Lemma pz_facts : ltac2:(tb__ "0|3|
S4S3S0S61S103VL;Vrb;Vpb;A3M0Z1000M1A2Z0M2A3S4S5bG1G0A2S4S5bS5cG0G1A2S96VL;A1A2S4S5bG2G0A2S5dG0S5eZ2Z40A2A2A2A2A2A2").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. pose proof pz_pre as (P1 & P2 & P3 & P4 & _). pose proof G_ceilB as G. unfold PGSZ in G. repeat split; lia. Qed.

    Definition md2 : Model := ltac2:(tb__ "0|1|
Sf1S193Se8Vmd;A1S91Q40S5cS103VL;Vrb;Vpb;A3Z1000A2A2M0G0A3Vmd;A2").
    Lemma K2 : Kc tr md2.
    Proof using HKc HOK. destruct HOK as (_ & _ & [VI _]). unfold md2. apply VI. exact HKc. Qed.
    Lemma K2x : Kc tr md2.
    Proof using HKc HVI. unfold md2. apply HVI. exact HKc. Qed.
    Lemma vm2_eq : ltac2:(tb__ "0|0|
S3Se9Se8Sc8A1S108VL;Vrb;Vpb;Vvm;A4A3").
    Proof using Evm HI HMI Hav Hbrk Hev Hgd.
      pose proof pz_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof round_pz as [R1 R2]. top_ranges.
      assert (EB : vm_brk vm = Z_to_bv 64 PZ) by (rewrite <- P5; symmetry; apply Z_to_bv_bv_unsigned).
      unfold md2. rewrite m_vmmaps_with_vmmaps, <- Evm. unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow, brk_unmaps, AllocMetaBrk.vmB.
      rewrite EB, U1, (u64 PZ) by lia.
      replace (0 <? PZ) with true by (symmetry; apply Z.ltb_lt; lia). replace (PZ + 4096 <? PZ) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (PZ <? PZ + 4096) with true by (symmetry; apply Z.ltb_lt; lia).
      assert (NZ : w_is0 (Z_to_bv 64 (PZ + 4096)) = false).
      { unfold w_is0, bv_eqb. rewrite U1. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
      rewrite NZ. cbn [negb andb app]. rewrite R1, R2. unfold brk_page_range.
      replace (PZ + 4096 <? PZ) with false by (symmetry; apply Z.ltb_ge; lia). cbn [maps_subtract_ranges fold_left].
      unfold wz, PGSZ. f_equal. f_equal. f_equal. apply bv_eq. rewrite bv_sub_unsigned, U1, (u64 PZ) by lia. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv_unsigned. change (bv_wrap 64 4096) with 4096. rewrite Z.mod_small by lia. lia.
    Qed.

    Lemma LBE_objs_miss rhoL : ltac2:(tb__ "0|1|
S111VrhoL;A1S20Se1S20R1S9S20Sa6S114A1S115A3A3S3eS28VrhoL;R2A2SaS0S0S103VL;Vrb;Vpb;A3M0S5cG0Z1000A2A4A2F_;Fo;F_;").
    Proof using EmW Evm HGOK HI HMI Hav Hbrk Hev Hgd Hsm_pre Htop Htp.
      intros VL o Ho.
      assert (RO : In (obj_range rhoL o) ((sp0 + D0, sp0) :: [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616); (369616, 369628); (369632, 369696); (370536, 370544)])).
      { destruct Ho as [<-|Ho]; [left; symmetry; exact (stk_range rhoL VL) | right; rewrite <- (statics_ranges rhoL VL); apply in_map; exact Ho]. }
      pose proof STK as (S1 & S2 & S3 & S4). pose proof pz_facts as (P1 & P2 & P3 & P4). pose proof B_page_vs_image as MISS.
      cbn [mc_img_lo mc_img_hi C_U] in MISS. unfold PGSZ in MISS. clear - RO MISS P2 P3 S2. top_ranges.
      assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (PZ, PZ + 4096)).
      { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
        destruct (Z_le_dec hi PZ); [lia|]. destruct (Z_le_dec (PZ + 4096) lo); [lia|]. exfalso.
        destruct (Z_le_dec PZ lo); [apply (MISS lo); lia | apply (MISS PZ); lia]. }
      destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
      repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
    Qed.
    Lemma segs_inside : ltac2:(tb__ "0|1|
S3SdSe2S16fS16fS18S60Z10000S64S170R1A1A1M0A2S60S5cG0S64S171R1A1A1A2Z5b000A2A2Lseg;S1bA3SfA3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma ro_addr_page (x : word) : ltac2:(tb__ "0|2|
S4S5bS103VL;Vrb;Vpb;A3M0S92Q40Vx;A2M1A2S5dG1S5cG0Z1000A2A2A2S3SdS4eS1bVx;A2S17A3F_;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd.
      intros Hx. apply ro_addr_false_of_no_segment.
      destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
      destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
      pose proof (proj1 (forallb_forall _ _) segs_inside seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
      apply (B_page_vs_image (bv_unsigned x)); [cbn [mc_img_lo mc_img_hi C_U]; lia|]. unfold PGSZ. exact Hx.
    Qed.

    Definition LC0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2Sb7A3S158A2Sa8Sb7A1A3A1").
    Definition LC : sstate := ltac:(let x := eval vm_compute in LC0 in exact x).
    Lemma LC_eq : LC0 = LC. Proof using . vm_cast_no_check (@eq_refl sstate LC). Qed.
    Definition pageK : sobj := O_page (SVar 187).
    Definition subC : list (positive * sv) := ltac2:(tb__ "0|3|
S9SeS1S21A2M0SaS1S21Pc9S22Sc5Z9A2A4S9G0SaS1S21PccS22Sc5Z1M1A2A4S9G0SaS1S21PcdS22Sc5Z5A2A4S9G0SaS1S21PceS22Sc5Z6A2A4S9G0SaS1S21PcfS22Sc5Z7A2A4S9G0SaS1S21Pd0S22Sc5Z8A2A4S9G0SaS1S21Pd2S22Sc5ZaA2A4S9G0SaS1S21Pd3S22Sc5ZbA2A4S9G0SaS1S21Pd4S22Sc5ZcA2A4S9G0SaS1S21Pd5S22Sc5ZdA2A4S9G0SaS1S21Pd6S22Sc5ZeA2A4S9G0SaS1S21Pd7S22Sc5ZfA2A4S9G0SaS1S21Pd8S22Sc5Z10A2A4S9G0SaS1S21Pd9S22Sc5Z11A2A4S9G0SaS1S21PdcS22Sc5Z14A2A4S9G0SaS1S21Pe4S22Sc5Z1cA2A4S9G0SaS1S21Pe5S22Sc5Z1dA2A4S9G0SaS1S21Pe6S22Sc5Z1eA2A4S9G0SaS1S21Pe7S22Sc5Z1fA2A4S9G0SaS1S21Pb7S23G1A1A4S9G0SaS1S21PbbM2S40S172S25G2A1S23Z1000A1A3A4S10G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
    Definition srcF : sstate := ltac2:(tb__ "0|0|
Sa9S38S2eSc5A1S3aSc5A1S36Sc5A1S35Sc5A1S37Sc5A1S11S20S2aSc5A1S9S20Sc7S10S20A1A3A3S34Sc5A1S2cSc5A1S39Sc5A1A9S9S29S47S174Sa3PbaA1S23Z0A1A3S10S29A1A3A2").
    Definition srcN : sstate := ltac2:(tb__ "0|2|
Sa9S38S2eSc5A1S3aSc5A1S36Sc5A1S35Sc5A1S37Sc5A1S11S20S2aSc5A1S9S20Sc7S9S20Sa7S10S20A1A3A3A3S34Sc5A1S2cSc5A1S39Sc5A1A9S9S29SbfPbaM0A1S9S29S46G0Z3A2S9S29S3bS25G0A1M1S23S5eZ2Z2fA2A1A2S9S29S3bS23Z1000A1G1A2S10S29A1A3A3A3A3A2").
    Lemma entF : ltac2:(tb__ "0|0|
S3SdS15dSccSa4S1bSa2Sb4A3Sc9A3SfA3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma entN : ltac2:(tb__ "0|0|
S3SdS15dScdSa4S1bSa2Sb5A3Sc9A3SfA3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Definition O_ctxC : sobj := ltac2:(tb__ "0|3|
S49S23Sc4Sa2A1A1S23Z18A1M0S23Z58A1S9S24S27S23Z30A1Z8M1S23Z1A1A3S9S24S27G0G1S23Z0A1M2A3S9S24S27S23Z20A1G1Sa3Pb0A1A3S9S24S27S23Z28A1G1G2A3S9S24S27S23Z38A1G1Sa3Pb8A1A3S9S24S27S23Z40A1G1Sa3Pb9A1A3S9S24S27S23Z48A1G1Sa3PbaA1A3S9S24S27S23Z50A1G1Sa3Pb1A1A3S10S24A1A3A3A3A3A3A3A3A3S44A5").
    Definition O_brkC : sobj := ltac2:(tb__ "0|0|
SadSa2S40S172S25PbbA1S23Z1000A1A3A2").
    Lemma LC_misc : ltac2:(tb__ "0|1|
S4S3S0S2eSc5A1Z20e3cA3S4S3S1S2cSc5A1Sa5A3S4S3S21S22Sc5Z9A2S25PbbA1A3S4S3ScS20A1S2aSc5A1S9S20Sa6S114A1S11S20S12fS20U6S115A3S9S20ScbS9S20ScaS10S20A1A3A3A3A3A3S3SdSe2SeS1S21A2M0G0S60Zc8S2S13S1S21R1A3A1A2Lp;S12fG0U13Sc9A3A3SfA3A2A2A2A2").
    Proof using . vm_compute. repeat split; reflexivity. Qed.
    Lemma swfF : ltac2:(tb__ "0|0|
S3SdS42S38S2eSc5A1S3aSc5A1S36Sc5A1S35Sc5A1S37Sc5A1S11S20S2aSc5A1S9S20Sc7S10S20A1A3A3S34Sc5A1S2cSc5A1S39Sc5A1A9A1SfA3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma swfN : ltac2:(tb__ "0|0|
S3SdS42S38S2eSc5A1S3aSc5A1S36Sc5A1S35Sc5A1S37Sc5A1S11S20S2aSc5A1S9S20Sc7S9S20Sa7S10S20A1A3A3A3S34Sc5A1S2cSc5A1S39Sc5A1A9A1SfA3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma LC_objs_missX rhoL : ltac2:(tb__ "0|1|
S111VrhoL;A1S20Se1S20R1S2aSc5A1A3S3eS28VrhoL;R2A2SaS0S0S103VL;Vrb;Vpb;A3M0S5cG0Z1000A2A4A2F_;Fo;F_;").
    Proof using EmW Evm HGOK HI HMI Hav Hbrk Hev Hgd Hsm_pre Htop Htp.
      intros VL o Ho. pose proof LC_misc as (_ & _ & _ & EO & _). rewrite EO in Ho.
      assert (H' : exists o', In o' (O_stk stkE_cells :: N_BK) /\ obj_range rhoL o' = obj_range rhoL o).
      { destruct Ho as [<-|Ho]; [exists (O_stk stkE_cells); split; [left; reflexivity|reflexivity]|].
        apply in_app_iff in Ho as [Ho|Ho].
        - exists o. split; [right|reflexivity]. unfold N_BK in Ho |- *. cbn [firstn In] in Ho |- *. tauto.
        - destruct Ho as [<-|[<-|[]]].
          + exists (O_ctxB AM_P (SLit 0) (v 176) (SLit 0) (SLit 0) (v 184) (v 185) (v 186) (v 177)). split; [unfold N_BK; cbn [In]; tauto | reflexivity].
          + exists (O_brk AM_P (v 187)). split; [unfold N_BK; cbn [In]; tauto | reflexivity]. }
      destruct H' as (o' & Ho' & <-). exact (LBE_objs_miss rhoL VL o' Ho').
    Qed.

    Section AtCut.
      Variables (msK : machine_state) (rhoC : valuation).
      Hypothesis VC : valC rhoC.
      Hypothesis MC : memC (rm rhoC).
      Hypothesis ZC : zeroC (rm rhoC).
      Hypothesis HsmK : ltac2:(tb__ "0|0|
S2bS1bVrhoC;Sc5SaScSe6A1Sf9Vtr;SfaVmsK;Sc8A2A4A4").

      Lemma HromC : rom_ok segsU msK. Proof using HsmK. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmK))))). Qed.
      Lemma pageK_range : ltac2:(tb__ "0|1|
S3SeS0S0A2S28VrhoC;Sc7A2SaS0S0S103VL;Vrb;Vpb;A3M0S5cG0Z40A2A4A3").
      Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd VC mW.
        clear HsmK ZC MC. unfold obj_range, obj_lo_of, obj_hi_of, pageK, O_page. cbn [ob_base ob_lo ob_hi]. rewrite (evC187 rhoC VC). rewrite !soff_lit_small by lia.
        pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges. rewrite u64 by lia. f_equal; lia.
      Qed.
      Lemma hold_pageK : ltac2:(tb__ "0|0|
S2fS1bVrhoC;S155VmsK;S26VrhoC;A1A2Sc7A4").
      Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd HsmK VC ZC mW.
        pose proof HromC as HromC. clear HsmK. pose proof pz_facts as (P1 & P2 & P3 & P4). top_ranges.
        change pageK with (carved (SVar 187) 0 64
          [(0, 8%nat, SLit 0); (8, 8%nat, SLit 0); (16, 4%nat, SLit 0); (20, 4%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0); (40, 8%nat, SLit 0); (48, 4%nat, SLit 0); (52, 4%nat, SLit 0); (56, 8%nat, SLit 0)]).
        assert (B : bv_unsigned (eval rhoC (SVar 187)) = PZ) by (rewrite (evC187 rhoC VC); apply u64; lia).
        assert (ZB : forall off, 0 <= off < 64 -> rm rhoC (Z_to_bv 64 (PZ + off)) = Some (Z_to_bv 8 0)).
        { intros off Hoff. apply ZC. rewrite u64 by lia. lia. }
        apply obj_holds_frame_lit; rewrite ?B; try exact HromC; try lia.
        - cells_inside_tac.
        - intros off Hoff. unfold Glue.wok_of, Glue.rd_of. rewrite (ZB off Hoff). split; [reflexivity | eexists; reflexivity].
        - unfold cells_in_view. apply Forall_forall. intros [[off k] vv] Hin j Hj.
          assert (HH : vv = SLit 0 /\ 0 <= off /\ off + Z.of_nat k <= 64 /\ (k <= 8)%nat).
          { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; injection E as <- <- <-; (split; [reflexivity|cbn; lia]). }
          destruct HH as (-> & O1 & O2 & K8). unfold Glue.rd_of. cbn [eval]. rewrite <- Z.add_assoc, (ZB (off + Z.of_nat j) ltac:(lia)). rewrite nth_enc_bytes by lia. f_equal. f_equal. symmetry. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
      Qed.
      Lemma views_at (m1 m2 : word -> option byte) x : ltac2:(tb__ "0|1|
S3SbS90Q8A1A1M0Vm1;Vx;A1Vm2;Vx;A1A3S4S3SdSe5S1bVm1;Vx;A3Se5S1bVm2;Vx;A3A3S3G0Se4S1bVm1;Vx;A3Se4S1bVm2;Vx;A3A3A2F_;").
      Proof using . intros E. unfold Glue.wok_of, Glue.rd_of. rewrite E. auto. Qed.
      Lemma hold_tailK T : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S2fS1bVrhoC;S155VmsK;S26VrhoC;A1A2Sa7A4F_;").
      Proof using Erd Evm Ewok HGOK HI HMI Hav Hbrk Hev Hgd HsmK MC VC.
        pose proof HromC as HromC. clear HsmK ZC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
        assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
        assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
        assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
        pose proof (area_R T HinT) as (RT1 & RT2 & RT3). top_ranges.
        assert (B : bv_unsigned (eval rhoC (v 186)) = zA T) by (rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT; cbn [optrZ]; apply u64; lia).
        assert (NG : forall off, 8 <= off < 16 -> ~ (PZ <= zA T + off < PZ + 4096)).
        { intros off Hoff G.
          apply (B_page_vs_footprint (LMem T, PGSZ) (zA T + off) (e_area_In s T HinT)); [|unfold PGSZ; exact G]. cbn [fst snd]. unfold zA, addr_of in *. unfold PGSZ. clear - Hoff. lia. }
        assert (MEQ : forall off, 8 <= off < 16 -> rm rhoC (Z_to_bv 64 (zA T + off)) = mW (Z_to_bv 64 (zA T + off))).
        { intros off Hoff. apply MC. rewrite u64 by lia. exact (NG off Hoff). }
        assert (C0 : In (MCell (LMem (padd T 8)) 8 (optr None)) (image s)).
        { unfold image. apply in_app_iff. right. apply in_app_iff. left.
          rewrite ET. clear - Hne. induction (st_areas s) as [|a0 t0 IH]; [exfalso; exact (Hne eq_refl)|].
          cbn [areas_cells last]. destruct t0 as [|b0 t'].
          - apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. right. left. reflexivity.
          - apply in_app_iff. right. apply IH. discriminate. }
        assert (A0 : loc_addr L (mc_loc (MCell (LMem (padd T 8)) 8 (optr None))) = zA T + 8) by (cbn [mc_loc]; unfold zA, addr_of, loc_addr; destruct T; cbn [padd]; lia).
        change O_tail with (carved (v 186) 8 16 [(8, 8%nat, SLit 0)]).
        apply obj_holds_frame_lit; rewrite ?B; try exact HromC; try lia.
        - cells_inside_tac.
        - intros off Hoff. destruct (views_at (rm rhoC) mW (Z_to_bv 64 (zA T + off)) (MEQ off Hoff)) as [-> ->].
          exact (cell_rw0 _ 0 (zA T) 8 8 C0 eq_refl eq_refl A0 (zA T + off) ltac:(lia)).
        - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
          replace (zA T + 8 + Z.of_nat j) with (zA T + (8 + Z.of_nat j)) by lia.
          destruct (views_at (rm rhoC) mW (Z_to_bv 64 (zA T + (8 + Z.of_nat j))) (MEQ (8 + Z.of_nat j) ltac:(lia))) as [_ ->].
          replace (zA T + (8 + Z.of_nat j)) with (zA T + 8 + Z.of_nat j) by lia.
          apply (cell_view0 _ 0 (zA T) 8 8 (SLit 0) C0 eq_refl eq_refl ltac:(lia) A0); [reflexivity | exact Hj].
      Qed.

      Definition rhoE : valuation := rho_sub rhoC subC.
      Lemma LC_objs_miss o : ltac2:(tb__ "0|1|
Se1S20Vo;S2aSc5A1A3S3eS28VrhoC;Vo;A2SaS0S0S103VL;Vrb;Vpb;A3M0S5cG0Z1000A2A4A2F_;").
      Proof using EmW Evm HGOK HI HMI Hav Hbrk Hev Hgd Hsm_pre Htop Htp VC. exact (LC_objs_missX rhoC VC o). Qed.

      Lemma enter_first : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S14S69A1A3S2bS1bS18fSa4S1bSa2Sb4A3SaScSe6A1Sf9Vtr;SfaVmsK;Sc8A2A4A4F_;").
      Proof using EmW Evm HGOK HI HMI Hav Hbrk Hev Hgd HsmK Hsm_pre Htop Htp VC ZC.
        intros HT. unfold rhoE. apply (entails_sound segsU srcF _ subC rhoC _ entF).
        unfold srcF. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [| |vm_compute; reflexivity].
        - apply (smatch_extend_objs segsU rhoC LC tr msK md2 [pageK] (ss_next LC) HsmK swfF).
          + constructor; [apply hold_pageK | constructor].
          + constructor; [|constructor]. apply Forall_forall. intros o' Ho'. rewrite pageK_range.
            pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
          + cbn. split; [constructor | exact I].
        - constructor; [|constructor]. cbn [SymState.holds]. unfold branch_taken, bv_eqb. rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ eval]. reflexivity.
      Qed.
      Lemma area_aligned a0 : ltac2:(tb__ "0|0|
Se1S69Va0;S70Vs;A1A3S3S0S61S100VL;Va0;A2Z1000A2Z0A3F_;").
      Proof using HI HMI.
        clear HsmK ZC MC VC. intros Ha. pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a0 Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
        pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
        subst a0. unfold zA, addr_of, loc_addr. cbn [padd prid poff]. clear - Hoo RA. unfold PGSZ in *. Z.to_euclidean_division_equations; lia.
      Qed.
      Lemma tail_range T : ltac2:(tb__ "0|3|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S4S3SeS0S0A2S28VrhoC;Sa7A2SaS0S0S5cS100VL;VT;A2M0Z8M1A2S5cG0Z10A2A4A3S4Se1S69VT;S70Vs;A1A3S4S5bZ1000M2G0A2S4S5bS5cG0G2A2S96VL;A1A2S3S0S61G0G1A2Z0A3A2A2A2A2F_;").
      Proof using HI HMI Hav Hev Hgd VC mW.
        clear HsmK ZC MC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
        assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
        assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
        assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
        pose proof (area_R T HinT) as (RT1 & RT2 & RT3 & _). top_ranges. pose proof (area_aligned T HinT) as AL.
        split; [|split; [exact HinT|split; [exact RT1|split; [exact RT2|clear - AL; Z.to_euclidean_division_equations; lia]]]].
        unfold obj_range, obj_lo_of, obj_hi_of, O_tail. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
        rewrite (evC rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ]. rewrite u64 by lia. reflexivity.
      Qed.
      Lemma enter_next T : ltac2:(tb__ "0|0|
S3SbS69A1S6dVs;A1S12S69VT;A2A3S2bS1bS18fSa4S1bSa2Sb5A3SaScSe6A1Sf9Vtr;SfaVmsK;Sc8A2A4A4F_;").
      Proof using EmW Erd Evm Ewok HGOK HI HMI Hav Hbrk Hev Hgd HsmK Hsm_pre Htop Htp MC VC ZC.
        pose proof HsmK as SMC. pose proof (hold_tailK T) as HTK. pose proof hold_pageK as HPK. clear HsmK ZC. intros HT. pose proof (tail_range T HT) as (RT & HinT & T1 & T2 & T3).
        pose proof pz_facts as (P1 & P2 & P3 & P4).
        unfold rhoE. apply (entails_sound segsU srcN _ subC rhoC _ entN).
        unfold srcN. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [| |vm_compute; reflexivity].
        - apply (smatch_extend_objs segsU rhoC LC tr msK md2 [pageK; O_tail] (ss_next LC) SMC swfN).
          + constructor; [apply HPK | constructor; [exact (HTK HT) | constructor]].
          + constructor; [|constructor; [|constructor]]; apply Forall_forall; intros o' Ho'.
            * rewrite pageK_range. pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
            * rewrite RT. pose proof LC_misc as (_ & _ & _ & EO & _).
              assert (RO : In (obj_range rhoC o') ((sp0 + D0, sp0) :: [(167248, 167256); (369464, 369472); (369504, 369512); (369544, 369552); (237612, 237616); (369616, 369628); (369632, 369696); (370536, 370544)])).
              { rewrite EO in Ho'. destruct Ho' as [<-|Ho']; [left; symmetry; exact (stk_range rhoC VC)|]. right. rewrite <- (statics_ranges rhoC VC).
                apply in_app_iff in Ho' as [Ho'|Ho']; [apply in_map; unfold N_BK in Ho' |- *; cbn [firstn In] in Ho' |- *; tauto|].
                destruct Ho' as [<-|[<-|[]]].
                - change (obj_range rhoC O_ctxC) with (obj_range rhoC (O_ctxB AM_P (SLit 0) (v 176) (SLit 0) (SLit 0) (v 184) (v 185) (v 186) (v 177))). apply in_map. unfold N_BK; cbn [In]; tauto.
                - change (obj_range rhoC O_brkC) with (obj_range rhoC (O_brk AM_P (v 187))). apply in_map. unfold N_BK; cbn [In]; tauto. }
              pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
              assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
              destruct (AllocMetaArea.fp_where s L C_U vm HV HLG (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as [[E _]|(pp & _ & _ & NI)]; [discriminate|].
              cbn [mc_img_lo mc_img_hi C_U] in NI. clear - RO S2 T1 T2 NI. top_ranges.
              unfold SymState.ranges_disjoint. cbn [fst snd].
              destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|].
              repeat (destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|]). destruct RO.
          + cbn. split; [constructor; [|constructor]|split; [constructor|exact I]].
            rewrite pageK_range, RT. unfold SymState.ranges_disjoint. cbn [fst snd].
            assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
            pose proof (B_page_vs_footprint (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as NG. unfold PGSZ in NG. cbn [fst snd] in NG.
            pose proof (area_aligned T HinT) as AT. clear - NG AT P1. unfold U.Mal_ameta__G1.Mal_ameta_I.zA, addr_of in *. Z.to_euclidean_division_equations; lia.
        - pose proof (evC rhoC (v 186) VC eq_refl) as E186. rewrite ev186, HT in E186. cbn [optrZ] in E186. change (v 186) with (SVar 186) in E186. cbn [eval] in E186.
          assert (U186 : bv_unsigned (Z_to_bv 64 (zA T)) = zA T) by (apply u64; clear - T1 T2; top_ranges; lia).
          clear MC.
          unfold nz_fact. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds eval v]; rewrite ?E186, ?U186.
          + unfold branch_taken, bv_eqb. rewrite ?U186. change (bv_unsigned (Z_to_bv 64 0)) with 0. replace (zA T =? 0) with false by (symmetry; apply Z.eqb_neq; clear - T1; lia). discriminate.
          + split; [clear; lia|]. change (2 ^ 3) with 8. exact T3.
          + change (bv_unsigned (Z_to_bv 64 (2 ^ 47))) with (2 ^ 47). clear - T2. top_ranges. lia.
          + change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact T1.
      Qed.
    End AtCut.

    Local Abbreviation W184 := (st_meta_alloc_shift s).
    Local Abbreviation VALF := (U.Mal_ameta__G2.Mal_ameta_C2E.valF s L rho gd evb avb mW PZ 1 W184 (PZ + 4096)).
    Definition GRb (x : Z) : Prop := ltac2:(tb__ "0|1|
S4S5bS103VL;Vrb;Vpb;A3M0Vx;A2S5dVx;S5cG0Z1000A2A2A2").

    Lemma valF_enter rhoC : ltac2:(tb__ "0|1|
S111VrhoC;A1S18aVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;S103VL;Vrb;Vpb;A3M0Z1S78Vs;A1S5cG0Z1000A2S17fVrhoC;Sc9A2AcF_;").
    Proof using HI HMI Hav Hbrk Hev Hgd Hinit.
      intros VC. pose proof VC as (A1 & A2 & A3). pose proof LC_misc as (_ & _ & E9 & _ & SUBOK).
      assert (LOW : forall j, (Z.pos j < 200) -> j <> 183%positive -> j <> 187%positive -> rw (rho_sub rhoC subC) j = rw rhoC j).
      { intros j Hj N1 N2. cbn [rho_sub rw]. rewrite wsub_get_miss; [reflexivity|].
        apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq. unfold subC in Hp.
        repeat (destruct Hp as [<-|Hp]; [cbn [fst]; first [lia | exact N1 | exact N2] |]). destruct Hp. }
      split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - intros j Hj. rewrite LOW by lia. rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
      - intros j Hj. cbn in Hj.
        assert (Hj' : (Z.pos j < 200) /\ j <> 183%positive /\ j <> 187%positive).
        { repeat (destruct Hj as [<-|Hj]; [split; [lia | split; discriminate]|]). destruct Hj. }
        destruct Hj' as (H1 & H2 & H3). rewrite (LOW j H1 H2 H3). rewrite <- (A1 j) by (unfold AM_NEXT; lia). reflexivity.
      -   rewrite LOW by first [lia | discriminate]. rewrite <- (A1 175%positive) by (unfold AM_NEXT; lia). transitivity (Z_to_bv 64 secZ); [exact (rw1_v 175 _ eq_refl) | unfold U.Mal_ameta__G1.Mal_ameta_I.secZ; rewrite Hinit; reflexivity].
      - unfold rho_sub. cbn [rw]. change (wsub_get subC 201) with (reg_sv LC 9). rewrite E9. exact (evC187 rhoC VC).
      - unfold rho_sub. cbn [rw wsub_get subC Pos.eqb fst snd]. reflexivity.
      - rewrite LOW by first [lia | discriminate]. rewrite <- (A1 184%positive) by (unfold AM_NEXT; lia). cbn [rho1 rw]. exact (rw1_v 184 _ eq_refl).
      - unfold rho_sub. cbn [rw wsub_get subC Pos.eqb fst snd]. exact (evC187p rhoC VC).
      - intros l. unfold rho_sub. cbn [rl]. rewrite <- A2. reflexivity.
    Qed.

    Lemma R_HF : ltac2:(tb__ "0|6|
S4S3ScS69A1S70S105Vs;Vrb;Vpb;A3M0A1S11S69S70Vs;A1S9S69S107Vrb;Vpb;A2M1S10S69A1A3A3A3S4S3SdS6eG0A1SfA3S4S3SbS69A1M2S6cG0A1S14S69A1A3S4S3S69S8cG0A1S75S106Vrb;Vpb;A2S89A2A3S4S3S0S71G0A1S63S88Z1M3A2A3S4S3S0S6bG0A1S63G3G3A2A3S4S3S0S78G0A1S78Vs;A1A3S4S3G2S86G0A1G2G2Lx;S86Vs;A1S69S12S69R1A2Ls0;S12S69G1A2M4Xbx2A3S4S3G2S6dG0A1G4A3S4S3S69S8dG0A1S75G1Z1000A2A3S4S3ScG2A1S76G0A1S76Vs;A1A3S4S3ScS0A1M5S7dG0A1S7dVs;A1A3S4S3G5S7cG0A1S7cVs;A1A3S4S3G5S77G0A1S77Vs;A1A3S4S3S0S7bG0A1S7bVs;A1A3S3S0S79G0A1S79Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
    Proof using HI HMI HXr Hac Hbrk Hcnt Hhd Hinit. pose proof B_tB_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). repeat split; assumption. Qed.
    Lemma R_brk2 : ltac2:(tb__ "0|0|
S3S0S14dVL;S189S105Vs;Vrb;Vpb;A3A1A2S5cS103VL;Vrb;Vpb;A3Z1000A2A3").
    Proof using HI HMI HXr Hac Hav Hbrk Hcnt Hev Hgd Hhd Hinit.
      unfold U.Mal_ameta__G2.Mal_ameta_C2E.brk_sval. pose proof B_tB_fields as (_ & _ & _ & F4 & _). rewrite F4. cbn [sval_num loc_addr]. unfold AllocMetaBrk.pz, PGSZ. lia.
    Qed.
    Lemma R_V183 : 1 <= 1 < 2 ^ 62. Proof using Hav Hev Hgd. lia. Qed.
    Lemma R_V184 : 0 <= W184 < 2 ^ 62. Proof using HMI Hav Hev Hgd. pose proof HB as (_ & SH & _). lia. Qed.
    Lemma R_mnew : ltac2:(tb__ "0|0|
S3S69S106Vrb;Vpb;A2S75S107Vrb;Vpb;A2Z18A2A3"). Proof using . reflexivity. Qed.
    Lemma R_Lext : ltac2:(tb__ "0|0|
Sf8VL;VL;S19S6aS7aVs;A1A2A3"). Proof using . apply layout_extends_refl. Qed.
    Lemma R_Lctx : ltac2:(tb__ "0|1|
S3S0S144VL;A1M0G0A3"). Proof using . reflexivity. Qed.
    Lemma R_Lsec : ltac2:(tb__ "0|1|
S3S0S149VL;A1M0G0A3"). Proof using . reflexivity. Qed.
    Lemma R_Lfp : ltac2:(tb__ "0|2|
SeS13aS0A2M0Se1G0R1S13dVs;A1A3S3S0S13cVL;S13S13aS0R2A3A2M1G1A3F_;Fe;"). Proof using . reflexivity. Qed.
    Lemma R_Lub : ltac2:(tb__ "0|2|
SeS69S0A2M0Se1G0R1S14eVs;A1A3S3S0S13cVL;S145S13S69S0R2A3A1A2M1G1A3F_;Fb;"). Proof using . reflexivity. Qed.
    Lemma R_Lold : ltac2:(tb__ "0|1|
S69S154S8bR1A1S19S6aS7aVs;A1A2A2S3S0S9fVL;R2A2M0G0A3F_;Fq;"). Proof using . reflexivity. Qed.
    Lemma R_pzR : ltac2:(tb__ "0|3|
S4S5bZ1000M0S103VL;Vrb;Vpb;A3M1A2S4S5bS5cG1G0A2S96VL;A1A2S4S3S0S61G1G0A2Z0M2A3S4S5bG2G1A2S5dG1S5eZ2Z40A2A2A2A2A2A2").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. pose proof pz_facts as (P1 & P2 & P3 & P4). repeat split; lia. Qed.
    Lemma R_cw2 c x : ltac2:(tb__ "0|5|
Se1S13bVc;S11S13bS13eS105Vs;Vrb;Vpb;A3M0A1S15eG0A1A3A3S4S5bS13cVL;S14aVc;A1A2M1Vx;A2S5dVx;S5cG1S5fS14bVc;A1A1A2A2A2S7S6SeS13aS0A2M2G2S4Se1G2R1S13dVs;A1A3S4S5bS13cVL;S13S13aS0R1A3A2M3Vx;A2S5dVx;S5cG3S16S13aS0R1A3A2A2A2A2Le;A2S4S5bS103VL;Vrb;Vpb;A3M4Vx;A2S5dVx;S5cG4Z1000A2A2A2A2F_;F_;").
    Proof using HI HMI HXr Hac Hav Hbrk Hcnt Hev Hgd Hhd Hinit. intros Hc Hx. destruct (B_cell_whereB c x Hc Hx) as [H|H]; [left; exact H | right; unfold PGSZ in H; lia]. Qed.
    Lemma R_GRdec x : ltac2:(tb__ "0|1|
S16eSc6Vx;A1M0S5G0A1A2"). Proof using . unfold GRb. apply range_dec. Qed.
    Lemma R_GRpage x : ltac2:(tb__ "0|1|
S4S5bS103VL;Vrb;Vpb;A3M0Vx;A2S5dVx;S5cG0Z1000A2A2A2Sc6Vx;A1F_;"). Proof using . intros H. exact H. Qed.
    Lemma R_GRimg x : ltac2:(tb__ "0|0|
Sc6Vx;A1S5S4S5bSa1S94A1Vx;A2S5dVx;Sa0S94A1A2A2A1F_;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. intros G Hi. apply (B_page_vs_image x Hi). unfold PGSZ. exact G. Qed.
    Lemma R_GRfp e x : ltac2:(tb__ "0|1|
Se1SeS13aS0A2Ve;S13dVs;A1A3S4S5bS13cVL;S13S13aS0Ve;A3A2M0Vx;A2S5dVx;S5cG0S16S13aS0Ve;A3A2A2A2S5Sc6Vx;A1A1F_;F_;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. intros He Hx G. apply (B_page_vs_footprint e x He Hx). unfold PGSZ. exact G. Qed.
    Lemma R_GRceil x : ltac2:(tb__ "0|0|
Sc6Vx;A1S4S5bZ1000Vx;A2S5dVx;S96VL;A1A2A2F_;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. pose proof pz_facts as (P1 & P2 & P3 & P4). unfold GRb. intros G. lia. Qed.
    Lemma R_GRmaps k rg x : ltac2:(tb__ "0|1|
S3SbS6aA1S13fVs;Vk;A2S12S6aVrg;A2A3S3SdS84Vrg;A1SfA3S3S85S82Vrg;A1S80A3S4S5bS142VL;Vk;A2M0Vx;A2S5dVx;S5cG0S83Vrg;A1A2A2A2S5Sc6Vx;A1A1F_;F_;F_;F_;").
    Proof using Evm HGOK HI HMI Hav Hbrk Hev Hgd. intros Hk Hl Hkd Hx G. apply (B_map_region_vs_page k rg x Hk Hl Hkd Hx). unfold PGSZ. exact G. Qed.
    Lemma R_GRblock b n x : ltac2:(tb__ "0|0|
Se1SeS0S0A2SaS0S0Vb;Vn;A4S98VL;Vs;A2A3S4S5bVb;Vx;A2S5dVx;S5cVb;Vn;A2A2A2S5Sc6Vx;A1A1F_;F_;").
    Proof using Evm HGOK HI HMI HXr Hav Hbrk Hev Hgd. intros Hin Hx G. apply (B_page_vs_block b n x Hin Hx). unfold PGSZ. exact G. Qed.
    Lemma R_notX : ltac2:(tb__ "0|1|
S4S3SdS14cS106Vrb;Vpb;A2M0VX;A2S17A3Se1S69G0S141S105Vs;Vrb;Vpb;A3A1A3A2"). Proof using HI Hac Hbrk Hcnt Hhd. pose proof B_bm_notX as (A & B & _). auto. Qed.
    Lemma R_Y : ltac2:(tb__ "0|2|
S140SeSbS69A1M0S6fA2S74Vs;A1S185Vs;Z1Z0M1G1A4SaG0S6fS12S69S106Vrb;Vpb;A2A2S105Vs;Vrb;Vpb;A3A4A4").
    Proof using Hac Hbrk Hcnt Hhd. pose proof (yields_BK s Hhd Hcnt Hac rb pb Hbrk 1 0 0) as Y. unfold r_BK in Y. cbn [Z.eqb] in Y. exact Y. Qed.

    Local Ltac c2e_args tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_sound s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc ok md2 B_vmB HOK K2 vm2_eq STK (smatch_facts_hold segsU _ _ _ Hsm_pre) B_tB L B_bp B_bm PZ 1 W184 (PZ + 4096) (tr_BK s 1 0 0)
             B_HIB B_xraw_tB B_layout_ok_tB B_vm_ok_tB (proj1 B_ledger_tB) (proj2 (proj2 B_ledger_tB)) B_bounded_tB B_maps_wf_tB
             R_HF R_brk2 R_V183 R_V184 B_image_tB B_ctx_cells_tBC B_area_cells_tB B_fresh_slot B_bp_fresh R_mnew B_fp_tB B_ub_tB
             R_Lext R_Lctx R_Lsec R_Lfp R_Lub R_Lold B_pz_eq B_bm_addr R_pzR R_cw2
             GRb R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock (AllocMetaArea.block_where X R U s L HI HXr) (AllocMetaArea.fp_where s L C_U vm HV HLG)
             R_notX B_keys_tB B_am_frame_tB R_Y).

    Theorem okc_sound : ltac2:(tb__ "0|0|
S15S109S32S10bS1bVok;R3S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw';A4S111R2A1S11aS26R3A1A1S11bS26R4A1A1S156S1bS157SffVtr;Sc8A2A1Sa4S1bSa2Sb7A3R5R6A5S10cS1bVok;R8R7A4F_;F_;F_;F_;F_;FrhoZ;Fw;Fn;").
    Proof using EmW Erd Evm Ewok HGOK HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
      intros n w rhoZ HQ VZ MZ ZZ Hw.
      pose proof (alloc_meta_run_P AC_brk_ok ok (Kexact tr md2) rhoZ (ok_frame_exact ok Kc tr md2 HOK K2)) as RUN1.
      refine (RUN1 n _ w Hw).
      intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC' & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape AC_brk_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_ok) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (valC_ext rhoZ rhoC AM_NEXT VZ ltac:(lia) HagC) as VC.
      assert (MC : memC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
      assert (ZC : zeroC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
      pose proof (valF_enter rhoC VC) as VE.
      assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2) ->
                   Safety.safe segsU ok n (tr, mkCfg ms1 md2)).
      { intros HE. c2e_args ltac:(fun t => apply (t n ms1 (rho_sub rhoC subC) HQ VE)); [| |exact HE].
        - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
        - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
      apply GO. unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
      - exact (enter_next ms1 rhoC VC MC ZC HsmC' T HT).
      - exact (enter_first ms1 rhoC VC ZC HsmC' HT).
    Qed.

    Local Ltac c2e_ex_args tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_ex s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc md2 B_vmB K2x vm2_eq STK (smatch_facts_hold segsU _ _ _ Hsm_pre) B_tB L B_bp B_bm PZ 1 W184 (PZ + 4096) (tr_BK s 1 0 0)
             B_HIB B_xraw_tB B_layout_ok_tB B_vm_ok_tB (proj1 B_ledger_tB) (proj2 (proj2 B_ledger_tB)) B_bounded_tB B_maps_wf_tB
             R_HF R_brk2 R_V183 R_V184 B_image_tB B_ctx_cells_tBC B_area_cells_tB B_fresh_slot B_bp_fresh R_mnew B_fp_tB B_ub_tB
             R_Lext R_Lctx R_Lsec R_Lfp R_Lub R_Lold B_pz_eq B_bm_addr R_pzR R_cw2
             GRb R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock (AllocMetaArea.block_where X R U s L HI HXr) (AllocMetaArea.fp_where s L C_U vm HV HLG)
             R_notX B_keys_tB B_am_frame_tB R_Y).

    Theorem okc_ex : forall (w : world) (rhoZ : valuation),
      valC rhoZ -> memC (rm rhoZ) -> zeroC (rm rhoZ) ->
      SPJ segsU (liftK (Kexact tr md2)) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_ok) rhoZ w ->
      etriple segsU (fun w' => w' = w)
        (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2).
    Proof using EmW Erd Evm Ewok HGOK HI HKc HMI HVI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
      intros w rhoZ VZ MZ ZZ Hw w0 ->.
      destruct (alloc_meta_run_ex_P AC_brk_ok (Kexact tr md2) rhoZ w Hw)
        as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoC & HinL & HagC & HsmC' & HK1).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape AC_brk_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC'. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC'.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_ok) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (valC_ext rhoZ rhoC AM_NEXT VZ ltac:(lia) HagC) as VC.
      assert (MC : memC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MZ x Hx)).
      assert (ZC : zeroC (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZZ x Hx)).
      pose proof (valF_enter rhoC VC) as VE.
      assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2) ->
                   etriple segsU (fun w' => w' = (tr, mkCfg ms1 md2))
                     (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = md2)).
      { intros HE. c2e_ex_args ltac:(fun t => apply (t ms1 (rho_sub rhoC subC) VE)); [| |exact HE].
        - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
        - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
      assert (HE : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 md2)).
      { unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
        - exact (enter_next ms1 rhoC VC MC ZC HsmC' T HT).
        - exact (enter_first ms1 rhoC VC ZC HsmC' HT). }
      destruct (GO HE (tr, mkCfg ms1 md2) eq_refl) as (w3 & ST3 & HQ3).
      exists w3. split; [eapply wsteps_trans; [exact ST1 | exact ST3] | exact HQ3].
    Qed.
  End Granted.

  Definition LBF0 : sstate := ltac2:(tb__ "0|0|
S15aSe3S159S15bSa4S1bSa2SbaA3S158A2Sa8SbaA1A3A1").
  Definition LBF : sstate := ltac:(let x := eval vm_compute in LBF0 in exact x).
  Lemma LBF_eq : LBF0 = LBF. Proof using . vm_cast_no_check (@eq_refl sstate LBF). Qed.
  Definition O_ctxD : sobj := ltac2:(tb__ "0|1|
SaeSa2S23Z0A1M0Sa3Pb0A1G0G0Sa3Pb8A1Sa3Pb9A1Sa3PbaA1Sa3Pb1A1A9").
  Definition O_brkD : sobj := ltac2:(tb__ "0|0|
SadSa2S23Sb8A1A2").
  Definition UNCH_F : list sobj := ltac2:(tb__ "0|0|
S9S20Sb0Sa2A1S9S20Sb1S9S20SacSa2A1S9S20Sb2Sa2A1S9S20SafS9S20Sb3Sa2Sa3PafA1Z1A3S9S20S118S10S20A1A3A3A3A3A3A3A3").
  Definition CHG_F : list sobj := [O_brkD].
  Lemma LBF_misc : ltac2:(tb__ "0|0|
S4S3S0S2eS10fA1Z20dd0A3S4S3S1S2cS10fA1P12dA3S3ScS20A1S2aS10fA1S9S20Sa6S114A1S11S20S110S112A3A3A3A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.

  Definition subBF : list (positive * sv) := ltac2:(tb__ "0|1|
S9SeS1S21A2M0SaS1S21PccS22S10fZ1A2A4S9G0SaS1S21PcdS22S10fZ5A2A4S9G0SaS1S21PceS22S10fZ6A2A4S9G0SaS1S21PcfS22S10fZ7A2A4S9G0SaS1S21Pd1S22S10fZ9A2A4S9G0SaS1S21Pd3S22S10fZbA2A4S9G0SaS1S21Pd4S22S10fZcA2A4S9G0SaS1S21Pd5S22S10fZdA2A4S9G0SaS1S21Pd6S22S10fZeA2A4S9G0SaS1S21Pd7S22S10fZfA2A4S9G0SaS1S21Pd8S22S10fZ10A2A4S9G0SaS1S21Pd9S22S10fZ11A2A4S9G0SaS1S21PdcS22S10fZ14A2A4S9G0SaS1S21Pe4S22S10fZ1cA2A4S9G0SaS1S21Pe5S22S10fZ1dA2A4S9G0SaS1S21Pe6S22S10fZ1eA2A4S9G0SaS1S21Pe7S22S10fZ1fA2A4S9G0SaS1S21PbbS23Sb8A1A4S10G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Lemma entBF : ltac2:(tb__ "0|0|
S3SdS15dSa9S10fSc1A2Sa4S1bSa2SaaA3S116A3SfA3").
  Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma subBF_ok : ltac2:(tb__ "0|2|
S4S3SdSe2SeS1S21A2M0G0S1aS60Zc8S2S13S1S21R1A3M1A1A2S162G1PbbA2A2Lp;S116A3SfA3S3SdSe2G0G0S3fP12cS16S1S21R1A3A2Lp;S116A3SfA3A2").
  Proof using . vm_compute. split; reflexivity. Qed.

  Lemma agree_set300 (rhoL : valuation) (b : word) : ltac2:(tb__ "0|0|
S33Sa5VrhoL;S176VrhoL;Sa5Vb;A3A3").
  Proof using Hav Hev Hgd.
    split; [|split; [intros l; reflexivity | intros x; reflexivity]].
    intros i Hi. cbn [rho_set_rw rw]. destruct (Pos.eqb i AM_NEXT) eqn:E; [apply Pos.eqb_eq in E; exfalso; unfold AM_NEXT in *; lia | reflexivity].
  Qed.
  Lemma valC_set300 (rhoL : valuation) (b : word) : ltac2:(tb__ "0|0|
S111VrhoL;A1S111S176VrhoL;Sa5Vb;A3A1F_;").
  Proof using Hav Hev Hgd. intros VL. exact (valC_ext rhoL _ AM_NEXT VL ltac:(lia) (agree_set300 rhoL b)). Qed.
  Lemma in_range_pz (x : word) : ltac2:(tb__ "0|5|
S8S3SdS195S91Q40M0S103VL;Vrb;Vpb;A3M1A2M2S93G0S91G0S5cG1Z1000A2M3A2G2A3Vx;A3SfA3S4S5bG1S92G0Vx;A2M4A2S5dG4G3A2A2A2").
  Proof using HI HMI Hav Hbrk Hev Hgd.
    pose proof pz_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    rewrite in_range_spec. rewrite bv_sub_unsigned, (u64 PZ), (u64 (PZ + 4096)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma ne_req_holds (rhoL : valuation) (b : word) : ltac2:(tb__ "0|0|
S111VrhoL;A1S3S0S92Q40Vb;A2S103VL;Vrb;Vpb;A3A3S12cS29S3cS176VrhoL;Sa5Vb;A3A1Sc3S113P12cA2A3F_;F_;").
  Proof using HI HMI Hav Hbrk Hev Hgd mW.
    intros VL Hb. pose proof pz_pre as (P1 & P2 & P3 & P4 & _). top_ranges.
    assert (E300 : eval (rho_set_rw rhoL AM_NEXT b) (SVar 300) = b) by reflexivity.
    assert (E9 : eval (rho_set_rw rhoL AM_NEXT b) (reg_sv LBE 9) = Z_to_bv 64 (PZ + 4096)).
    { replace (reg_sv LBE 9) with (SAlu ALU_ADD (SVar 187) (SLit 4096)) by (vm_compute; reflexivity).
      rewrite <- (eval_agree AM_NEXT rhoL (rho_set_rw rhoL AM_NEXT b) (SAlu ALU_ADD (SVar 187) (SLit 4096)) (agree_set300 rhoL b) eq_refl). exact (evC187p rhoL VL). }
    unfold ne_req. constructor; [|constructor; [|constructor]]; cbn [SymState.holds]; unfold branch_taken, bv_eqb; rewrite E300, E9, Hb, (u64 (PZ + 4096)) by lia;
      replace (PZ =? PZ + 4096) with false by (symmetry; apply Z.eqb_neq; lia); [discriminate | reflexivity].
  Qed.

  Definition FAILC : assn := ltac2:(tb__ "0|1|
S109S6S17aS17aS6S32S32S4S3S109R3SaScSe6A1Sf9Vtr;SfaR2Vmd;A2A4M0A3S4S111R1A1S4S90Q40A1S3SbS90Q8A1A1S26R2R1A2VmW;R1A1A3Fx;S2bS1bR1S10fG0A4A2A2A2LrhoF;A2LmsF;A2Lw;").

  Theorem bk_chain : ltac2:(tb__ "0|0|
S15S10bS1bVok;R1S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw;A4S10bS1bVok;R2S117A4S10cS1bVok;R3SaScSe6A1Sf9Vtr;SfaVms;Vmd;A2A4A4F_;F_;Fn;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    intros n HQ HFC.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof pz_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof pz_pre as pz_pre'.
    pose proof (alloc_meta_run_P AE_brk ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg ms md) (conj entry_BK (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1]] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AE_brk) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LBE) by (rewrite <- LBE_eq; unfold LBE0; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_brk) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
    destruct n as [|m]; [exact I|].
    pose proof LBE_misc as (Mpc & M17 & M10 & Mnx & Mobjs).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    pose proof (evC187p rhoL VL) as E10.
    assert (EB : vm_brk (m_vmmaps md) = Z_to_bv 64 PZ) by (rewrite <- Evm, <- P5; symmetry; apply Z_to_bv_bv_unsigned).
    refine (triple1_brk_growJ segsU ok (liftK (Kexact tr md)) (liftK (Kexact tr md))
              (fun _ tr' md' => tr' = tr /\ md' = with_vmmaps (brk_model_next (m_vmmaps md) (Z_to_bv 64 (PZ + 4096)) (Z_to_bv 64 (PZ + 4096))) md
                                 /\ brk_grow_ok md (Z_to_bv 64 (PZ + 4096)) (Z_to_bv 64 (PZ + 4096)) = true)
              LBE rhoL (vm_brk (m_vmmaps md)) (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) (ok_pframe_exact md HKc) LBE_ecall M17 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL LBE tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      change (10 + Z.of_nat 0) with 10 in G0. rewrite M10, E10 in G0.
      clear Hsp HsmL RUN1 HQ HFC ELF EP. rewrite G0, EB. clear G0.
      rewrite (u64 PZ) by lia. rewrite (u64 (PZ + 4096)) by (top_ranges; lia).
      split; [reflexivity|]. split; [rewrite <- Evm; exact P6|].
      split; [unfold page_size; exact P1|]. split; [unfold page_size; rewrite <- Z.add_mod_idemp_l, P1 by lia; reflexivity|].
      split; [lia|]. split; [split; reflexivity|].
      intros HG. split; [|split; [|split; [reflexivity | split; [reflexivity | exact HG]]]].
      + rewrite Mobjs. exact (LBE_objs_miss HG rhoL VL).
      + intros x Hx. exact (ro_addr_page HG x Hx).
    -
      intros w2 [HF2 | HO2].
      +
        destruct w2 as [tr2 [ms2 md2']]. destruct HF2 as [Hsm2 HK2]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
        set (rhoL' := rho_set_rw rhoL (ss_next LBE) (vm_brk (m_vmmaps md))) in *.
        assert (Hsm2' : smatch segsU rhoL' (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_fail) (tr, mkCfg ms2 md)).
        { rewrite Pre_fail_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm2 | | vm_compute; reflexivity].
          subst rhoL'. rewrite Mnx. apply (ne_req_holds rhoL _ VL). rewrite EB. exact (u64 PZ (proj1 (proj2 (proj2 (proj2 pz_pre'))))). }
        pose proof (alloc_meta_run_P AC_brk_fail ok (Kexact tr md) rhoL' (ok_frame_exact ok Kc tr md HOK HKc)) as RUN2.
        refine (RUN2 m _ (tr, mkCfg ms2 md) (conj Hsm2' (conj eq_refl eq_refl))).
        intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
        destruct (Posts_am_P_shape AC_brk_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
        assert (ELF3 : lf_state L3 = LBF) by (rewrite <- LBF_eq; unfold LBF0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
        assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_fail) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
        apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HFC. exists ms3, rhoF. split; [reflexivity|]. split; [|split; [|exact Hsm3]].
        * apply (valC_ext rhoL' rhoF 301); [|unfold AM_NEXT; clear; lia|exact Hag3]. subst rhoL'. rewrite Mnx. exact (valC_set300 rhoL _ VL).
        * intros x. destruct Hag3 as (_ & _ & M). rewrite <- (M x). subst rhoL'. cbn [rho_set_rw rm]. destruct HagL as (_ & _ & ML). rewrite <- (ML x). reflexivity.
      +
        destruct w2 as [tr2 [ms2 md2']]. destruct HO2 as [Hsm2 (Etr & Emd & HG)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm2, Etr, Emd. subst tr2 md2'.
        rewrite <- Pre_ok_eq in Hsm2. rewrite M10, E10, EB in Hsm2.
        refine (okc_sound HG m _ _ (@Safety.guards_mono segsU ok (S m) m _ (Nat.le_succ_diag_r m) HQ) _ _ _ (conj Hsm2 (conj eq_refl eq_refl))).
        * destruct VL as (A1 & A2 & A3). split; [|split; [exact A2 | intros x; reflexivity]]. intros i Hi. cbn [set_rm rw rm rho1]. exact (A1 i Hi).
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          destruct (SysStep.in_range (Z_to_bv 64 PZ) (Z_to_bv 64 (PZ + 4096) - Z_to_bv 64 PZ)%bv x) eqn:E.
          -- exfalso. apply Hx. exact (proj1 (in_range_pz x) E).
          -- destruct HagL as (_ & _ & M). rewrite <- (M x). reflexivity.
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at. rewrite (proj2 (in_range_pz x) Hx). reflexivity.
  Qed.

  Theorem bk_chain_ex : etriple segsU (fun w => w = (tr, mkCfg ms md))
    (fun w => FAILC w \/ LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
  Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Hsm_pre Htop Htp.
    intros w ->. pose proof pz_pre as (P1 & P2 & P3 & P4 & P5 & P6). pose proof pz_pre as pz_pre'.
    destruct (alloc_meta_run_ex_P AE_brk (Kexact tr md) (rho1 mW) (tr, mkCfg ms md) (conj entry_BK (conj eq_refl eq_refl)))
      as ([tr1 [ms1 md1]] & ST1 & Lf & rhoL & HinL & HagL & HsmL & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape AE_brk) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = LBE) by (rewrite <- LBE_eq; unfold LBE0; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AE_brk) = AM_NEXT) by (vm_compute; reflexivity). rewrite NX in HagL.
    pose proof LBE_misc as (Mpc & M17 & M10 & Mnx & Mobjs).
    assert (VL : valC rhoL).
    { destruct HagL as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; reflexivity]]. }
    pose proof (evC187p rhoL VL) as E10.
    assert (EB : vm_brk (m_vmmaps md) = Z_to_bv 64 PZ) by (rewrite <- Evm, <- P5; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (brk_grow_ok md (Z_to_bv 64 (PZ + 4096)) (Z_to_bv 64 (PZ + 4096))) eqn:HG.
    { assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) LBE rhoL)
                      (SPJ segsU (liftK (Kexact tr md2)) (S_after LBE (reg_sv LBE 10) (ss_objs LBE) (ss_next LBE))
                         (set_rm rhoL (zero_range (rm rhoL) (vm_brk (m_vmmaps md)) (bv_sub (eval rhoL (reg_sv LBE 10)) (vm_brk (m_vmmaps md))))))).
      { apply (HeapEx.etriple_brk_grow_okJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md2)) LBE rhoL (vm_brk (m_vmmaps md)) LBE_ecall M17).
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoL LBE tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
        change (10 + Z.of_nat 0) with 10 in G0. rewrite M10, E10 in G0.
        clear Hsp HsmL. rewrite G0, EB. clear G0.
        rewrite (u64 PZ) by lia. rewrite (u64 (PZ + 4096)) by (top_ranges; lia).
        split; [reflexivity|]. split; [rewrite <- Evm; exact P6|].
        split; [unfold page_size; exact P1|]. split; [unfold page_size; rewrite <- Z.add_mod_idemp_l, P1 by lia; reflexivity|].
        split; [lia|]. split; [exact HG|].
        split; [rewrite Mobjs; exact (LBE_objs_miss HG rhoL VL)|].
        split; [intros x Hx; exact (ro_addr_page HG x Hx)|].
        split; reflexivity. }
      destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as ([tr2 [ms2 md2']] & ST2' & [Hsm2 HK2]).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
      rewrite <- Pre_ok_eq in Hsm2. rewrite M10, E10, EB in Hsm2.
      unshelve (epose proof (okc_ex HG (tr, mkCfg ms2 md2) _ _ _ _ (conj Hsm2 (conj eq_refl eq_refl)) (tr, mkCfg ms2 md2) eq_refl) as OK3).
      + destruct VL as (A1 & A2 & A3). split; [|split; [exact A2 | intros x; reflexivity]]. intros i Hi. cbn [set_rm rw rm rho1]. exact (A1 i Hi).
      + intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        destruct (SysStep.in_range (Z_to_bv 64 PZ) (Z_to_bv 64 (PZ + 4096) - Z_to_bv 64 PZ)%bv x) eqn:E.
        * exfalso. apply Hx. exact (proj1 (in_range_pz x) E).
        * destruct HagL as (_ & _ & M). rewrite <- (M x). reflexivity.
      + intros x Hx. cbn [rm set_rm]. rewrite zero_range_at. rewrite (proj2 (in_range_pz x) Hx). reflexivity.
      + destruct OK3 as (w3 & ST3 & HQ3 & _). exists w3. split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
        right. destruct HQ3 as (Lq & JLq & rho' & Hin0 & Hrest). destruct Hin0 as [E0|[]].
        exists Lq, JLq, rho'. split; [right; left; exact E0 | exact Hrest]. }
    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) LBE rhoL)
                                 (SPJ segsU (liftK (Kexact tr md)) (S_ret_fresh LBE) (rho_set_rw rhoL (ss_next LBE) (vm_brk (m_vmmaps md))))).
    { apply (HeapEx.etriple_brk_grow_failJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md)) LBE rhoL (vm_brk (m_vmmaps md)) LBE_ecall M17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL LBE tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      change (10 + Z.of_nat 0) with 10 in G0. rewrite M10, E10 in G0.
      clear Hsp HsmL. rewrite G0, EB. clear G0. rewrite (u64 PZ) by lia. rewrite (u64 (PZ + 4096)) by (top_ranges; lia).
      split; [reflexivity|]. split; [rewrite <- Evm; exact P6|]. split; [lia|]. split; [exact HG|]. split; reflexivity. }
    destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as ([tr2 [ms2 md2']] & ST2' & [Hsm2 HK2]).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK2. destruct HK2 as [-> ->].
    set (rhoL' := rho_set_rw rhoL (ss_next LBE) (vm_brk (m_vmmaps md))) in *.
    assert (Hsm2' : smatch segsU rhoL' (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_fail) (tr, mkCfg ms2 md)).
    { rewrite Pre_fail_eq. apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact Hsm2 | | vm_compute; reflexivity].
      subst rhoL'. rewrite Mnx. apply (ne_req_holds rhoL _ VL). rewrite EB. exact (u64 PZ (proj1 (proj2 (proj2 (proj2 pz_pre'))))). }
    destruct (alloc_meta_run_ex_P AC_brk_fail (Kexact tr md) rhoL' (tr, mkCfg ms2 md) (conj Hsm2' (conj eq_refl eq_refl)))
      as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape AC_brk_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LBF) by (rewrite <- LBF_eq; unfold LBF0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P AC_brk_fail) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
    exists (tr, mkCfg ms3 md). split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
    left. exists ms3, rhoF. split; [reflexivity|]. split; [|split; [|exact Hsm3]].
    - apply (valC_ext rhoL' rhoF 301); [|unfold AM_NEXT; clear; lia|exact Hag3]. subst rhoL'. rewrite Mnx. exact (valC_set300 rhoL _ VL).
    - intros x. destruct Hag3 as (_ & _ & M). rewrite <- (M x). subst rhoL'. cbn [rho_set_rw rm]. destruct HagL as (_ & _ & ML). rewrite <- (ML x). reflexivity.
  Qed.

  Section FailCut.
    Variables (msF : machine_state) (rhoF : valuation).
    Hypothesis VF : valC rhoF.
    Hypothesis RMF : ltac2:(tb__ "0|0|
S90Q40A1S3SbS90Q8A1A1S26VrhoF;R1A2VmW;R1A1A3Fx;").
    Hypothesis HsmF : ltac2:(tb__ "0|0|
S2bS1bVrhoF;S10fSaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").

    Local Abbreviation SD := (AllocMetaBrk.sd s).
    Lemma HagF : ltac2:(tb__ "0|0|
S33Sa5SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
    Proof using RMF VF. destruct VF as (A1 & A2 & A3). split; [intros i Hi; exact (A1 i Hi) | split; [exact A2 | intros x; symmetry; exact (RMF x)]]. Qed.
    Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
    Lemma HOF : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3S9S20Sa6S114A1S11S20S110S112A3A3A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. pose proof LBF_misc as (_ & _ & EO). rewrite EO in Hall. exact Hall. Qed.
    Lemma HfrF : ltac2:(tb__ "0|0|
S90Q40A1S4dVrhoF;S9S20Sa6S114A1S11S20S110S112A3A3R1A3S3SbS90Q8A1A1S17bVmsF;R2A2S26VrhoF;R2A2A3F_;Fa;").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. pose proof LBF_misc as (_ & _ & EO). rewrite EO in Hfr. exact Hfr. Qed.

    Definition mC : word -> option byte := ltac2:(tb__ "0|0|
S187VrhoF;VmsF;S110S112A4").

    Lemma KU_entry : ltac2:(tb__ "0|0|
S12cS20S2fS1bSfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2A3S110A3").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom Htp.
      unfold UNCH_F. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
      constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
      constructor; [apply hold_errno|]. constructor; [exact HS|].
      constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
      constructor.
    Qed.
    Lemma KU_leaf : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3S110A3").
    Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [H _]. exact H. Qed.
    Lemma KC_leaf : ltac2:(tb__ "0|0|
S12cS20S2fS1bVrhoF;VmsF;A3S112A3").
    Proof using HsmF. pose proof HOF as H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. exact H. Qed.
    Lemma Kvars : ltac2:(tb__ "0|0|
S3SdSe2S20S4cSa5A1S11S20S110S112A3A3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kcov : ltac2:(tb__ "0|0|
S3SdSe2S20S186S110A3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Klits : ltac2:(tb__ "0|0|
S3SdSe2S20S188S11S20S110S112A3A3SfA3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdSe2S20S20S41SdLx;S4bR1A1SfS17S17S1S17Ll;M0G0S0S21ScSeS0S0A2A1ScS4fA1S17Ltmpl;Lflds;Lcnt;Lesz;X41x6Lo;S11S20S110S112A3A3SfA3"). Proof using . reflexivity. Qed.
    Lemma KIT_unch : ltac2:(tb__ "0|2|
S20S0Se1S20R2S110A3S4S5bS13S0S0S28VrhoF;R3A2M0A3R2A2S5dR2S16S0S0G0A3A2A2S4S3SbS90Q8A1A1Se4S1bS128S91Q40R3A2M1A3Se4S1bVmW;G1A3A3S3SdSe5S1bS128G1A3Se5S1bVmW;G1A3A3A2F_;F_;Fx;Fo;").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_F CHG_F KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
    Lemma KIT_chgb : ltac2:(tb__ "0|3|
S20S0Se1S20R2S112A3S4S5bS13S0S0S28VrhoF;R3A2M0A3R2A2S5dR2S16S0S0G0A3A2A2S4S3SdSe5S1bS128S91Q40M1R3A2A3SfA3S6S90Q8A1M2G2S3SbG2A1Se4S1bS128S91G1R4A2A3S12G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
    Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_F CHG_F KC_leaf Kdunk). Qed.
    Lemma KIT_chgc : ltac2:(tb__ "0|4|
S20S24S15Se1S20R3S112A3Se1S24R3S57R4A1A3S154R3S62S48R4A1A1A2S3SbS90Q8M0A1M1A1Se4S1bS128S91Q40M2S5cS5cS92G2S30SfcVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7M3S56R6A1A2A2S43G3S50R5A1A2A2S5fR4A1A2A2A3S12G1S12dG1R4S52S62S48R5A1A1S30VrhoF;S51R5A1A2A2S91G0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
    Proof using HsmF RMF VF. exact (ReabKit.chg_cell segsU (rho1 mW) rhoF msF HromF UNCH_F CHG_F KC_leaf AM_NEXT HagF Kvars). Qed.

    Definition touched (x : Z) : Prop := 370536 <= x < 370544.
    Lemma touched_dec x : ltac2:(tb__ "0|1|
S16eS12aVx;A1M0S5G0A1A2"). Proof using . unfold touched. apply range_dec. Qed.
    Lemma CHG_ranges : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28VrhoF;A1S112A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3").
    Proof using Hav Hev Hgd. cbn [map CHG_F]. unfold O_brkD, O_brk. cbn [am_ctx AM_P]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by lia. rewrite !u64 by lia. reflexivity. Qed.
    Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3ScSeS0S0A2M0A1S12eS20G0S28VrhoF;A1S110A4S9G0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S10G0A1A3A3A3A3A3A3A3A3").
    Proof using Hav Hev Hgd Htp VF mW.
      cbn [map UNCH_F]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxD, O_ctxB. cbn [am_got am_libc am_ctx AM_P].
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      assert (EL0 : forall z, eval rhoF (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
      rewrite (evC rhoF (v 173) VF eq_refl), ev173. rewrite (evC rhoF (SVar 24) VF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.
    Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S5bZ0Vx;A2S5dVx;S5eZ2Z40A2A2A2S17eVrhoF;S11S20S110S112A3S91Q40Vx;A2A3S7S6S20S20S4Se1S20R1S110A3S4S5bS13S0S0S28VrhoF;R1A2M0A3Vx;A2S5dVx;S16S0S0G0A3A2A2A2Lo;A2S12aVx;A1A2F_;F_;").
    Proof using Hav Hev Hgd.
      intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
      pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
      destruct M as [E|[]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
    Qed.

    Lemma mC_out x : ltac2:(tb__ "0|2|
S4S5bZ0Vx;A2S5dVx;S5eZ2Z40A2A2A2SeS0S0A2M0Se1G0R1S9G0SaS0S0Z28d50Z28d58A4S9G0SaS0S0Z5a338Z5a340A4S9G0SaS0S0Z5a360Z5a368A4S9G0SaS0S0Z5a388Z5a390A4S9G0SaS0S0Z3a02cZ3a030A4S9G0SaS0S0Z5a3d0Z5a3dcA4S9G0SaS0S0Z5a3e0Z5a420A4S9G0SaS0S0Z5a768Z5a770A4S10G0A1A3A3A3A3A3A3A3A3A3S5S4S5bS13S0S0R2A3Vx;A2S5dVx;S16S0S0R2A3A2A2A1F_;Fr;S3SbS90Q8A1A1S128S91Q40Vx;A2M1A1VmW;G1A1A3F_;F_;").
    Proof using Hav Hev Hgd Htp RMF VF.
      intros Hx NI. unfold mC. rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F); [exact (RMF _)|].
      intros (o & Ho & RR). rewrite u64 in RR by lia. pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite map_app, UNCH_rangesF, CHG_ranges in M.
      cbn [app] in M. exact (NI _ M RR).
    Qed.

    Let bv1 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bS128A2Se5S1bS128A2A2").
    Let rv1 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bS128A2S90Q40A1SfL_;A2").
    Let rv0 : byteview := ltac2:(tb__ "0|0|
S95Se4S1bVmW;A2S90Q40A1SfL_;A2").

    Theorem V1 : ltac2:(tb__ "0|1|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S5S12aR2A1A1S4S3SbS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF.
      intros x Hx NT.
      assert (EQ : Glue.rd_of segsU mC (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mC (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
      { destruct (in_ranges_dec rhoF (UNCH_F ++ CHG_F) (Z_to_bv 64 x)) as [IN|OUT].
        - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
        - unfold mC. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F _ OUT), RMF. auto. }
      destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
    Qed.
    Theorem VM : ltac2:(tb__ "0|0|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S12aR2A1S147VL;S104Vs;A1R3A3S5S3SbS0A1Vbv1;R4A1S14S0A1A3A1F_;F_;F_;Fx;").
    Proof using Hav Hev Hgd HsmF.
      intros x Hx T _. pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR. cbn [nth map CHG_F] in CR.
      destruct (KIT_chgb O_brkD x ltac:(left; reflexivity) ltac:(rewrite CR; cbn [fst snd]; unfold touched in T; lia)) as [W [b Hb]].
      unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, Hb. discriminate.
    Qed.
    Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.

    Theorem VIN : ltac2:(tb__ "0|1|
S13bSe1S13bR1S11S13bS13eS104Vs;A1M0A1S15eG0A1A3A3S179VL;S12aR2A3S148VL;Vbv1;R3A3F_;F_;Fc;").
    Proof using HI HMI HXr Hav Hbrk Hev Hgd Hinit HsmF RMF VF.
      intros c Hc (k & Hk & T). pose proof Hctx' as HCX. unfold touched in T.
      assert (Halive : st_brk s <> BrkDead) by (rewrite Hbrk; discriminate).
      destruct (AllocMetaBrk.image_sd X R U s HI HXr Hinit c Hc) as [-> | [Hold NE]].
      -
        unfold AllocMetaBrk.C_brkD, MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr sval_num]. intros j Hj.
        pose proof (KIT_chgc O_brkD (mkCell (SLit 928) 8 (SLit M64)) j (or_introl eq_refl) (or_introl eq_refl) ltac:(cbn; lia)) as RD.
        cbn [ob_base O_brkD O_brk c_off c_width c_val am_ctx AM_P] in RD. rewrite B_ctx, soff_lit_small in RD by lia.
        change (eval rhoF (SLit M64)) with (Z_to_bv 64 M64) in RD. rewrite nth_enc_bytes in RD by (cbn; lia).
        pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR. cbn [nth map CHG_F] in CR.
        destruct (KIT_chgb O_brkD (ly_ctx L + CTX_brk + Z.of_nat j) (or_introl eq_refl) ltac:(rewrite CR; cbn [fst snd]; rewrite HCX; unfold CTX_brk; lia)) as [W _].
        unfold bv1, byteview_of.
        replace ((0 <=? ly_ctx L + CTX_brk + Z.of_nat j) && (ly_ctx L + CTX_brk + Z.of_nat j <? 2 ^ 64))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; rewrite HCX; unfold CTX_brk; lia).
        cbn [andb]. rewrite W. rewrite HCX. unfold CTX_brk. replace (369616 + 920 + Z.of_nat j) with (369608 + 928 + Z.of_nat j) by lia.
        rewrite RD. f_equal. replace (le_byte M64 8 j) with (le_byte (-1) 8 j) by reflexivity.
        rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia.
      -
        exfalso. destruct (cell_cases X R U s HI HXr c Hold) as [Hcc | [(a & next & Ha & Hca) | (g & am & Hu & Hcg)]].
        + destruct (Zones2.ctx_zone X R U s L HI HXr HL c 920 8 Hold ltac:(lia) ltac:(unfold CTX_SIZE; lia) ltac:(exists k; split; [exact Hk | rewrite HCX; lia])) as [_ (o & Eloc & O1 & O2)].
          pose proof (AllocMetaBrk.ctx_cell_w8 s c Hcc) as W8.
          pose proof (AllocMetaBrk.ctx_cells_SC13 s c o Hcc Eloc ltac:(unfold CTX_active, CTX_seq; lia)) as S13.
          unfold AllocMetaBrk.SC13 in S13. unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
            CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
          destruct S13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2, NE; injection Eloc as Eo; subst o; try lia.
          apply NE. reflexivity.
        + pose proof (area_cell_in s L a next c Hca) as RI. pose proof (area_R a Ha) as (A1 & A2 & A3). top_ranges.
          unfold range_incl, crange, e_area, cell_range in RI. cbn [fst snd] in RI. unfold PGSZ in RI.
          assert (EA : zA a = loc_addr L (LMem a)) by (unfold zA, addr_of, loc_addr; destruct a; reflexivity). rewrite EA in A1, A2, A3. lia.
        + destruct (group_cell_in X R U s L HI g am c Hu Hcg) as (rg & _ & _ & _ & ER & RI & RI2).
          destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4). cbn [mc_img_lo mc_img_hi C_U] in G3.
          destruct RI2 as (d & Ed & Hd0 & Hd1). rewrite Ed in T. cbn [loc_addr] in T.
          assert (EA : addr_of L (am_mem am) = loc_addr L (LMem (am_mem am))) by (unfold addr_of, loc_addr; destruct (am_mem am); reflexivity).
          rewrite EA in G1, G2, G3. revert T G3 Hd0 Hd1 Hk. clear. cbn [loc_addr]. destruct (am_mem am) as [pr po]. cbn [padd]. intros. lia.
    Qed.
    Theorem OLD : ltac2:(tb__ "0|1|
S13bSe1S13bR1S11S13bS13eS104Vs;A1M0A1S15eG0A1A3A3S5S179VL;S12aR2A3A1Se1S13bR3S11S13bS13eVs;A1S15eVs;A1A3A3F_;F_;Fc;").
    Proof using HI HMI HXr Hav Hbrk Hev Hgd Hinit.
      intros c Hc NM. pose proof Hctx' as HCX. assert (Halive : st_brk s <> BrkDead) by (rewrite Hbrk; discriminate).
      destruct (AllocMetaBrk.image_sd X R U s HI HXr Hinit c Hc) as [-> | [Hold _]]; [|exact Hold].
      exfalso. apply NM. exists 0%nat. split; [cbn; lia|]. cbn [mc_loc loc_addr AllocMetaBrk.C_brkD]. rewrite HCX. unfold touched, CTX_brk. lia.
    Qed.

    Theorem minvI_sd : ltac2:(tb__ "0|0|
S16dS94VX;VR;VU;Sf5S104Vs;A1VL;A2Se4S1bS128A2Se5S1bS128A2Vvm;A8").
    Proof using Erd Ewok HI HMI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF bv0 rv0.
      unfold MInvI. pose proof Hctx' as HCX. assert (Halive : st_brk s <> BrkDead) by (rewrite Hbrk; discriminate).
      refine (minv_postG C_U (Inv X R U) (Inv X R U) s SD L (Glue.rd_of segsU mW) (Glue.rd_of segsU mC) (Glue.wok_of segsU mW) (Glue.wok_of segsU mC) vm
                HMI0 (AllocMetaBrk.Inv_sd X R U s HI Hinit Halive) HB HL eq_refl eq_refl
                (AllocMetaBrk.vm_ok_sd s L vm HV) touched touched_dec V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _).
      - intros c Hc. exact (cell_spanI X R U SD L (AllocMetaBrk.Inv_sd X R U s HI Hinit Halive) HXr HL c Hc).
      - intros x Hx. exact (owned_spanI s L HL x Hx).
      - intros c Hc. exact (cell_w_posI SD c Hc).
      - intros x T _. left. unfold touched in T. cbn [mc_ctx C_U]. unfold CTX_SIZE. lia.
      - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
        unfold CTX_SIZE in Hx. clear - Hx. lia.
      - intros Hf. exfalso. cbn in Hf. rewrite Hinit in Hf. discriminate.
    Qed.

    Lemma gd_rd' : ltac2:(tb__ "0|0|
S99S95Se4S1bS128A2S90Q40A1SfL_;A2S97S94A1U8Vgd;A4").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF.
      intros k Hk. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_F] in R1.
      destruct (KIT_unch O_guard (mc_chk_guard C_U + Z.of_nat k) ltac:(right; left; reflexivity) ltac:(rewrite R1; cbn [fst snd mc_chk_guard C_U]; lia)) as [E _].
      unfold byteview_of in *. pose proof (Hgd_rd k Hk) as G. unfold byteview_of in G. rewrite Erd in G. cbn beta in G |- *. rewrite E. exact G.
    Qed.
    Lemma ev_rd' : ltac2:(tb__ "0|2|
S15S154R1U4A2S3SbS90Q8M0A1M1A1Se4S1bS128S91Q40S5cS9bS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vevb;S91G0Z0A2A4A2A3F_;Fj;").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF.
      intros j Hj. pose proof (f_equal (fun l => nth 4 l (0, 0)) UNCH_rangesF) as R4. cbn [nth map UNCH_F] in R4.
      destruct (KIT_unch O_errno (mc_errno C_U + Z.of_nat j) ltac:(do 4 right; left; reflexivity) ltac:(rewrite R4; unfold mc_errno; cbn [fst snd mc_tp C_U]; lia)) as [E _].
      rewrite E. exact (Hev_rd j Hj).
    Qed.
    Lemma av_rd' : ltac2:(tb__ "0|2|
S15S154R1U8A2S3SbS90Q8M0A1M1A1Se4S1bS128S91Q40S5cS9aS94A1S5fR2A1A2A2A3S12G1S12dG1R2Vavb;S91G0Z0A2A4A2A3F_;Fj;").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF.
      intros j Hj. pose proof (f_equal (fun l => nth 2 l (0, 0)) UNCH_rangesF) as R2. cbn [nth map UNCH_F] in R2.
      destruct (KIT_unch (O_auxvp AM_P) (mc_auxv C_U + Z.of_nat j) ltac:(do 2 right; left; reflexivity) ltac:(rewrite R2; unfold mc_auxv; cbn [fst snd mc_libc C_U]; lia)) as [E _].
      rewrite E. exact (Hav_rd j Hj).
    Qed.
    Lemma canary_rd' x : ltac2:(tb__ "0|4|
S7S4S5bS9dS94A1M0Vx;A2S5dVx;S5cG0Z8M1A2A2A2S4S5bS97S94A1M2Vx;A2S5dVx;S5cG2G1A2A2A2A2S3SbS90Q8A1A1Se4S1bS128S91Q40Vx;A2M3A3Se4S1bVmW;G3A3A3F_;").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF.
      intros Hx. pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_F] in R0, R1.
      cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx. destruct Hx as [Hx|Hx].
      - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
      - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
    Qed.

    Definition rhoEF : valuation := rho_sub rhoF subBF.
    Definition rhoX : valuation := ltac2:(tb__ "0|0|
S4aS2dS12bA1S3dS12bA1S128A3").
    Lemma smatch_cutE : ltac2:(tb__ "0|0|
S2bS1bS12bSa4S1bSa2SaaA3SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").
    Proof using HMI Hav Hev Hgd HsmF RMF VF.
      unfold rhoEF. apply (entails_sound segsU (U.Mal_ameta__G1.Mal_ameta_runs.add_facts LBF U.Mal_ameta__G1.Mal_ameta_runs.res_facts) _ subBF rhoF _ entBF).
      pose proof LBF_misc as (_ & NX & _).
      apply U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app; [exact HsmF | | rewrite NX; vm_compute; reflexivity].
      exact (U.Mal_ameta__G5.Mal_ameta_NB.res_facts_hold s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW rhoF HagF).
    Qed.
    Lemma Pre78r_objs_eq : ltac2:(tb__ "0|0|
S20Se1S20R1S2aSa4S1bSa2SaaA3A1A3S6S20S20S4Se1S20R1S9S20Sa6S114A1S11S20S110S112A3A3A3S32S3SeS0S0A2S28R1R4A2S28R1R2A2A3FrhoY;A2Lo';A2F_;Fo;").
    Proof using Hgd.
      intros o Ho. rewrite (U.Mal_ameta__G2.Mal_ameta_R78.Pre78r_objs) in Ho.
      destruct Ho as [<-|Ho]; [exists (O_stk stkE_cells); split; [left; reflexivity | intros; reflexivity]|].
      exists o. split; [right|intros; reflexivity]. revert Ho. unfold U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R, UNCH_F, CHG_F, U.Mal_ameta__G2.Mal_ameta_R78.O_ctx78, O_ctxD, U.Mal_ameta__G2.Mal_ameta_R78.O_brkD, O_brkD. cbn [firstn skipn app In]. tauto.
    Qed.
    Theorem smatch_cut : ltac2:(tb__ "0|0|
S2bS1bS129Sa4S1bSa2SaaA3SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").
    Proof using HMI Hav Hev Hgd HsmF RMF VF.
      unfold rhoX. apply (smatch_set_rm segsU rhoEF _ (tr, mkCfg msF md) mC); [|exact smatch_cutE].
      intros a Ha. unfold mC. rewrite (ReabKit.kit_out rhoF msF UNCH_F CHG_F); [reflexivity|].
      intros (o & Ho & RR). pose proof smatch_cutE as SM.

      assert (RNG : obj_range rhoEF o = obj_range rhoF o).
      { apply (ReabKit.range_ag rhoF rhoEF (O_stk stkE_cells :: UNCH_F ++ CHG_F) [] 187%positive); [| vm_compute; reflexivity | right; exact Ho].
        split; [|split; [intros l; reflexivity | intros x; reflexivity]]. intros i Hi. unfold rhoEF, rho_sub. cbn [rw].
        rewrite wsub_get_miss; [reflexivity|]. apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq.
        pose proof (proj1 (forallb_forall _ _) (proj1 subBF_ok) p Hp) as Q. cbn beta in Q. apply Bool.orb_prop in Q as [Q|Q]; [apply Z.leb_le in Q; lia | apply Pos.eqb_eq in Q; lia]. }
      unfold outside_all in Ha. rewrite (U.Mal_ameta__G2.Mal_ameta_R78.Pre78r_objs) in Ha.
      assert (IN' : In o (O_stk frame_cells :: firstn 4 (U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R) ++ [O_errno] ++ skipn 4 (U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R))).
      { right. revert Ho. unfold UNCH_F, CHG_F, U.Mal_ameta__G2.Mal_ameta_R78.UNCH_R, U.Mal_ameta__G2.Mal_ameta_R78.O_ctx78, O_ctxD, U.Mal_ameta__G2.Mal_ameta_R78.O_brkD, O_brkD. cbn [firstn skipn app In]. tauto. }
      pose proof (proj1 (Forall_forall _ _) Ha o IN') as NR. lazy beta zeta in NR. rewrite RNG in NR. exact (NR RR).
    Qed.

    Lemma Halive : ltac2:(tb__ "0|0|
S5S3S72S73Vs;A1S7eA3A1"). Proof using Hbrk. rewrite Hbrk. discriminate. Qed.
    Lemma RXlow j : ltac2:(tb__ "0|0|
S5dS2Vj;A1Zc8A2S5S3S1Vj;PbbA3A1S3S90Q40A1S2dS129Vj;A2S2dVrhoF;Vj;A2A3F_;F_;").
    Proof using Hav Hev Hgd.
      intros Hj NE. unfold rhoX, rhoEF, rho_sub. cbn [rw]. rewrite wsub_get_miss; [reflexivity|].
      apply forallb_forall. intros p Hp. apply Bool.negb_true_iff. apply Pos.eqb_neq.
      pose proof (proj1 (forallb_forall _ _) (proj1 subBF_ok) p Hp) as Q. cbn beta in Q. apply Bool.orb_prop in Q as [Q|Q]; [apply Z.leb_le in Q; lia | apply Pos.eqb_eq in Q; congruence].
    Qed.
    Lemma RXrho j : ltac2:(tb__ "0|0|
S15fVj;PaaA2S3S90Q40A1S2dS129Vj;A2S2dVrho;Vj;A2A3F_;").
    Proof using Hav Hev Hgd VF. intros Hj. rewrite RXlow by lia. destruct VF as (A1 & _). rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj. Qed.
    Lemma RLrho l : ltac2:(tb__ "0|0|
S3ScS90Q8A1A1S3dS129Vl;A2S3dVrho;Vl;A2A3").
    Proof using VF. unfold rhoX, rhoEF, rho_sub. cbn [rl]. destruct VF as (_ & A2 & _). rewrite <- (A2 l). reflexivity. Qed.
    Lemma RX187 : rw rhoX 187%positive = Z_to_bv 64 (-1).
    Proof using . unfold rhoX, rhoEF, rho_sub. cbn [rw]. replace (wsub_get subBF 187) with (SLit M64) by (vm_compute; reflexivity). cbn [eval]. apply bv_eq. reflexivity. Qed.
    Lemma rw1v_sd j : ltac2:(tb__ "0|0|
S5S3S1Vj;PbbA3A1S3SbS0A1S102S104Vs;A1VL;Vgd;Vevb;Vavb;Vj;A6S102Vs;VL;Vgd;Vevb;Vavb;Vj;A6A3F_;").
    Proof using Hav Hev Hgd.
      intros NE. unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v.
      repeat (let c := match goal with |- context [if (Z.pos j =? ?k) then _ else _] => constr:(Z.pos j =? k) end in
              destruct c eqn:?; [first [reflexivity | exfalso; match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H; lia end] |]).
      reflexivity.
    Qed.
    Lemma RX1 : ltac2:(tb__ "0|1|
S1S0S3SbS0A1S102S104Vs;A1VL;Vgd;Vevb;Vavb;R2A6S12S0R1A2A3S3S90Q40M0A1S2dS129R3A2S91G0R2A2A3F_;Fz;Fj;").
    Proof using Hav Hev Hgd VF mW.
      intros j z E. destruct (Pos.eq_dec j 187) as [->|NE].
      - unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E. cbn in E. injection E as <-. exact RX187.
      - rewrite (rw1v_sd j NE) in E.
        assert (Hj : (Z.pos j < 200)).
        { unfold U.Mal_ameta__G1.Mal_ameta_I.rw1v in E. clear - E.
          repeat match type of E with context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [apply Z.eqb_eq in e; lia|clear e] end. discriminate. }
        rewrite (RXlow j Hj NE). destruct VF as (A1 & _). rewrite <- (A1 j) by (unfold AM_NEXT; lia). exact (rw1_v j z E).
    Qed.
    Lemma AGX k : ltac2:(tb__ "0|0|
S33Vk;S129SfcS104Vs;A1VL;S129Vgd;Vevb;Vavb;S128A7A3").
    Proof using Hav Hev Hgd VF mW. apply rho1_self; [exact RX1 | reflexivity]. Qed.
    Lemma HsmC' : ltac2:(tb__ "0|0|
S2bS1bSfcS104Vs;A1VL;S129Vgd;Vevb;Vavb;S128A7Sa4S1bSa2SaaA3SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4").
    Proof using HMI Hav Hev Hgd HsmF RMF VF. exact (smatch_agree segsU rhoX _ (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res) _ (AGX _) smatch_cut). Qed.
    Lemma HtpX : ltac2:(tb__ "0|1|
S3S90Q40M0A1S2dS129P18A2S91G0S9cS94A1A2A3").
    Proof using Hav Hev Hgd Htp VF. rewrite RXrho by lia. exact Htp. Qed.
    Lemma STKX : ltac2:(tb__ "0|3|
S4S5bZ0S5cSfeS129A1M0SfdS129A1M1A2M2A2S4S5bS96VL;A1G2A2S4S5bG0S5eZ2Z40A2A2S5bG1S65SbeA1A2A2A2A2").
    Proof using EmW Hav Hev Hgd Hsm_pre Htop VF. unfold U.Mal_ameta__G1.Mal_ameta_I.sp0, U.Mal_ameta__G1.Mal_ameta_I.D0. rewrite !RXrho by lia. exact STK. Qed.
    Lemma HFpreX : ltac2:(tb__ "0|0|
S12cS29S3cS129A1S34S132Sf2A1A1A3").
    Proof using Hav Hev Hgd Hsm_pre Htop VF.
      assert (AGV : agree_vals NF rho rhoX) by (split; [intros i Hi; symmetry; apply RXrho; unfold NF in Hi; lia | intros l; symmetry; apply RLrho]).
      assert (SB : forall f, In f (ss_facts (ContractAM.Pre_am IEC_U)) -> sprop_below NF f = true) by (apply forallb_forall; vm_compute; reflexivity).
      apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) (smatch_facts_hold segsU _ _ _ Hsm_pre) f Hf) as H.
      exact (proj1 (holds_agree_vals NF rho rhoX f AGV (SB f Hf)) H).
    Qed.
    Lemma s0_sd : ltac2:(tb__ "0|1|
S3S6fS183S104Vs;A1M0A1G0A3").
    Proof using Hinit. unfold s0, AllocMetaBrk.sd, set_init_done, set_brk. generalize Hinit. clear. destruct s; cbn. intros ->. reflexivity. Qed.
    Lemma s0_s : ltac2:(tb__ "0|0|
S3S6fS183Vs;A1Vs;A3").
    Proof using Hinit. unfold s0, set_init_done. generalize Hinit. clear. destruct s; cbn. intros ->. reflexivity. Qed.
    Lemma HY : ltac2:(tb__ "0|2|
ScSeS81S0A2A1M0SeSbS69A1S6fA2M1S140G1S74S104Vs;A1A1R2R1A4S6G0G0S140G1S74Vs;A1R1R3A4Lktr';A2F_;Fres;Fktr;").
    Proof using Hac Hbrk Hcnt Hhd Hinit.
      intros ktr res Y. destruct (AllocMetaBrk.yields_dead_inv SD Hhd Hcnt Hac eq_refl ktr res Y) as (zm & zp & ->).
      exists (tr_BK s 0 zm zp). pose proof (yields_BK s Hhd Hcnt Hac rb pb Hbrk 0 zm zp) as YB. unfold r_BK in YB. cbn [Z.eqb] in YB.
      rewrite s0_sd. unfold s_dead in YB. rewrite s0_s in YB. exact YB.
    Qed.
    Lemma MEMC : ltac2:(tb__ "0|1|
S0S4S5bZ0R1A2S5dR1S5eZ2Z40A2A2A2S165S1bS94Sf5Vs;VL;A2R2A4S5S169S94R3A2A1S5S168S94R4A2A1S3SbS90Q8A1A1S26S129S91Q40R5A2M0A2S26Vrho;G0A2A3F_;F_;F_;F_;Fa;").
    Proof using EmW HI HMI HXr Hav Hev Hgd Htp RMF VF.
      intros a Ha CA NE NS. change (rm rhoX) with mC. rewrite <- EmW. apply (mC_out a Ha).
      unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in NS, NE.
      assert (NCTX : ~ (369616 <= a < 369616 + CTX_SIZE)).
      { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
        - top_ranges. unfold CTX_SIZE in Hc. lia.
        - unfold ma_blocks in Hin. cbn [ma_s ma_L] in Hin. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
          destruct (user_block_in_group X R U s L HI HXr (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4). cbn [fst snd] in B1, B2, B3, B4.
          destruct (group_range X R U s L HI HL C_U vm g am Hu HV HLG) as (G1 & G2 & G3 & G4). cbn [mc_img_lo mc_img_hi C_U] in G3.
          pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia. unfold UNIT, IB, CTX_SIZE in *. lia.
        - apply H. cbn [mc_ctx C_U]. exact Hc. }
      unfold CTX_SIZE in NCTX. clear - NS NE NCTX. intros r Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
    Qed.
    Lemma MEMM : ltac2:(tb__ "0|2|
S15S6aS0S3SbS6aA1S13fVs;R3A2S12S6aR2A2A3S3S85S82R3A1S80A3S3SdS84R4A1SfA3S4S5bS142VL;R6A2M0R4A2S5dR4S5cG0S83R5A1A2A2A2S3SbS90Q8A1A1S26S129S91Q40R5A2M1A2S26Vrho;G1A2A3F_;F_;F_;F_;Fa;Frg;Fk;").
    Proof using EmW HI HMI Hav Hev Hgd Htp RMF VF.
      intros k rg a Hk Hkd Hl Ha. change (rm rhoX) with mC. rewrite <- EmW.
      destruct (map_region_where k rg a Hk Hkd Hl Ha) as (R64 & NI & _). cbn [mc_img_lo mc_img_hi C_U] in NI.
      apply (mC_out a R64). clear - NI. intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd]; lia|]). destruct Hr.
    Qed.
    Lemma MEMG : ltac2:(tb__ "0|4|
S0S7S4S5bS9dS94A1M0R1A2S5dR1S5cG0Z8M1A2A2A2S4S5bS97S94A1M2R1A2S5dR1S5cG2G1A2A2A2A2S3SbS90Q8A1A1Se4S1bS26S129A1S91Q40R2A2M3A3Se4S1bS26Vrho;A1G3A3A3F_;Fa;").
    Proof using EmW Erd Ewok HMI Hac Hav Hav_rd Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp RMF VF. intros a Ha. change (rm rhoX) with mC. rewrite <- EmW. exact (canary_rd' a Ha). Qed.

    Theorem fail_sound : ltac2:(tb__ "0|0|
S15S10bS1bVok;R1S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw;A4S10cS1bVok;R2SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A4F_;Fn;").
    Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros n HQ.
      pose proof (AllocMetaBrk.Inv_sd X R U s HI Hinit Halive) as HI'.
      assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA SD L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
      { intros w. apply (LQP_rebase_state SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      apply (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_sound SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
               gd_rd' av_rd' HtpX tr md eq_refl Hhd Hcnt Hac eq_refl Hinit msF HsmC' Kc HKc Evm ok HOK
               (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX n).
      intros w [HL|HO].
      - apply HQ. exact (REB w HL).
      - refine (U.Mal_ameta__G4.Mal_ameta_R2E.resok_sound SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl Hhd Hcnt Hac eq_refl Hinit Kc HKc Evm ok HOK STKX HFpreX n _ w HO).
        intros w' HL'. apply HQ. exact (REB w' HL').
    Qed.

    Theorem fail_ex : ltac2:(tb__ "0|0|
S10aS1bS109S3S109R1SaScSe6A1Sf9Vtr;SfaVmsF;Vmd;A2A4A3Lw;S109S11cS1bS1cVrho;S131S1bS94Sf2VX;VR;VU;Sf5Vs;VL;A2VKc;A8R1A5Lw;A3").
    Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hev_rd Hgd Hgd_rd Hhd Hinit Hrom HsmF Hsm_pre Htop Htp RMF VF bv0 bv1 rv0 rv1.
      intros w ->.
      pose proof (AllocMetaBrk.Inv_sd X R U s HI Hinit Halive) as HI'.
      assert (REB : forall w, LQP segsU NF rhoX (Posts_am segsU C_U IEC_U X R U (mkMA SD L) Kc) w -> LQP segsU NF rho (Posts_am segsU C_U IEC_U X R U (mkMA s L) Kc) w).
      { intros w. apply (LQP_rebase_state SD Kc rhoX); try reflexivity.
        - intros i Hi. apply RXrho. unfold NF in Hi. lia.
        - exact RLrho.
        - exact MEMC. - exact MEMM. - exact MEMG. - exact HY. }
      destruct (U.Mal_ameta__G2.Mal_ameta_R78.cut78r_anyex SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl Hhd Hcnt Hac eq_refl Hinit msF HsmC' Kc HKc Evm
                  (U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm) STKX (tr, mkCfg msF md) eq_refl) as (w' & ST & [HL | HO]).
      - exists w'. split; [exact ST | exact (REB w' HL)].
      - destruct (U.Mal_ameta__G4.Mal_ameta_R2E.resok_anyex SD L X R U rhoX HI' HXr (Glue.rd_of segsU mC) (Glue.wok_of segsU mC) vm minvI_sd gd evb avb Hgd Hev Hav mC eq_refl eq_refl ms Hrom
                  gd_rd' av_rd' HtpX tr md eq_refl Hhd Hcnt Hac eq_refl Hinit Kc HKc Evm HVI STKX HFpreX w' HO w' eq_refl) as (w'' & ST2 & HL').
        exists w''. split; [eapply wsteps_trans; [exact ST | exact ST2] | exact (REB w'' HL')].
    Qed.
  End FailCut.

End BK.

End InstX.

Theorem am_BK_sound : ltac2:(tb__ "0|1|
S109OF_;ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S15S0S164S1bR9R4A3S3SbS69A1S6cSf6R6A1A1S14S69A1A3S3S0S71Sf6R7A1A1Z0M0A3S3S0S6bSf6R8A1A1G0A3S3S72S73Sf6R9A1A1S87R6R5A2A3S3SdS6eSf6RaA1A1SfA3S10dS1bRfS156S1bS133S1bS94ReRdRcRbRaA7S132Sf2A1R9A4S11cS1bS1cR9S131S1bS94Sf2ReRdRcRbRaA8A4A4F_;F_;F_;F_;F_;F_;Fpb;Frb;Frho;FKc;FA;FU;FR;FX;Fok;").
Proof.
  intros ok X R U [s L] Kc rho rb pb HOK Hhd Hcnt Hac Hbrk Hinit. cbn [ma_s ma_L] in *.
  intros n HQ [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.
  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }
  apply (bk_chain s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
           mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit rb pb Hbrk Kc HKc eq_refl ok HOK n).
  - intros w HL. apply HQ. exact HL.
  - intros w (msF & rhoF & -> & VF & RMF & HsmF).
    exact (fail_sound s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
             mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit rb pb Hbrk Kc HKc eq_refl ok HOK msF rhoF VF RMF HsmF n HQ).
Qed.

Theorem am_BK_ex : ltac2:(tb__ "0|1|
ScS69A1SbSeS69S0A2A1S0S0F_;Sf7ScSe6A1Se7OF_;F_;S32S15S0S167R4A1S3SbS69A1S6cSf6R6A1A1S14S69A1A3S3S0S71Sf6R7A1A1Z0M0A3S3S0S6bSf6R8A1A1G0A3S3S72S73Sf6R9A1A1S87R6R5A2A3S3SdS6eSf6RaA1A1SfA3S10aS1bS156S1bS133S1bS94ReRdRcRbRaA7S132Sf2A1R9A4S11cS1bS1cR9S131S1bS94Sf2ReRdRcRbRaA8A4A3F_;F_;F_;F_;F_;F_;Fpb;Frb;Frho;FKc;FA;FU;FR;FX;").
Proof.
  intros X R U [s L] Kc rho rb pb HVI Hhd Hcnt Hac Hbrk Hinit. cbn [ma_s ma_L] in *.
  intros [tr [ms md]] [Hsm HJ]. cbn [w_tr w_cfg fst snd cfg_model] in HJ.
  destruct HJ as (HMI & HXr & HKc & _ & Htp & Htop).
  unfold MInvIR in HMI. pose proof HMI as HMI0. unfold MInvI in HMI0.
  pose proof (mig_I HMI0) as HI. cbn [ma_s] in HI.
  pose proof (mig_statics HMI0) as HST. destruct HST as (_ & _ & _ & _ & _ & _ & _ & _ & (g0 & _ & Hg0)).
  set (mW := rm rho) in *.
  assert (Hrom : rom_ok segsU ms) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))).
  destruct (read_bytes (rd_of segsU mW) (mc_errno C_U) 4 (image_readable mW (mc_errno C_U) 4 ltac:(vm_compute; reflexivity))) as (evb & Hev & Hev_rd).
  destruct (read_bytes (rd_of segsU mW) (mc_auxv C_U) 8 (image_readable mW (mc_auxv C_U) 8 ltac:(vm_compute; reflexivity))) as (avb & Hav & Hav_rd).
  set (gd := g0 mod 2 ^ 64).
  assert (Hgd : 0 <= gd < 2 ^ 64) by (subst gd; apply Z.mod_pos_bound; lia).
  assert (Hgd_rd : holds (byteview_of (rd_of segsU mW) (fun _ => true)) (mc_chk_guard C_U) 8 gd).
  { intros k Hk. etransitivity; [exact (Hg0 k Hk)|]. f_equal. subst gd. unfold le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
  assert (Htp' : rw rho 24%positive = Z_to_bv 64 (mc_tp C_U)).
  { unfold tp_ok in Htp. rewrite <- Htp. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (bk_chain_ex s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit rb pb Hbrk Kc HKc eq_refl HVI (tr, mkCfg ms md) eq_refl)
    as (w1 & ST1 & [(msF & rhoF & -> & VF & RMF & HsmF) | HL1]).
  2:{ exists w1. split; [exact ST1 | exact HL1]. }
  destruct (fail_ex s L X R U rho HI HXr (rd_of segsU mW) (wok_of segsU mW) (m_vmmaps md) HMI gd evb avb Hgd Hev Hav
              mW eq_refl eq_refl ms Hrom Hgd_rd Hev_rd Hav_rd Htp' tr md eq_refl Hsm Htop Hhd Hcnt Hac Hinit rb pb Hbrk Kc HKc eq_refl HVI msF rhoF VF RMF HsmF (tr, mkCfg msF md) eq_refl)
    as (w2 & ST2 & HL).
  exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2] | exact HL].
Qed.
End Mal_ameta_BK.
