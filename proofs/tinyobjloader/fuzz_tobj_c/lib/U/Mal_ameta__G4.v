(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "True"; "False"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "pre_fregs"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "option"; "list"; "true"; "nil"; "prod"; "app"; "Some"; "nat"; "fst"; "snd"; "None"; "false"; "andb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "cell"; "sv"; "mkCell"; "eval"; "SVar"; "reg_sv"; "SAlu"; "obj_range"; "rm"; "sprop"; "sstate"; "ss_objs"; "agree_below"; "rw"; "valuation"; "obj_holds"; "smatch"; "ss_next"; "ss_pc"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "mkSS"; "soff"; "ss_lenient"; "ss_regs"; "c_width"; "holds"; "DUnknown"; "FcsrFrm0"; "SPUle"; "c_off"; "c_val"; "mkObj"; "ob_base"; "ob_cells"; "odefault"; "ranges_disjoint"; "swf"; "SPAlign"; "SPBranch"; "enc_bytes"; "fcsr_match"; "freg_sv"; "fregs_match"; "mkVal"; "ob_dflt"; "obj_wf"; "outside_all"; "regs_match"; "resv_match"; "rl"; "ro_addr"; "sfcsr"; "sprop_below"; "sv_below"; "tfact"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "pow"; "of_nat"; "sub"; "to_nat"; "modulo"; "leb"; "eqb"; "mul"; "of_N"; "opp"; "ltb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E.InstX.Cut78r.Granted"; "LC"; "GRr"; "pageK"; "subC"; "srcF"; "srcN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "guards"; "safe"; "etriple"; "w_cfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "st_area_tail"; "st_areas"; "st_meta_alloc_shift"; "padd"; "brkst"; "st_area_head"; "st_avail_meta"; "st_brk"; "st_free_meta_head"; "st_mmap_counter"; "st_seq"; "AREA_HDR"; "BrkDead"; "META_SIZE"; "PGSZ"; "astate"; "mslot"; "region"; "st_active"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_init_done"; "st_unmap_seq"; "st_usage"; "METAS_PER_AREA"; "RkMap"; "SP"; "alloc_meta"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK.InstX.Cut78r.Granted"; "az"; "UNCH2"; "md1"; "CHG2"; "LOK"; "LRF2"; "rhoU"; "valU"; "OKC"; "OBJ2"; "O_brkD"; "O_ctxOK"; "memU"; "stkRF2_cells"; "O_errF"; "md2"; "stkOK_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "topL"; "holds"; "mc_auxv"; "mc_chk_guard"; "mc_errno"; "mc_tp"; "addr_of"; "blocks"; "mc_ctx"; "mc_img_hi"; "mc_img_lo"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "LCtx"; "MCell"; "VZ"; "loc"; "sval_num"; "loc_addr"; "optr"; "sval"; "image"; "VP"; "mc_loc"; "CTX_seq"; "Inv"; "LMem"; "cell_holds"; "ctx_cells"; "footprint"; "ly_ctx"; "ly_sec"; "mc_w"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_areas"; "CTX_avail_meta_count"; "CTX_brk"; "CTX_free_meta_head"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head";
"CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "MT"; "VSec"; "alloc_owned"; "keys"; "ly_reg"; "mc_val"; "memb"; "region_of"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "AM_P"; "v"; "Pre_am"; "AM_NEXT"; "LENX"; "A78_res_ok_fail"; "M64"; "A78_res_ok"; "A78_res_ok_ok"; "O_stk"; "O_tail"; "add_facts"; "O_sec"; "Posts_am_P"; "A2e4_first"; "A2e4_next"; "AM_D"; "page_facts"; "O_auxvp"; "O_brk"; "O_errno"; "O_got"; "O_guard"; "O_page"; "O_pgsz"; "am_ctx"; "nz_fact"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "instr"; "BC_EQ"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow"; "L'"; "mnew"; "t1"; "t2"; "pnew"; "lenZ"; "vm1"; "vm2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK.InstX.Cut78r.Granted.FailLeaf2"; "mF"; "touched"; "rho'"; "rw'"; "SC13"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK"; "az"; "md2"; "OKC"; "valU"; "LOK"; "md1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78"; "lenZ"; "L78"; "OKP"; "OKPX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "vm_maps"; "vm_reserved"; "with_vmmaps"; "map_contains"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "rho1"; "Kexact"; "D0"; "sp0"; "optrZ"; "zA"; "avmZ"; "brkZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "liftK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "Posts_am"; "JL_am_ok"; "L_am_ok"; "L_am_null"; "Pre_am"; "AM_D"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "firstn"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "S_ret_lit"; "enomem_ret"; "rho_after_unmap"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "le"; "of_nat"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_n"; "mmap_nZ"; "mmap_none_vm"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "res_n"; "s0"; "tr_RES"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_budget_ok"; "mprotect_model_next"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_base"; "seg_size";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "rho_set_rw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "top_high"; "V_DEPTH"; "mem_kept"; "stack_win"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow"; "gmeets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_R2E.InstX.Cut78r.Granted.AtCut"; "rhoE"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK.InstX.Cut78r"; "OKC"; "az"; "md1"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_pc"; "ms_svc_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E"; "brk_sval"; "valF"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_ROK.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.

Local Ltac lia := slia.
Local Ltac nia := snia.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
Sc9VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S162SacVX;VR;VU;Se7Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§1§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HVX := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HVX).
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
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation avmZ := (@U.Mal_ameta__G1.Mal_ameta_I.avmZ s L).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Notation "§2§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§3§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§3§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev1 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev1).
Local Abbreviation ze_v := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ze_v).
Local Abbreviation ev173 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev185 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§3§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S6aQ40A1S13S6aQ8A1A1F_;Vrd0;S106SbVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S6aQ40A1S12F_;Vwok0;S107SbVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
SafSadVrd0;S6aQ40A1S15L_;A2Sb1SacA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S1aS14fR1U4A2S0S13S6aQ8M0A1M1A1S106SbVmW;S6bQ40S5cSb2SacA1S60R2A1A2A2A3S19G1S144G1R2Vevb;S6bG0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S1aS14fR1U8A2S0S13S6aQ8M0A1M1A1S106SbVmW;S6bQ40S5cSb0SacA1S60R2A1A2A2A3S19G1S144G1R2Vavb;S6bG0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SadS106SbVmW;A2S107SbVmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§4§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S2fVrho;P18A2S6bG0Sb3SacA1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_sec := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brkE := (§4§ U.Mal_ameta__G1.Mal_ameta_I.hold_brkE).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (@U.Mal_ameta__G1.Mal_ameta_I.rng_stk s L rho gd evb avb Hgd Hev Hav mW).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S6aQ40A1S13S6aQ8A1A1F_;VmW;S2aVrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S32SbVrho;S141S103A1S11S14S128A1S138Vtr;S139Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S16bSe7Vs;VL;A2Vrho;A2").
Local Abbreviation zr1_var := (§2§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).

Lemma smatch_add_facts_app : ltac2:(tb__ "0|0|
S30S2cS14S2bA1S17S14S128A1S138A2S32SbR4R3R1A4S143S2bS3eR5A1R3A3S0S12SbaS2bS59S33R5A1A1R4A3S15A3S32SbR7Sf3R6R5A2R4A4F_;F_;F_;Fw;Ffs;FS;FrhoX;").
Proof using .
  intros rhoX S fs [tr0 [ms0 md0]] Hsm HF Hb.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hhalt & HromX & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  unfold smatch, U.Mal_ameta__G1.Mal_ameta_runs.add_facts. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient fst snd cfg_ms cfg_model] in *.
  split.
  { unfold swf in *. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
    repeat (apply andb_prop in Hwf as [Hwf ?]). rewrite forallb_app.
    repeat (apply andb_true_intro; split); try assumption. }
  repeat (split; [assumption|]). apply Forall_app. split; assumption.
Qed.

Section Cut78r.
  Hypothesis Hhd : st_free_meta_head s = None.
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : st_avail_meta_area_count s = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S0S7dS80Vs;A1S85A3").
  Hypothesis Hinit : st_init_done s = true.
  Variable Kc : ltac2:(tb__ "0|0|
S14S128A1S129OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S0S12aVvm;S12bVmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S16aSbVok;VKc;A3").

  Hypothesis HVI : vm_insensitive Kc.
  Hypothesis STK : ltac2:(tb__ "0|3|
S1S5dZ0S5cS133Vrho;A1M0S132Vrho;A1M1A2M2A2S1S5dSaeVL;A1G2A2S1S5dG0S5fZ2Z40A2A2S5dG1S68Sf8A1A2A2A2A2").

  Local Abbreviation L78 := U.Mal_ameta__G2.Mal_ameta_R78.L78.
  Local Abbreviation lenZ78 := (U.Mal_ameta__G2.Mal_ameta_R78.lenZ s).
  Local Abbreviation OKP := (U.Mal_ameta__G2.Mal_ameta_R78.OKP s L rho gd evb avb mW tr md).

  Lemma lenZ_eq : ltac2:(tb__ "0|0|
S0S8S124Vs;A1S116Vs;A1A3").
  Proof using . reflexivity. Qed.
  Lemma lenZ_range : ltac2:(tb__ "0|1|
S1S1S5dZ2000S124Vs;A1M0A2S5dG0S5fZ2Z30A2A2A2S0S8S63G0Z1000A2Z0A3A2").
  Proof using HMI Hav Hev Hgd. exact (U.Mal_ameta__G2.Mal_ameta_R78.lenZ_range s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav). Qed.
  Lemma LENX_val m : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S25S130Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7SecA2S6bG0S124Vs;A1A2A3").
  Proof using HMI Hav Hev Hgd. exact (U.Mal_ameta__G2.Mal_ameta_R78.LENX_val s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav m). Qed.
  Lemma mmap_n_lenZ : ltac2:(tb__ "0|2|
S0S8S6cQ40M0S152S6bG0S124Vs;A1M1A2A1A2G1A3").
  Proof using HMI Hav Hev Hgd. exact (U.Mal_ameta__G2.Mal_ameta_R78.mmap_n_lenZ s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav). Qed.
  Lemma mmap_nZ_lenZ : ltac2:(tb__ "0|1|
S0S8S153S6bQ40S124Vs;A1M0A2A1G0A3").
  Proof using HMI Hav Hev Hgd. exact (U.Mal_ameta__G2.Mal_ameta_R78.mmap_nZ_lenZ s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav). Qed.
  Lemma mmap_n_eq : ltac2:(tb__ "0|2|
S0S6aQ40M0A1S152S6bG0S124Vs;A1A2M1A1G1A3").
  Proof using HMI Hav Hev Hgd. apply bv_eq. rewrite mmap_n_lenZ. symmetry. apply u64. pose proof lenZ_range. lia. Qed.

  Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S167SbVok;S13cS131Vtr;Vmd';A2A1A3F_;").
  Proof using HOK.
    intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho).
  Qed.
  Lemma Kc_vm md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd;A2S3S12aS12aS0S129Vmd';S12eR1Vmd;A2A3Lvmz;A2VKc;Vtr;Vmd';A2F_;F_;").
  Proof using HOK. intros HK [vmz ->]. destruct HOK as (_ & _ & [VI _]). exact (VI tr md vmz HK). Qed.

  Section Granted.
    Variables (aw : word) (rhoL : valuation).
    Hypothesis HagL : ltac2:(tb__ "0|0|
S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoL;A3").
    Hypothesis Hpl : ltac2:(tb__ "0|0|
S151S6bQ40Z0A2Vmd;S25VrhoL;SecA2Vaw;A4").
    Definition az : Z := bv_unsigned aw.
    Definition md1 : Model := ltac2:(tb__ "0|0|
S12eS154S12bVmd;A1S25VrhoL;SecA2Vaw;A3Vmd;A2").
    Definition rhoU : valuation := ltac2:(tb__ "0|0|
S14aVrhoL;SebVaw;Vaw;S152S25VrhoL;SecA2A1A5").

    Lemma EL : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S25VrhoL;SecA2S6bG0S124Vs;A1A2A3").
    Proof using HMI HagL Hav Hev Hgd. rewrite <- (LENX_val mW). symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. Qed.

    Lemma grant_facts : ltac2:(tb__ "0|6|
S1S0S8S63S9bS87A2Z0M0A3S1S5eG0S9bA2S1S5dS5cS9bS124Vs;A1A2M1SaeVL;A1A2S17S6aQ40M2A1M3G3A2M4Sb9G4R1S18G4S12dVvm;A1S12cVvm;A1A3A3S4S5dS5cS6cG2S1bG3G3R2A3A2M5S6cG2S1cG3G3R2A3A2A2S9bA2S5dG1G5A2A2F_;Fe;A2A2A2").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      pose proof Hpl as (Hal & Hpos & Hceil & Hfree). rewrite EL in Hceil, Hfree. rewrite mmap_nZ_lenZ in Hceil. rewrite <- Evm, <- (vm_ok_top L s vm HV) in Hceil. rewrite Evm.
      unfold az. split; [exact Hal|]. split; [exact Hpos|]. split; [exact Hceil|].
      intros [ea esz] He. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV.
      unfold iv_overlap in OV. rewrite mmap_n_lenZ in OV. cbn [fst snd] in *. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
    Qed.
    Lemma az64 : 0 <= az < 2 ^ 64. Proof using . unfold az. apply urange. Qed.
    Lemma aw_eq : ltac2:(tb__ "0|1|
S0S6aQ40M0A1Vaw;S6bG0S9bA2A3"). Proof using . unfold az. symmetry. apply Z_to_bv_bv_unsigned. Qed.

    Lemma Hctx_C : ltac2:(tb__ "0|0|
S0S8SceVL;A1Sb6SacA1A3"). Proof using HMI. exact Hctx. Qed.
    Lemma G_al : az mod PGSZ = 0. Proof using Evm HMI HagL Hav Hev Hgd Hpl. exact (proj1 grant_facts). Qed.
    Lemma G_pos : 0 < az. Proof using Evm HMI HagL Hav Hev Hgd Hpl. exact (proj1 (proj2 grant_facts)). Qed.
    Lemma G_ceil : ltac2:(tb__ "0|0|
S5dS5cS9bS116Vs;A1A2SaeVL;A1A2"). Proof using Evm HMI HagL Hav Hev Hgd Hpl. rewrite <- lenZ_eq. exact (proj1 (proj2 (proj2 grant_facts))). Qed.
    Lemma G_free : ltac2:(tb__ "0|4|
S17S6aQ40M0A1M1G1A2M2Sb9G2R1S18G2S12dVvm;A1S12cVvm;A1A3A3S4S5dS5cS6cG0S1bG1G1R2A3A2M3S6cG0S1cG1G1R2A3A2A2S9bA2S5dS5cS9bS116Vs;A1A2G3A2A2F_;Fe;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl. rewrite <- lenZ_eq. exact (proj2 (proj2 (proj2 grant_facts))). Qed.
    Lemma HIRv : img_reserved C_U vm. Proof using HMI. exact (mig_img HMI). Qed.
    Lemma HIRX : U.Mal_ameta__G2.Mal_ameta_R78.img_reservedX (m_vmmaps md). Proof using Evm HMI. rewrite <- Evm. exact (mig_img HMI). Qed.
    Local Abbreviation MISSIMG := (U.Mal_ameta__G2.Mal_ameta_R78.grant_misses_image gd evb avb Hgd Hev Hav md HIRX aw (eval rhoL LENX) Hpl).

Local Notation "§5§ h__" := (h__ s) (at level 10, h__ global).
Local Abbreviation G_rr := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rr).
Local Abbreviation G_lenZ := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.lenZ).
Local Abbreviation G_pnew := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.pnew).
Local Abbreviation G_mnew := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew).
Local Abbreviation G_t1 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t1).
Local Abbreviation G_t2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2).
Local Abbreviation G_rg1 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rg1).
Local Abbreviation G_rg2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rg2).
Local Abbreviation G_s0_t := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_SPEC1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.SPEC1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_SPEC2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.SPEC2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_HI1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.HI1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_HI2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.HI2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Notation "§6§ h__" := (h__ s Hhd Hcnt Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_t1_fields := (§6§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t1_fields).
Local Abbreviation G_t2_eq := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_eq).
Local Notation "§7§ h__" := (h__ s Hhd Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_t2_fields := (§7§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_fields).
Local Abbreviation G_C_ac := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_ac).
Local Abbreviation G_C_sh := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_sh).
Local Abbreviation G_C_ars := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_ars).
Local Abbreviation G_CHG1 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.CHG1).
Local Abbreviation G_old_ctx1 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_ctx1).
Local Notation "§8§ h__" := (h__ X R U s HI) (at level 10, h__ global).
Local Abbreviation G_res_n_ge2 := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.res_n_ge2).
Local Abbreviation G_ctx_maps_loc := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_maps_loc).
Local Notation "§9§ h__" := (h__ X R U s HI Hhd Hcnt Hac Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_ctx_cells_t1 := (§9§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t1).
Local Abbreviation G_old_noctx_loc := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_noctx_loc X R U s HI HXr).
Local Notation "§10§ h__" := (h__ X R U s HI HXr Hhd Hcnt Hac Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_image_t1 := (§10§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t1).
Local Abbreviation G_C_avm2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_avm2).
Local Abbreviation G_C_cnt2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_cnt2).
Local Abbreviation G_C_hd2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_hd2).
Local Abbreviation G_C_tl2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_tl2).
Local Abbreviation G_CHG2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.CHG2).
Local Abbreviation G_old_ctx2 := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_ctx2).
Local Abbreviation G_C_tn := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_tn).
Local Abbreviation G_fresh_slot := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fresh_slot).
Local Abbreviation G_pnew_fresh := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.pnew_fresh).
Local Abbreviation G_ctx_cells_t2 := (§9§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t2).
Local Abbreviation G_t2pre := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2pre).
Local Abbreviation G_t2_upd := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_upd).
Local Abbreviation G_t2pre_fields := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2pre_fields).
Local Abbreviation G_mnew_prid := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew_prid).
Local Abbreviation G_area_cells_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.area_cells_t2 X R U s HI Hhd Hbrk Hinit).
Local Abbreviation G_image_t2 := (§10§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t2).
Local Abbreviation G_image_t2C := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t2C X R U s HI HXr Hhd Hbrk Hinit).
Local Abbreviation G_ctx_cells_t2C := (§9§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t2C).
Local Abbreviation G_fp_t1 := (§6§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_t1).
Local Abbreviation G_fp_t2 := (§7§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_t2).
Local Abbreviation G_ub_t1 := (§6§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ub_t1).
Local Abbreviation G_ub_t2 := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ub_t2).
Local Abbreviation G_footers_t1 := (§6§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.footers_t1).
Local Abbreviation G_footers_t2 := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.footers_t2).
Local Abbreviation G_L' := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L' s L az).
Local Abbreviation G_wa := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.wa az).
Local Abbreviation G_wn := (§5§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.wn).
Local Abbreviation G_vm1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm1 s vm az).
Local Abbreviation G_vm2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm2 s vm az).
Local Abbreviation G_lenZ_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.lenZ_facts s az HB G_al G_pos).
Local Abbreviation G_a_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.a_facts s L az HB G_al G_pos G_ceil).
Local Abbreviation G_ua := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ua s L az HB G_al G_pos G_ceil).
Local Abbreviation G_un := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.un s L az HB G_al G_pos G_ceil).
Local Abbreviation G_grant_vs_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_image s C_U vm az HIRv G_al G_pos G_free).
Local Abbreviation G_grant_vs_maps := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_maps s vm az G_al G_pos G_free).
Local Abbreviation G_grant_vs_footprint := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_footprint s L C_U vm az Hctx_C statics_in_image_U HV HIRv G_al G_pos G_free).
Local Abbreviation G_fp_size := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_size s L vm az HV).
Local Abbreviation G_L'_ext := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ext s L az).
Local Abbreviation G_L'_ctx := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ctx s L az).
Local Abbreviation G_L'_reg_new := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_reg_new s L az).
Local Abbreviation G_L'_fp := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_fp X R U s L HI az).
Local Abbreviation G_L'_crange := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_crange X R U s L HI az).
Local Abbreviation G_L'_ub := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ub X R U s L HI HXr az).
Local Abbreviation G_L'_addr_of := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_addr_of s L az).
Local Abbreviation G_L'_pnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_pnew s L az).
Local Abbreviation G_L'_mnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_mnew s L az).
Local Abbreviation G_region_of_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_of_t1 s Hhd Hcnt Hbrk Hinit az G_al G_pos).
Local Abbreviation G_region_of_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_of_t2 s Hhd Hbrk Hinit az G_al G_pos).
Local Abbreviation G_layout_ok_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.layout_ok_t1 X R U s L HI Hhd Hcnt Hbrk Hinit HL az HB G_al G_pos G_ceil).
Local Abbreviation G_layout_ok_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.layout_ok_t2 X R U s L HI Hhd Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_region_live_t := (§8§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_live_t).
Local Abbreviation G_old_region_vs_grant := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_region_vs_grant s L vm az HV G_al G_pos G_free).
Local Abbreviation G_vm_okX_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_okX_t1 X R U s L HI Hhd Hcnt Hbrk Hinit vm az HV HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_ok_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_ok_t1 X R U s L HI Hhd Hcnt Hbrk Hinit C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_ledger_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ledger_t1 s L C_U vm az statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_okX_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_okX_t2 X R U s L HI Hhd Hcnt Hbrk Hinit vm az HV HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_ok_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_ok_t2 X R U s L HI Hhd Hcnt Hbrk Hinit C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_ledger_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ledger_t2 s L C_U vm az statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_fp_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_where s L C_U vm az HV HLG G_al G_pos).
Local Abbreviation G_maps_wf_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.maps_wf_t1 s L vm az HB HMW G_al G_pos G_ceil G_free).
Local Abbreviation G_maps_wf_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.maps_wf_t2 s L vm az HB HMW G_al G_pos G_ceil G_free).
Local Abbreviation G_block_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.block_where X R U s L HI HXr az G_pos).
Local Abbreviation G_grant_vs_block := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_block X R U s L HI HXr C_U vm az Hctx_C statics_in_image_U HV HIRv G_al G_pos G_free).
Local Abbreviation G_xraw_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.xraw_t1 X s HXr Hhd Hcnt Hbrk Hinit).
Local Abbreviation G_xraw_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.xraw_t2 X R U s HI HXr az).
Local Abbreviation G_mnew_notX := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew_notX X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_keys_t1 := (§6§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.keys_t1).
Local Abbreviation G_keys_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.keys_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az).
Local Abbreviation G_am_frame_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.am_frame_t1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_am_frame_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.am_frame_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_bounded34 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34).
Local Abbreviation G_bounded34_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34_t1 s L Hhd Hcnt Hbrk Hinit az HB G_al G_pos G_ceil).
Local Abbreviation G_bounded34_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_bounded_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded_t1 s L Hhd Hcnt Hbrk Hinit az HB G_al G_pos G_ceil).
Local Abbreviation G_bounded_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_cell_where1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.cell_where1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az G_al G_pos).
Local Abbreviation G_cell_where2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.cell_where2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az G_al G_pos).

    Lemma vm1_eq : ltac2:(tb__ "0|0|
S0S12aS12bS9dA1S117Vs;Vvm;S9bA3A3").
    Proof using Evm HMI HagL Hav Hev Hgd.
      unfold md1. rewrite m_vmmaps_with_vmmaps. unfold AllocMetaGrow.vm1, mmap_none_vm, AllocMetaGrow.wa, AllocMetaGrow.wn, wz.
      rewrite EL, mmap_n_eq, <- aw_eq, Evm, lenZ_eq. reflexivity.
    Qed.

    Lemma Pre_resok_eq : ltac2:(tb__ "0|0|
S0S2cSeaSbSe8SefA3Sf3S147S125A1Sf9P12cA1A2A3").
    Proof using . vm_compute. reflexivity. Qed.

    Lemma rhoU_300 : ltac2:(tb__ "0|0|
S0S6aQ40A1S2fSa1P12cA2Vaw;A3").
    Proof using . unfold rhoU, rho_after_unmap, rho_set_rw, AM_NEXT. cbn [rw]. rewrite Pos.eqb_refl. reflexivity. Qed.
    Lemma rhoU_low j : ltac2:(tb__ "0|0|
S14bVj;P12cA2S0S6aQ40A1S2fSa1Vj;A2S2fVrhoL;Vj;A2A3F_;").
    Proof using Hav Hev Hgd.
      intros Hj. unfold rhoU, rho_after_unmap, rho_set_rw, AM_NEXT. cbn [rw set_rm].
      destruct (Pos.eqb j 300) eqn:E; [apply Pos.eqb_eq in E; lia | reflexivity].
    Qed.
    Lemma agU : ltac2:(tb__ "0|0|
S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;S2aSa1A1A7Sa1A3").
    Proof using HagL Hav Hev Hgd.
      destruct HagL as (A1 & A2 & A3). split; [|split; [intros l; cbn; rewrite <- A2; reflexivity | intros x; reflexivity]].
      intros i Hi. rewrite rhoU_low by exact Hi. rewrite <- (A1 i Hi). reflexivity.
    Qed.

    Lemma page_facts_hold : ltac2:(tb__ "0|0|
S143S2bS3eSa1A1Sf9P12cA1A3").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      pose proof grant_facts as (Hal & Hpos & Hceil & _). pose proof lenZ_range as [LR _]. pose proof az64 as A64.
      unfold page_facts. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [SymState.holds eval]; rewrite rhoU_300.
      - rewrite (u64 4096) by lia. fold az. unfold PGSZ in Hal. Z.to_euclidean_division_equations; lia.
      - unfold ACEIL. rewrite (u64 0x7fffff800000) by lia. fold az. top_ranges. lia.
      - split; [lia|]. fold az. change (2 ^ 12) with 4096. unfold PGSZ in Hal. exact Hal.
    Qed.

    Lemma entry_resok : ltac2:(tb__ "0|1|
S73S13bSbS13cS131Vtr;S9dA2A1M0S147S125A1Sa1R1A5S13bSbG0SeaSbSe8SefA3Sa1R2A5F_;Fw;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      intros w [Hsm HJ]. split; [|exact HJ]. rewrite Pre_resok_eq. apply smatch_add_facts_app; [exact Hsm | apply page_facts_hold | vm_compute; reflexivity].
    Qed.

    Definition LOK : sstate := ltac2:(tb__ "0|0|
S15eSbbS15dS15fSeaSbSe8SefA3S15cA2Sf5SefA1A3A1").
    Lemma LOK_misc : ltac2:(tb__ "0|1|
S1S0S8S34S9fA1Z21ef8A3S1S0S23S27S9fZ11A2S21Ze2A1A3S1S0S23S27S9fZaA2S28S108S26P12cA1S21Z1000A1M0A3A3S1S0S23S27S9fZbA2G0A3S1S0S23S27S9fZcA2S21Z3A1A3S0S9S33S9fA1P12dA3A2A2A2A2A2").
    Proof using . vm_compute. repeat split; reflexivity. Qed.
    Lemma LOK_ecall : ltac2:(tb__ "0|0|
S0S13S10aA1S160SbS34S9fA1A2S19S10aS10cA2A3").
    Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.
    Lemma Pre_resok_fail_eq : ltac2:(tb__ "0|0|
S0S2cSeaSbSe8SedA3S148S9fS149A2A3").
    Proof using . vm_compute. reflexivity. Qed.
    Lemma Pre_resok_ok_eq : ltac2:(tb__ "0|0|
S0S2cSeaSbSe8Sf0A3S148S9fZ0A2A3").
    Proof using . vm_compute. reflexivity. Qed.

    Definition O_ctxOK : sobj := ltac2:(tb__ "0|4|
S44S21S101Se8A1A1S21Z18A1M0S21Z58A1S10S22S24S21Z50A1Z8M1S28S108S26P12cA1S21Z1000A1A3A3S10S22S24S21Z38A1G1S28S108Se9Pb8A1M2S21Z1A1A3A3S10S22S24S21Z30A1G1S28S108S28S109S21Z2A1G2A3S21N1A1A3A3S10S22S24G0G1S21Z0A1M3A3S10S22S24S21Z20A1G1Se9Pb0A1A3S10S22S24S21Z28A1G1G3A3S10S22S24S21Z40A1G1Se9Pb9A1A3S10S22S24S21Z48A1G1Se9PbaA1A3S16S22A1A3A3A3A3A3A3A3A3S3fA5").
    Definition O_brkD : sobj := ltac2:(tb__ "0|0|
SfbSe8S21SeeA1A2").
    Definition O_errF : sobj := ltac2:(tb__ "0|1|
S44S26P18A1S21Na4A1M0S21Na0A1S10S22S24G0Z4S21ZcA1A3S16S22A1A3S3fA5").
    Definition UNCH2 : list sobj := ltac2:(tb__ "0|0|
S10S20SfdSe8A1S10S20SfeS10S20SfaSe8A1S10S20S100Se8A1S10S20Sf4Se8Se9PafA1Z1A3S10S20Sa5S16S20A1A3A3A3A3A3A3").
    Definition stkOK_cells : list cell := ltac2:(tb__ "0|1|
S10S22S24S21N48A1Z8M0S21Z20edcA1A3S10S22S24S21N78A1G0S26P29A1A3S10S22S24S21N70A1G0S21SeeA1A3S10S22S24S21N68A1G0S21Z5a3c8A1A3S10S22S24S21N60A1G0Se9PadA1A3S10S22S24S21N58A1G0S28S109S21Z2A1Se9Pb8A1A3A3S10S22S24S21N50A1G0S21Z1000A1A3S10S22S24S21N8A1G0S26PbA1A3S10S22S24S21N10A1G0S26P1cA1A3S10S22S24S21N18A1G0S26P1dA1A3S10S22S24S21N20A1G0S26P26A1A3S10S22S24S21N28A1G0S26P27A1A3S10S22S24S21N30A1G0S26P28A1A3S10S22S24S21N38A1G0Se9PaeA1A3S16S22A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
    Lemma LOK_objs : ltac2:(tb__ "0|1|
S0S14S20A1S2dS9fA1S10S20Sf1SabA1S18S20S146S20U4S9cA3S18S20S10S20SfcS16S20A1M0A3S10S20Sf4Se8Se9PafA1Z1A3S10S20Sa6S10S20Sa5G0A3A3A3A3A3A3A3").
    Proof using . vm_compute. reflexivity. Qed.

    Definition valU (rhoX : valuation) : Prop := ltac2:(tb__ "0|0|
S1S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;S2aVrhoX;A1A7VrhoX;A3S0S6aQ40A1S2fVrhoX;P12cA2Vaw;A3A2").
    Lemma valU_rhoU : valU rhoU.
    Proof using HagL Hav Hev Hgd. split; [apply agU | apply rhoU_300]. Qed.
    Lemma valU_ext rhoX rhoY n : ltac2:(tb__ "0|0|
Sa2VrhoX;A1S14bP12cVn;A2S2eVn;VrhoX;VrhoY;A3Sa2VrhoY;A1F_;F_;F_;").
    Proof using Hav Hev Hgd.
      intros [(A1 & A2 & A3) A4] Hn (B1 & B2 & B3). split; [split; [|split]|].
      - intros i Hi. cbn [rho1 rw]. rewrite <- (B1 i) by (unfold AM_NEXT in Hi; lia). rewrite <- (A1 i Hi). reflexivity.
      - intros l. cbn. rewrite <- B2, <- A2. reflexivity.
      - intros x. reflexivity.
      - rewrite <- (B1 300%positive Hn). exact A4.
    Qed.

    Definition memU (m : word -> option byte) : Prop := ltac2:(tb__ "0|2|
S6aQ40M0A1S2S1S5dS9bS6cG0R1A2M1A2S5eG1S5cS9bS124Vs;A1A2A2A2A1S0S13S6aQ8A1A1Vm;R2A1VmW;R2A1A3F_;Fx;").
    Lemma memU_rhoU : memU (rm rhoU).
    Proof using HMI HagL Hav Hev Hgd.
      intros x Hx. unfold rhoU, rho_after_unmap, rho_set_rw. cbn [rm set_rm]. rewrite unmap_range_at.
      destruct (in_range aw (mmap_n (eval rhoL LENX)) x) eqn:E.
      - exfalso. apply in_range_spec in E. rewrite EL, mmap_n_lenZ in E. apply Hx. exact E.
      - destruct HagL as (_ & _ & M). rewrite <- (M x). reflexivity.
    Qed.

    Lemma evU rhoX e : ltac2:(tb__ "0|0|
Sa2VrhoX;A1S0S12S5aSebVe;A2S15A3S0S6aQ40A1S25VrhoX;Ve;A2S25S130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2A3F_;F_;").
    Proof using .
      intros [A _] He. rewrite <- (eval_agree AM_NEXT (rho1 (rm rhoX)) rhoX e A He). exact (eval_set_rm (rho1 mW) (rm rhoX) e).
    Qed.
    Lemma evU300 rhoX : ltac2:(tb__ "0|2|
Sa2VrhoX;A1S0S6aQ40M0A1S25VrhoX;S28S108S26P12cA1S21Z1000M1A1A3A2S6bG0S5cS9bG1A2A2A3F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      intros [_ A]. cbn [eval]. rewrite A. rewrite aw_eq. pose proof az64. pose proof grant_facts as (_ & _ & Hc & _). top_ranges. pose proof lenZ_range.
      apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, !u64 by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
    Qed.

    Lemma LOK_ranges rhoX : ltac2:(tb__ "0|2|
Sa2VrhoX;A1S0S14S17S8S8A2M0A1S145S20G0S29VrhoX;A1S2dS9fA1A4S10G0S11S8S8S5cS133Vrho;A1M1S132Vrho;A1A2G1A4S10G0S11S8S8Z28d50Z28d58A4S10G0S11S8S8Z5a338Z5a340A4S10G0S11S8S8Z5a360Z5a368A4S10G0S11S8S8Z5a388Z5a390A4S10G0S11S8S8Z3a02cZ3a030A4S10G0S11S8S8Z5a3d0Z5a3dcA4S10G0S11S8S8Z5a3e0Z5a420A4S10G0S11S8S8Z5a768Z5a770A4S16G0A1A3A3A3A3A3A3A3A3A3A3F_;").
    Proof using Hav Hev Hgd Htp mW.
      intros VU. rewrite LOK_objs. cbn [map firstn skipn app UNCH2].
      rewrite (ReabKit.range_ag (rho1 (rm rhoX)) rhoX [O_stk stkOK_cells] [] AM_NEXT (proj1 VU) ltac:(vm_compute; reflexivity) (O_stk stkOK_cells) ltac:(left; reflexivity)).
      change (obj_range (rho1 (rm rhoX)) (O_stk stkOK_cells)) with (obj_range (rho1 mW) (O_stk stkOK_cells)). rewrite rng_stk.
      unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctxOK, O_brkD, O_brk. cbn [am_got am_libc am_ctx AM_P].
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
      assert (EL0 : forall z, eval rhoX (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
      rewrite (evU rhoX (v 173) VU eq_refl), ev173. rewrite (evU rhoX (SVar 24) VU eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.

    Lemma segs_inside : ltac2:(tb__ "0|1|
S0S12SbaS164S164S1fS64Z10000S67S165R1A1A1M0A2S64S5cG0S67S166R1A1A1A2Z5b000A2A2Lseg;SbA3S15A3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma ro_addr_grant (x : word) : ltac2:(tb__ "0|1|
S1S5dS9bS6cQ40Vx;A2M0A2S5eG0S5cS9bS124Vs;A1A2A2A2S0S12S57SbVx;A2S1eA3F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      intros Hx. apply ro_addr_false_of_no_segment.
      destruct (find_segment segsU (bv_unsigned x) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
      destruct (ClientLaws.find_segment_In _ _ _ _ E) as (Hin & H1 & H2).
      pose proof (proj1 (forallb_forall _ _) segs_inside seg Hin) as Q. apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2.
      apply (MISSIMG (bv_unsigned x)); [cbn [mc_img_lo mc_img_hi C_U]; lia|].
      rewrite EL, mmap_n_lenZ. fold az. exact Hx.
    Qed.
    Lemma LOK_objs_miss rhoX : ltac2:(tb__ "0|2|
Sa2VrhoX;A1S20Sb9S20R1S2dS9fA1A3S48S29VrhoX;R2A2S11S8S8S5cS9bZ1000M0A2M1S5cG1G0A2A4A2F_;Fo;F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl Htp STK.
      intros VU o Ho. pose proof (in_map (obj_range rhoX) _ _ Ho) as RO. rewrite (LOK_ranges rhoX VU) in RO.
      pose proof STK as (S1 & S2 & S3 & S4). pose proof grant_facts as (_ & Hpos & Hceil & _). pose proof lenZ_range as [LR _].
      pose proof MISSIMG as MISS.
      rewrite EL, mmap_n_lenZ in MISS. fold az in MISS. cbn [mc_img_lo mc_img_hi C_U] in MISS. clear - RO MISS Hceil S2 Hpos LR. top_ranges.
      assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (az + 4096, az + 4096 + 4096)).
      { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
        destruct (Z_le_dec hi (az + 4096)); [lia|]. destruct (Z_le_dec (az + 4096 + 4096) lo); [lia|]. exfalso.
        destruct (Z_le_dec (az + 4096) lo); [apply (MISS lo); lia | apply (MISS (az + 4096)); lia]. }
      destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
      repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
    Qed.

    Definition md2 : Model := ltac2:(tb__ "0|2|
S15bS9dS6bQ40M0S5cS9bZ1000M1A2A2S6bG0G1A2A3").
    Definition OKC : assn := ltac2:(tb__ "0|6|
S73S3S30S30S1Sa2R1A1S1Sa7S2aR1A1A1S1S6aQ40M0A1S1S5dS5cS9bZ1000M1A2M2S6cG0R1A2M3A2S5eG3S5cG2G1A2A2A2S0S13S6aQ8M4A1M5A1S2aR3R2A2S19G5S6bG4Z0A2A2A3F_;Fx;S13bSbS13cS131Vtr;SaaA2A1SeaSbSe8Sf0A3R1R2A5A2A2A2LrhoK;A2Lw;").

    Lemma mmap_nZ_4096 : mmap_nZ (Z_to_bv 64 4096) = 4096. Proof using . vm_compute. reflexivity. Qed.
    Lemma mmap_n_4096 : mmap_n (Z_to_bv 64 4096) = Z_to_bv 64 4096. Proof using . unfold mmap_n. rewrite mmap_nZ_4096. reflexivity. Qed.

    Lemma map_contains_head (e : word * word) l lo n : ltac2:(tb__ "0|4|
S5dS6cQ40M0S1bS6aG0A1M1G1Ve;A3A2M2S6cG0Vlo;A2M3A2S5dS5cG3S6cG0Vn;A2A2S5cG2S6cG0S1cG1G1Ve;A3A2A2A2S0S12S12fS10S17G1G1A2Ve;Vl;A3Vlo;Vn;A3S15A3F_;F_;").
    Proof using .
      intros H1 H2. unfold map_contains. cbn [existsb]. apply Bool.orb_true_iff. left.
      apply andb_true_intro; split; apply Z.leb_le; assumption.
    Qed.

    Theorem stepBC : ltac2:(tb__ "0|1|
S1aS73S74SbVok;R2S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A4S74SbVok;R3Sa3A4S1aS73S150R2R6A2S3S30S30S1Sa2R1A1S1Sa7S2aR1A1A1S13bSbS13cS131Vtr;S9dA2A1M0SeaSbSe8SedA3R1R3A5A2A2LrhoF;A2S75SbVok;R4R3A4F_;F_;Fw';Fm;S13bSbG0S147S125A1Sa1R4A5S75SbVok;R6R5A4F_;F_;F_;F_;Fw;Fn;").
    Proof using Evm HKc HMI HOK HagL Hav Hev Hgd Hpl Htp STK.
      intros n w HQ HC HF Hw. pose proof grant_facts as (Hal & Hpos & Hceil & _). pose proof lenZ_range as [LR LA]. pose proof az64 as A64.
      assert (K1 : Kc tr md1) by (apply (Kc_vm md1 HKc); eexists; reflexivity).
      pose proof (alloc_meta_run_P A78_res_ok ok (Kexact tr md1) rhoU (ok_frame_exact ok Kc tr md1 HOK K1)) as RUN1.
      refine (RUN1 n _ w (entry_resok w Hw)).
      intros [tr1 [ms1 mdx]] (Lf & rhoX & HinL & HagX & HsmX & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LOK) by (unfold LOK; rewrite EP; reflexivity). rewrite ELF in HsmX. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmX.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagX.
      pose proof (valU_ext rhoU rhoX 301 valU_rhoU ltac:(reflexivity) HagX) as VX.
      destruct n as [|m]; [exact I|].
      pose proof LOK_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
      refine (triple1_mprotect_exposeJ segsU ok (liftK (Kexact tr md1)) (liftK (Kexact tr md1)) (liftK (Kexact tr md2))
                LOK rhoX (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md1 HOK K1)) (ok_pframe_exact md1 K1) LOK_ecall M17 _ m _
                (tr, mkCfg ms1 md1) (conj HsmX (conj eq_refl eq_refl))).
      -
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
        change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
        rewrite M10, (evU300 rhoX VX) in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
        pose proof (LOK_objs_miss rhoX VX) as MISS. pose proof ro_addr_grant as ROG. pose proof EL as EL'. pose proof mmap_n_lenZ as MN.
        clear Hsp HsmX HagX RUN1 Hw HQ HC HF VX ELF EP.
        rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
        assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
        assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
        assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
        rewrite ?U1, ?U2, ?U3.
        split; [reflexivity|]. split; [unfold page_size; unfold PGSZ in Hal; clear - Hal; Z.to_euclidean_division_equations; lia|].
        split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
        split; [unfold two_pow_64; clear - Hceil LR A64; top_ranges; lia|].
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_noaccess]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_maps]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split; [split; reflexivity|].
        intros _. split; [exact MISS|]. split; [intros x Hx; apply ROG; clear - Hx LR; lia|].
        split; reflexivity.
      -
        assert (MX : memU (rm rhoX)).
        { intros x Hx. destruct HagX as (_ & _ & M). rewrite <- (M x). exact (memU_rhoU x Hx). }
        intros w2 [HF2 | HO2].
        +
          apply (HF m w2); [apply Nat.le_succ_diag_r|]. exists rhoX. split; [exact VX|]. split; [exact MX|].
          rewrite Pre_resok_fail_eq. exact HF2.
        +
          apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HC.
          exists (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))).
          rewrite M10, M11, (evU300 rhoX VX). cbn [eval]. rewrite mmap_n_4096.
          assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
          split; [|split; [|split]].
          * destruct VX as [(A1 & A2 & A3) A4]. split; [split; [exact A1|split; [exact A2|intros x; reflexivity]]| exact A4].
          * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
            destruct (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) eqn:E; [|exact (MX x Hx)].
            exfalso. apply in_range_spec in E. rewrite U1 in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. apply Hx. clear - E LR. lia.
          * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
            replace (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) with true; [reflexivity|].
            symmetry. apply in_range_spec. rewrite U1. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
          * rewrite Pre_resok_ok_eq. rewrite M10, M11, (evU300 rhoX VX) in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. exact HO2.
    Qed.

    Theorem stepBC_S : ltac2:(tb__ "0|2|
S1aS73S0S12S15aS9dS6bQ40M0S5cS9bZ1000M1A2A2S6bG0G1A2A3S15A3S74SbVok;R3Sa3A4S13bSbS13cS131Vtr;S9dA2A1S147S125A1Sa1R3A5S75SbVok;R5R4A4F_;F_;F_;Fw;Fn;").
    Proof using Evm HKc HMI HOK HagL Hav Hev Hgd Hpl Htp STK.
      intros n w HB HC Hw. pose proof grant_facts as (Hal & Hpos & Hceil & _). pose proof lenZ_range as [LR LA]. pose proof az64 as A64.
      assert (K1 : Kc tr md1) by (apply (Kc_vm md1 HKc); eexists; reflexivity).
      pose proof (alloc_meta_run_P A78_res_ok ok (Kexact tr md1) rhoU (ok_frame_exact ok Kc tr md1 HOK K1)) as RUN1.
      refine (RUN1 n _ w (entry_resok w Hw)).
      intros [tr1 [ms1 mdx]] (Lf & rhoX & HinL & HagX & HsmX & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LOK) by (unfold LOK; rewrite EP; reflexivity). rewrite ELF in HsmX. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmX.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagX.
      pose proof (valU_ext rhoU rhoX 301 valU_rhoU ltac:(reflexivity) HagX) as VX.
      destruct n as [|m]; [exact I|].
      pose proof LOK_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
      refine (triple1_mprotect_exposeJ_forced segsU ok (liftK (Kexact tr md1)) (fun _ _ _ => False) (liftK (Kexact tr md2))
                LOK rhoX (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md1 HOK K1)) (ok_pframe_exact md1 K1) LOK_ecall M17 _ m _
                (tr, mkCfg ms1 md1) (conj HsmX (conj eq_refl eq_refl))).
      -
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
        change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
        rewrite M10, (evU300 rhoX VX) in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
        pose proof (LOK_objs_miss rhoX VX) as MISS. pose proof ro_addr_grant as ROG. pose proof EL as EL'. pose proof mmap_n_lenZ as MN.
        pose proof HB as HB'.
        clear Hsp HsmX HagX RUN1 Hw HC VX ELF EP HB.
        rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
        assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
        assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
        assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
        rewrite ?U1, ?U2, ?U3.
        split; [reflexivity|]. split; [unfold page_size; unfold PGSZ in Hal; clear - Hal; Z.to_euclidean_division_equations; lia|].
        split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
        split; [unfold two_pow_64; clear - Hceil LR A64; top_ranges; lia|].
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_noaccess]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_maps]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split; [intros Hb; rewrite ?mmap_n_4096 in Hb; rewrite HB' in Hb; discriminate Hb|].
        intros _. split; [exact MISS|]. split; [intros x Hx; apply ROG; clear - Hx LR; lia|].
        split; reflexivity.
      -
        assert (MX : memU (rm rhoX)).
        { intros x Hx. destruct HagX as (_ & _ & M). rewrite <- (M x). exact (memU_rhoU x Hx). }
        intros w2 [HF2 | HO2].
        + destruct HF2 as [_ F]. exact (False_ind _ F).
        +
          apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HC.
          exists (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))).
          rewrite M10, M11, (evU300 rhoX VX). cbn [eval]. rewrite mmap_n_4096.
          assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
          split; [|split; [|split]].
          * destruct VX as [(A1 & A2 & A3) A4]. split; [split; [exact A1|split; [exact A2|intros x; reflexivity]]| exact A4].
          * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
            destruct (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) eqn:E; [|exact (MX x Hx)].
            exfalso. apply in_range_spec in E. rewrite U1 in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. apply Hx. clear - E LR. lia.
          * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
            replace (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) with true; [reflexivity|].
            symmetry. apply in_range_spec. rewrite U1. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
          * rewrite Pre_resok_ok_eq. rewrite M10, M11, (evU300 rhoX VX) in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. exact HO2.
    Qed.

    Definition LRF2 : sstate := ltac2:(tb__ "0|0|
S15eSbbS15dS15fSeaSbSe8SedA3S15cA2Sf5SedA1A3A1").
    Definition stkRF2_cells : list cell := ltac2:(tb__ "0|2|
S10S22S24S21N60A1Z8M0S21Z1000A1M1A3S10S22S24S21N58A1G0S21Z21f00A1A3S10S22S24S21N48A1G0S21Z20edcA1A3S10S22S24S21N78A1G0S26P29A1A3S10S22S24S21N70A1G0S21SeeA1A3S10S22S24S21N68A1G0S21Z5a3c8A1A3S10S22S24S21N50A1G0G1A3S10S22S24S21N8A1G0S26PbA1A3S10S22S24S21N10A1G0S26P1cA1A3S10S22S24S21N18A1G0S26P1dA1A3S10S22S24S21N20A1G0S26P26A1A3S10S22S24S21N28A1G0S26P27A1A3S10S22S24S21N30A1G0S26P28A1A3S10S22S24S21N38A1G0Se9PaeA1A3S16S22A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
    Definition CHG2 : list sobj := ltac2:(tb__ "0|0|
S10S20Sa9S10S20Sa6S16S20A1A3A3").
    Definition OBJ2 : list sobj := ltac2:(tb__ "0|1|
S10S20Sf1Sa8A1S18S20S146S20U4S9cA3S18S20S10S20Sa9S16S20A1M0A3S10S20Sf4Se8Se9PafA1Z1A3S10S20Sa6S10S20Sa5G0A3A3A3A3A3A3").
    Lemma LRF2_objs : ltac2:(tb__ "0|0|
S0S14S20A1S2dSa0A1Sa4A3").
    Proof using . vm_compute. reflexivity. Qed.
    Lemma LRF2_misc : ltac2:(tb__ "0|0|
S1S0S8S34Sa0A1Z20ec8A3S1S0S9S33Sa0A1P12dA3S1S0S14S23A1S37Sa0A1SfA3S1S0S58S36Sa0A1S40A3S1S0S13S23A1S38Sa0A1S1dS23A1A3S0S23S27Sa0ZaA2S21Z0A1A3A2A2A2A2A2").
    Proof using . vm_compute. repeat split; reflexivity. Qed.
    Lemma LRF2_cs : ltac2:(tb__ "0|0|
S8S1S5dZ1R1A2S5dR1Z1fA2A2S0S12SdS62R2A1A1S15A3S0S23S27Sa0R3A2SeS62R3A1A1A3F_;F_;Fz;").
    Proof using Hav Hev Hgd.
      intros z Hz Hcs.
      pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LRF2 z) (pre_reg (Z.to_nat z)))%bool 1 31
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
      cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
    Qed.
    Lemma OBJ2_perm o : ltac2:(tb__ "0|0|
S7Sb9S20Vo;Sa4A3Sb9S20Vo;S10S20Sf1Sa8A1S18S20S9cS9eA3A3A3A2").
    Proof using Hgd STK. unfold OBJ2, UNCH2, CHG2. cbn [firstn app In]. tauto. Qed.

    Section FailLeaf2.
      Variables (msF : machine_state) (rhoF : valuation).
      Hypothesis VF : valU rhoF.
      Hypothesis MF : memU (rm rhoF).
      Hypothesis HsmF : ltac2:(tb__ "0|0|
S32SbVrhoF;Sa0S11S14S128A1S138Vtr;S139VmsF;S9dA2A4A4").

      Let rhoW : valuation := rho1 (rm rhoF).
      Lemma HagF : ltac2:(tb__ "0|0|
S2eSebVrhoW;VrhoF;A3"). Proof using VF. exact (proj1 VF). Qed.
      Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
      Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
      Lemma HOF : ltac2:(tb__ "0|0|
S143S20S31SbVrhoF;VmsF;A3Sa4A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. rewrite LRF2_objs in Hall. exact Hall. Qed.
      Lemma HfrF : ltac2:(tb__ "0|0|
S6aQ40A1S53VrhoF;Sa4R1A3S0S13S6aQ8A1A1S174VmsF;R2A2S2aVrhoF;R2A2A3F_;Fx;").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. rewrite LRF2_objs in Hfr. exact Hfr. Qed.
      Lemma F_pc : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S175VmsF;A1S6bG0Z20ec8A2A3").
      Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LRF2_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
      Lemma F_pend : ltac2:(tb__ "0|1|
S0S13S6aQ40A1M0A1S176VmsF;A1S1dG0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
      Lemma F_halt : model_idle md1. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
      Lemma F_regs : ltac2:(tb__ "0|0|
S54VrhoF;Sa0VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
      Lemma F_fregs : ltac2:(tb__ "0|0|
S4fVrhoF;Sa0VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
      Lemma F_fcsr : ltac2:(tb__ "0|0|
S4dVrhoF;S40VmsF;A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LRF2_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
      Lemma F_resv : ltac2:(tb__ "0|0|
S55VrhoF;S1dS23A1VmsF;A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LRF2_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

      Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S17aVrhoF;VmsF;S9cS9eA4").

      Lemma hold_rm_irrel o : ltac2:(tb__ "0|1|
S0S12S110S9S15L_;Vo;A2S15A3S31SbS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S155Vms;VmW;A2M0Vo;A4S31SbVrhoW;G0Vo;A4F_;F_;").
      Proof using rhoF. intros Hv Ho. apply (obj_holds_agree_vars segsU (fun _ => true) (rho1 mW) rhoW (with_mem ms mW) o); [intros; reflexivity | intros; reflexivity | exact Hv | exact Ho]. Qed.
      Lemma evM64 m : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S25S130Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S21SeeA1A2S6bG0S137Vs;VL;A2A2A3").
      Proof using Hbrk. unfold brkZ. rewrite Hbrk. apply bv_eq. reflexivity. Qed.
      Lemma KU_entry : ltac2:(tb__ "0|0|
S143S20S31SbVrhoW;S155Vms;VmW;A2A3S9cA3").
      Proof using Erd Ewok HMI Hav Hav_rd Hbrk Hev Hgd Hgd_rd Hinit Hrom rho rhoF.
        unfold UNCH2. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
        repeat (constructor; [apply hold_rm_irrel; [reflexivity|]|]); [apply hold_got | apply hold_guard | apply hold_auxvp | apply hold_pgsz | exact HS | apply hold_brkE; apply evM64 | constructor].
      Qed.
      Lemma KU_leaf : ltac2:(tb__ "0|0|
S143S20S31SbVrhoF;VmsF;A3S9cA3").
      Proof using Hgd HsmF STK. apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). apply OBJ2_perm. right. apply in_app_iff. left. exact Ho. Qed.
      Lemma KC_leaf : ltac2:(tb__ "0|0|
S143S20S31SbVrhoF;VmsF;A3S9eA3").
      Proof using Hgd HsmF STK. apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). apply OBJ2_perm. right. apply in_app_iff. right. exact Ho. Qed.
      Lemma Kcov : ltac2:(tb__ "0|0|
S0S12SbaS20S179S9cA3S15A3"). Proof using . vm_compute. reflexivity. Qed.
      Lemma Klits : ltac2:(tb__ "0|0|
S0S12SbaS20S17bS18S20S9cS9eA3A3S15A3"). Proof using . vm_compute. reflexivity. Qed.
      Lemma Kdunk : ltac2:(tb__ "0|1|
S0S12SbaS20S20S47S12Lx;S51R1A1S15S1eS1eS9S1eLl;M0G0S8S23S14S17S8S8A2A1S14S5bA1S1eLtmpl;Lflds;Lcnt;Lesz;X47x6Lo;S18S20S9cS9eA3A3S15A3"). Proof using . reflexivity. Qed.

      Lemma Kvars301 : ltac2:(tb__ "0|0|
S0S12SbaS20S52P12dA1S18S20S9cS9eA3A3S15A3"). Proof using . vm_compute. reflexivity. Qed.
      Lemma HagF301 : ltac2:(tb__ "0|0|
S2eP12dS168VrhoW;P12cVaw;A3VrhoF;A3").
      Proof using Hav Hev Hgd VF.
        destruct VF as [(A1 & A2 & A3) A4]. split; [|split; [exact A2 | exact A3]].
        intros i Hi. unfold rho_set_rw. cbn [rw]. destruct (Pos.eqb i 300) eqn:E.
        - apply Pos.eqb_eq in E. subst i. symmetry. exact A4.
        - apply A1. apply Pos.eqb_neq in E. unfold AM_NEXT. lia.
      Qed.
      Let rhoW' : valuation := ltac2:(tb__ "0|0|
S168VrhoW;P12cVaw;A3").
      Lemma KU_entry' : ltac2:(tb__ "0|0|
S143S20S31SbVrhoW';S155Vms;VmW;A2A3S9cA3").
      Proof using Erd Ewok HMI Hav Hav_rd Hbrk Hev Hgd Hgd_rd Hinit Hrom aw rhoW.
        apply Forall_forall. intros o Ho. apply (obj_holds_agree segsU AM_NEXT rhoW rhoW' (with_mem ms mW) o).
        - split; [|split; [intros; reflexivity | intros; reflexivity]]. intros i Hi. unfold rhoW', rho_set_rw. cbn [rw].
          destruct (Pos.eqb i 300) eqn:E; [apply Pos.eqb_eq in E; unfold AM_NEXT in Hi; lia | reflexivity].
        - revert o Ho. apply forallb_forall. vm_compute. reflexivity.
        - exact (proj1 (Forall_forall _ _) KU_entry o Ho).
      Qed.

      Lemma KIT_unch : ltac2:(tb__ "0|2|
S20S8Sb9S20R2S9cA3S1S5dS1bS8S8S29VrhoF;R3A2M0A3R2A2S5eR2S1cS8S8G0A3A2A2S1S0S13S6aQ8A1A1S106SbS119S6bQ40R3A2M1A3S106SbVmW;G1A3A3S0S12S107SbS119G1A3S107SbVmW;G1A3A3A2F_;F_;Fx;Fo;").
      Proof using Erd Ewok HMI Hav Hav_rd Hbrk Hev Hgd Hgd_rd Hinit Hrom HsmF STK VF rhoW'. exact (ReabKit.unch_same segsU rhoW' rhoF ms msF mW Hrom HromF UNCH2 CHG2 KU_entry' KU_leaf 301 HagF301 Kvars301 Kcov Klits Kdunk). Qed.
      Lemma KIT_chgb : ltac2:(tb__ "0|3|
S20S8Sb9S20R2S9eA3S1S5dS1bS8S8S29VrhoF;R3A2M0A3R2A2S5eR2S1cS8S8G0A3A2A2S1S0S12S107SbS119S6bQ40M1R3A2A3S15A3S3S6aQ8A1M2G2S0S13G2A1S106SbS119S6bG1R4A2A3S19G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
      Proof using Hgd HsmF STK. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH2 CHG2 KC_leaf Kdunk). Qed.
      Lemma KIT_chgc : ltac2:(tb__ "0|3|
S20S22S1aSb9S20R3S9eA3Sb9S22R3S46R4A1A3S14fR3S62S3dR4A1A1A2S0S13S6aQ8M0A1M1A1S106SbS119S6bQ40M2S5cS5cS6cG2S25VrhoW';S45R6A1A2A2S3aVrhoW';S42R5A1A2A2S60R4A1A2A2A3S19G1S144G1R4S4cS62S3dR5A1A1S25VrhoF;S43R5A1A2A2S6bG0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
      Proof using Hav Hev Hgd HsmF STK VF rhoW. exact (ReabKit.chg_cell segsU rhoW' rhoF msF HromF UNCH2 CHG2 KC_leaf 301 HagF301 Kvars301). Qed.

      Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S4S1S5dZ3a02cVx;A2S5eVx;Z3a030A2A2S4S1S5dZ5a3e0Vx;A2S5eVx;Z5a420A2A2S1S5dS9bVx;A2S5eVx;S5cS9bS124Vs;A1A2A2A2A2A2").
      Lemma touched_dec x : ltac2:(tb__ "0|1|
S163S11aVx;A1M0S2G0A1A2").
      Proof using . unfold touched. apply or_dec; [apply range_dec|]. apply or_dec; apply range_dec. Qed.
      Lemma evF_lit z : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S25VrhoF;S21Vz;A1A2S6bG0Vz;A2A3"). Proof using . reflexivity. Qed.
      Lemma evF_v j : ltac2:(tb__ "0|1|
S14bVj;P12cA2S0S6aQ40A1S25VrhoF;Se9Vj;A1M0A2S25S130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;").
      Proof using VF. intros Hj. apply (evU rhoF (v j) VF). cbn. unfold AM_NEXT. apply Pos.ltb_lt. exact Hj. Qed.
      Lemma CHG_ranges : ltac2:(tb__ "0|1|
S0S14S17S8S8A2M0A1S145S20G0S29VrhoF;A1S9eA4S10G0S11S8S8Z3a02cZ3a030A4S10G0S11S8S8Z5a3e0Z5a420A4S16G0A1A3A3A3").
      Proof using Hav Hev Hgd Htp VF mW.
        cbn [map CHG2]. unfold O_errF, O_ctxOK. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi am_ctx AM_P]. rewrite !evF_lit, !soff_lit_small by lia.
        rewrite (evU rhoF (SVar 24) VF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
      Qed.
      Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S0S14S17S8S8A2M0A1S145S20G0S29VrhoF;A1S9cA4S10G0S11S8S8Z28d50Z28d58A4S10G0S11S8S8Z5a338Z5a340A4S10G0S11S8S8Z5a360Z5a368A4S10G0S11S8S8Z5a388Z5a390A4S10G0S11S8S8Z5a3d0Z5a3dcA4S10G0S11S8S8Z5a768Z5a770A4S16G0A1A3A3A3A3A3A3A3").
      Proof using Hav Hev Hgd VF mW.
        cbn [map UNCH2]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_sec, O_brkD, O_brk. cbn [am_got am_libc am_ctx AM_P].
        unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
        rewrite (evU rhoF (v 173) VF eq_refl), ev173. rewrite !u64 by (cbn; lia). reflexivity.
      Qed.
      Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S1S5dZ0Vx;A2S5eVx;S5fZ2Z40A2A2A2S177VrhoF;S18S20S9cS9eA3S6bQ40Vx;A2A3S4S3S20S20S1Sb9S20R1S9cA3S1S5dS1bS8S8S29VrhoF;R1A2M0A3Vx;A2S5eVx;S1cS8S8G0A3A2A2A2Lo;A2S11aVx;A1A2F_;F_;").
      Proof using Hav Hev Hgd Htp VF mW.
        intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
        pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
        destruct M as [E|[E|[]]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
      Qed.
      Lemma touched_in x : ltac2:(tb__ "0|1|
S11aVx;A1S2S1S5dS9bVx;A2S5eVx;S5cS9bS124Vs;A1A2A2A2A1S3S20S20S1Sb9S20R1S9eA3S1S5dS1bS8S8S29VrhoF;R1A2M0A3Vx;A2S5eVx;S1cS8S8G0A3A2A2A2Lo;A2F_;F_;").
      Proof using Hav Hev Hgd Htp STK VF mW.
        intros T NG. unfold touched in T.
        pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as C0. pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as C1. cbn [nth map CHG2] in C0, C1.
        destruct T as [T|[T|T]]; [exists O_errF | exists O_ctxOK | exfalso; exact (NG T)]; (split; [cbn; tauto|]); [rewrite C0 | rewrite C1]; cbn [fst snd]; lia.
      Qed.

      Let bv1 : byteview := ltac2:(tb__ "0|0|
SadS106SbS119A2S107SbS119A2A2").
      Let rv1 : byteview := ltac2:(tb__ "0|0|
SadS106SbS119A2S6aQ40A1S15L_;A2").
      Let rv0 : byteview := ltac2:(tb__ "0|0|
SadS106SbVmW;A2S6aQ40A1S15L_;A2").

      Theorem V1 : ltac2:(tb__ "0|1|
S8S1S5dZ0R1A2S5eR1S5fZ2Z40A2A2A2S2S11aR2A1A1S1S0S13S8A1M0Vbv1;R3A1Vbv0;R3A1A3S0G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
      Proof using Erd Ewok HMI Hav Hav_rd Hbrk Hev Hgd Hgd_rd Hinit Hrom HsmF Htp MF STK VF rhoW'.
        intros x Hx NT.
        assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
        { destruct (in_ranges_dec rhoF (UNCH2 ++ CHG2) (Z_to_bv 64 x)) as [IN|OUT].
          - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
          - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH2 CHG2 _ OUT).
            rewrite (MF (Z_to_bv 64 x)) by (rewrite u64 by lia; intros G; apply NT; right; right; exact G). auto. }
        destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
      Qed.

      Theorem VM : ltac2:(tb__ "0|0|
S8S1S5dZ0R1A2S5eR1S5fZ2Z40A2A2A2S11aR2A1Se0S111Vs;VL;S9bA3S113Vs;A1R3A3S2S0S13S8A1Vbv1;R4A1S1dS8A1A3A1F_;F_;F_;Fx;").
      Proof using Evm HI HMI HagL Hav Hbrk Hcnt Hev Hgd Hhd Hinit Hpl HsmF Htp STK VF.
        intros x Hx T [(e & He & Rx) _].
        assert (NG : ~ (az <= x < az + lenZ78)).
        { rewrite G_fp_t1 in He. rewrite (G_L'_fp e He) in Rx. rewrite lenZ_eq. exact (G_grant_vs_footprint e x He Rx). }
        destruct (touched_in x T NG) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
        unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
        cbn [andb]. rewrite W, Hb. discriminate.
      Qed.

      Lemma leaf_cell (oF : sobj) (cF : cell) (o : Z) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|5|
Sb9S20VoF;S9eA3Sb9S22VcF;S46VoF;A1A3S0S8S3dVcF;A1S60Vw;A1M0A3S150Vw;U8A2Sc4OLval;Vval;S8S5Lz0;S78S5Lp;S8S6Lz0;S5Xc4x4S0S8Sc1S111Vs;VL;S9bA3M1Vval;A2Vz;A3S0S8S5cS6cQ40M2S25VrhoW';S45VoF;A1A2A2S3aVrhoW';S42VcF;A1A2A2S5cSceVL;A1Vo;A2M3A3S1S5dS1bS8S8S29VrhoF;VoF;A2M4A3G3A2S5dS5cG3G0A2S1cS8S8G4A3A2A2S0S6aG2A1S25VrhoF;S43VcF;A1A2S6bG2Vz;A2A3ScbG1Vbv1;SbeSbdVo;A1Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
      Proof using Hav Hev Hgd HsmF STK VF rhoW.
        intros HoF HcF Hw Hw8 Hval Hz Haddr Hrng Hevl. subst z.
        unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w loc_addr]. rewrite G_L'_ctx.
        assert (BYTE : forall k, (k < w)%nat -> bv1 (ly_ctx L + o + Z.of_nat k) = Some (le_byte (sval_num G_L' val) w k)).
        { intros k Hk.
          pose proof (KIT_chgc oF cF k HoF HcF ltac:(rewrite Hw, Nat2Z.id; exact Hk)) as RD. rewrite Haddr, Hw, Nat2Z.id, Hevl in RD.
          rewrite nth_enc_bytes in RD by assumption.
          destruct (KIT_chgb oF (ly_ctx L + o + Z.of_nat k) HoF ltac:(lia)) as [W _].
          unfold bv1, byteview_of.
          assert (R64 : 0 <= ly_ctx L + o + Z.of_nat k < 2 ^ 64).
          { pose proof (proj1 (Forall_forall _ _) KC_leaf oF HoF) as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hrng, R0, R1. cbn [fst snd] in Hrng. lia. }
          replace ((0 <=? ly_ctx L + o + Z.of_nat k) && (ly_ctx L + o + Z.of_nat k <? 2 ^ 64))%bool with true
            by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. rewrite W, RD. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
          change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
        destruct val; try (exact BYTE); destruct Hval.
      Qed.

      Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
S10SbcSbeSbdSddA1U8M0S12Sc4L_;M1S90Vu;A1M2SdfSbfZ0M3A1M4X12x2A3S10SbcSbeSbdSd8A1U4M5SbfS12S8L_;G2Z1G3X12x2A1A3S10SbcSbeSbdSdcA1G5SbfS82Vu;A1A1A3S10SbcSbeSbdSd7A1G0Sc3S81Vu;A1A1A3S10SbcSbeSbdSd2A1G0S14S78A1M6Sc4Lx;S7aVu;A1M7G4S78G6Sc6S7fVu;A1A1Ll;Ls0;X14x2A3S10SbcSbeSbdSd5A1G0SbfS8eVu;A1A1A3S10SbcSbeSbdSd3A1G0SbfS8cVu;A1M8A1A3S10SbcSbeSbdSd9A1G0SbfS7bVu;A1A1A3S10SbcSbeSbdSdaA1G0Sc3S7eVu;A1A1A3S10SbcSbeSbdSdbA1G0Sc3S79Vu;A1A1A3S10SbcSbeSbdSd4A1G0G1S1fG6S12Lx;G7S15S78G6S1eLl;Ls0;X14x2S65G8G3A2A2G4Sc6S8dVu;A1A1X12x2A3S10SbcSbeSbdSc8A1U1SbfS83Vu;A1A1A3S10SbcSbeSbdSd6A1G0S7dSc4Lx;S80Vu;A1G4SbfN1A1S1aS8Sc6S95R2S66S87R1A2A2A1Lp;Lr;X7dx3A3S16SbcA1A3A3A3A3A3A3A3A3A3A3A3A3A3").
      Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
Sb9SbcVc;SccVu;A1A3S0Sc0Sc7Vc;A1SbdVo;A1A3S4S5eVo;Sd1A2S5dSc8Vo;A2A2Sb9SbcVc;S11dVu;A1A3F_;F_;F_;").
      Proof using Hav Hev Hgd.
        intros Hin Hloc Ho. unfold ctx_cells in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
        unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
        apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
          apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
      Qed.
      Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
Sb9SbcVc;SccVu;A1A3S150Sd0Vc;A1U8A2F_;").
      Proof using Hav Hev Hgd.
        intros Hin. unfold ctx_cells in Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
        apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
          apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
      Qed.

      Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.
      Lemma B_ctxW : ltac2:(tb__ "0|1|
S0S8S6cQ40S25VrhoW';S21Z5a3c8M0A1A2A2G0A3"). Proof using Hav Hev Hgd aw rhoW. cbn [eval]. apply u64. lia. Qed.

      Lemma ev_acount : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S25VrhoF;S28S108S28S109S21Z2A1Se9Pb8A1A3S21N1A1A3A2S6bG0S61S156Vs;A1Z1A2A2A3").
      Proof using HI HMI Hav Hev Hgd VF mW.
        pose proof HB as (_ & SH & _). pose proof G_res_n_ge2 as R2.
        rewrite (evU rhoF (SAlu ALU_ADD (SAlu ALU_SLL (SLit 2) (v 184)) (SLit (-1))) VF eq_refl). rewrite (ev1 mW) by reflexivity. f_equal.
        cbn [zeval zalu]. rewrite ze_v, (zr1_var 184 _ eq_refl).
        assert (P27 : 2 <= 2 * 2 ^ st_meta_alloc_shift s <= 2 ^ 35).
        { split; [assert (1 <= 2 ^ st_meta_alloc_shift s) by (apply (Z.pow_le_mono_r 2 0); lia); lia|].
          change (2 ^ 35) with (2 * 2 ^ 34). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
        rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia. rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia.
        rewrite (Z.mod_small (st_meta_alloc_shift s) 64) by lia. change (2 mod 2 ^ 64) with 2.
        rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (2 * _)) by lia. unfold res_n. rewrite Z.shiftl_mul_pow2 by lia.
        change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
        replace (2 * 2 ^ st_meta_alloc_shift s + (2 ^ 64 - 1)) with ((2 * 2 ^ st_meta_alloc_shift s - 1) + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia.
      Qed.
      Lemma ev_shift : ltac2:(tb__ "0|2|
S0S6aQ40M0A1S25VrhoF;S28S108Se9Pb8A1S21Z1M1A1A3A2S6bG0S5cS7bVs;A1G1A2A2A3").
      Proof using HMI Hav Hev Hgd VF mW.
        pose proof HB as (_ & SH & _).
        rewrite (evU rhoF (SAlu ALU_ADD (v 184) (SLit 1)) VF eq_refl). rewrite (ev1 mW) by reflexivity. f_equal.
        cbn [zeval zalu]. rewrite ze_v, (zr1_var 184 _ eq_refl). change (1 mod 2 ^ 64) with 1.
        rewrite !(Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia. apply Z.mod_small. lia.
      Qed.
      Lemma ev_areas : ltac2:(tb__ "0|2|
S0S6aQ40M0A1S25VrhoF;S28S108S26P12cA1S21Z1000M1A1A3A2S6bG0S5cS9bG1A2A2A3").
      Proof using Evm HMI HagL Hav Hev Hgd Hpl VF. exact (evU300 rhoF VF). Qed.

      Lemma old_head : ltac2:(tb__ "0|1|
S0S8Sc1S111Vs;VL;S9bA3Sc3S7eVs;A1M0A1A2S134VL;G0A2A3").
      Proof using HI.
        pose proof (inv_areas HI) as (_ & _ & A3 & _). rewrite A3. destruct (st_areas s) as [|a0 l] eqn:Ea; cbn [hd_error optr sval_num optrZ]; [reflexivity|].
        unfold zA. apply G_L'_addr_of. apply (area_below X R U s HI). rewrite Ea. left. reflexivity.
      Qed.
      Lemma old_tail : ltac2:(tb__ "0|1|
S0S8Sc1S111Vs;VL;S9bA3Sc3S79Vs;A1M0A1A2S134VL;G0A2A3").
      Proof using HI.
        pose proof (inv_areas HI) as (_ & _ & _ & A4 & _). rewrite A4. destruct (st_areas s) as [|a0 l] eqn:Ea; cbn [optr sval_num optrZ]; [reflexivity|].
        unfold zA. apply G_L'_addr_of. apply (area_below X R U s HI). rewrite Ea. apply last_In. discriminate.
      Qed.
      Lemma old_avm : ltac2:(tb__ "0|1|
S0S8Sc1S111Vs;VL;S9bA3S14S78A1M0Sc4Lx;S7aVs;A1SbfZ0A1S78G0Sc6S7fVs;A1A1Ll;Ls0;X14x2A2S136Vs;VL;A2A3").
      Proof using HI.
        pose proof (inv_keys HI) as (_ & _ & _ & K4 & _). unfold avmZ. destruct (st_areas s) as [|a0 l] eqn:Ea; cbn [sval_num]; [reflexivity|].
        unfold zA. apply G_L'_addr_of. rewrite (K4 ltac:(discriminate)). cbn [padd prid].
        pose proof (area_below X R U s HI (last (a0 :: l) (SP 0%nat 0)) ltac:(rewrite Ea; apply last_In; discriminate)) as B.
        destruct (last (a0 :: l) (SP 0%nat 0)); cbn in *. exact B.
      Qed.

      Theorem VIN : ltac2:(tb__ "0|2|
SbcSb9SbcR1S18SbcSc5S113Vs;A1M0A1S159G0A1A3A3S16fS111Vs;VL;S9bA3M1S11aR2A3ScbG1Vbv1;R3A3F_;F_;Fc;").
      Proof using Evm HI HMI HXr Hac HagL Hav Hbrk Hcnt Hev Hgd Hhd Hinit Hpl HsmF Htp STK VF rhoW'.
        intros c Hc (k & Hk & T). pose proof Hctx' as HCX. pose proof lenZ_range as [LR _].
        pose proof G_t1_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).

        destruct (G_cell_where1 c (loc_addr G_L' (mc_loc c) + Z.of_nat k) Hc ltac:(lia)) as (e & He & Rx).
        unfold touched in T. destruct T as [T|[T|T]].
        { exfalso. destruct (G_fp_where e _ He Rx) as [[_ Rc]|(pp & _ & _ & NI)]; [rewrite HCX in Rc; unfold CTX_SIZE in Rc; lia | apply NI; cbn [mc_img_lo mc_img_hi C_U]; lia]. }
        2:{ exfalso. rewrite lenZ_eq in T. exact (G_grant_vs_footprint e _ He Rx T). }

        assert (CM : cmeets G_L' c (ly_ctx G_L' + 16) 64).
        { exists k. split; [exact Hk|]. rewrite G_L'_ctx, HCX. lia. }
        destruct (ctx_zone X R U G_t1 G_L' G_HI1 G_xraw_t1 G_layout_ok_t1 c 16 64 Hc ltac:(lia) ltac:(unfold CTX_SIZE; lia) CM) as [Hcc (o & Eloc & O1 & O2)].
        pose proof (ctx_cell_w8 G_t1 c Hcc) as W8.
        pose proof (ctx_cells_SC13 G_t1 c o Hcc Eloc ltac:(unfold CTX_active; lia)) as H13.
        unfold SC13 in H13. rewrite F2, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F18, F19 in H13.
        unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
          CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in H13.
        pose proof (f_equal (fun l => nth 1 l (0, 0)) CHG_ranges) as CR. cbn [nth map CHG2] in CR.
        pose proof G_res_n_ge2 as R2.
        destruct H13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2; injection Eloc as Eo; subst o;
          try (exfalso; lia).
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 24) 8 (SLit 0)) 16 8 (optr None) 0); try reflexivity; try (cbn; tauto); try lia.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 32) 8 (v 176)) 24 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end) avmZ); try reflexivity; try lia.
          + cbn; tauto. + cbn; tauto. + destruct (st_areas s); exact I. + exact old_avm.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + cbn [c_val]. rewrite (evF_v 176) by reflexivity. apply ev176.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 40) 8 (SLit 0)) 32 8 (VZ 0) 0); try reflexivity; try (cbn; tauto); try lia.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 48) 8 (SAlu ALU_ADD (SAlu ALU_SLL (SLit 2) (v 184)) (SLit (-1)))) 40 8 (VZ (res_n s - 1)) (res_n s - 1)); try reflexivity; try (cbn; tauto); try lia.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + exact ev_acount.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 56) 8 (SAlu ALU_ADD (v 184) (SLit 1))) 48 8 (VZ (st_meta_alloc_shift s + 1)) (st_meta_alloc_shift s + 1)); try reflexivity; try (cbn; tauto); try lia.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + exact ev_shift.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 64) 8 (v 185)) 56 8 (optr (st_area_head s)) (optrZ (st_area_head s))); try reflexivity; try lia.
          + cbn; tauto. + cbn; tauto. + destruct (st_area_head s); exact I. + exact old_head.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + cbn [c_val]. rewrite (evF_v 185) by reflexivity. apply ev185.
        -   apply (leaf_cell O_ctxOK (mkCell (SLit 72) 8 (v 186)) 64 8 (optr (st_area_tail s)) (optrZ (st_area_tail s))); try reflexivity; try lia.
          + cbn; tauto. + cbn; tauto. + destruct (st_area_tail s); exact I. + exact old_tail.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + cbn [c_val]. rewrite (evF_v 186) by reflexivity. apply ev186.
        -
          replace (if match st_areas s with [] => true | _ :: _ => false end && (res_n s - 1 =? 0) then VZ 0 else VP G_pnew) with (VP G_pnew)
            by (replace (res_n s - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); rewrite Bool.andb_false_r; reflexivity).
          apply (leaf_cell O_ctxOK (mkCell (SLit 80) 8 (SAlu ALU_ADD (SVar 300) (SLit 4096))) 72 8 (VP G_pnew) (az + 4096)); try reflexivity; try (cbn; tauto); try lia.
          + cbn [sval_num]. rewrite G_L'_pnew. reflexivity.
          + cbn [ob_base O_ctxOK c_off am_ctx AM_P]. rewrite B_ctxW, soff_lit_small by lia. rewrite HCX. lia.
          + rewrite CR. cbn [fst snd]. rewrite HCX. lia.
          + exact ev_areas.
      Qed.

      Theorem OLD : ltac2:(tb__ "0|4|
SbcSb9SbcR1S18SbcSc5S113Vs;A1M0A1S159G0A1A3A3S2S16fS111Vs;VL;S9bA3M1S11aR2A3A1S1Sb9SbcR3S18SbcSc5Vs;A1S159Vs;A1A3A3S1S0S8Sc2G1Sc7R3A1M2A2Sc2VL;G2A2A3S0S8Sc1G1Se3R3A1M3A2Sc1VL;G3A2A3A2A2F_;F_;Fc;").
      Proof using HI HMI HXr Hac Hav Hbrk Hcnt Hev Hgd Hhd Hinit.
        intros c Hc NM. pose proof Hctx' as HCX.
        destruct (G_image_t1 c Hc) as [Hchg|[(Hin & N1 & N2 & N3)|(Hin & q & Eq)]].
        - exfalso. apply NM. unfold AllocMetaGrow.CHG1, AllocMetaGrow.C_ac, AllocMetaGrow.C_sh, AllocMetaGrow.C_ars in Hchg. cbn [In] in Hchg.
          unfold CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_avail_meta_areas in Hchg.
          destruct Hchg as [<-|[<-|[<-|[]]]]; exists 0%nat; (split; [cbn; lia|]); cbn [mc_loc loc_addr]; rewrite G_L'_ctx, HCX; unfold touched; lia.
        - assert (ST := AllocMetaGrow.cell_stable X R U s HI HXr L G_L' c G_L'_ext ltac:(apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Hin) ltac:(intros E; exfalso; exact (N3 E))).
          split; [apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Hin | exact ST].
        - assert (ST := AllocMetaGrow.cell_stable X R U s HI HXr L G_L' c G_L'_ext Hin ltac:(intros E; rewrite Eq in E; discriminate)).
          split; [exact Hin | exact ST].
      Qed.

      Theorem minvI2 : ltac2:(tb__ "0|0|
S162SacVX;VR;VU;Se7S113Vs;A1S111Vs;VL;S9bA3A2S106SbS119A2S107SbS119A2S117Vs;Vvm;S9bA3A8").
      Proof using Erd Evm Ewok HI HMI HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom HsmF Htp MF STK VF bv0 rhoW' rv0.
        unfold MInvI. pose proof Hctx' as HCX. pose proof lenZ_range as [LR _].
        refine (GapGrow.minv_postGX C_U (Inv X R U) (Inv X R U) s G_t1 L G_L' (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm G_vm1
                  HMI0 G_HI1 G_bounded_t1 G_layout_ok_t1 G_L'_ctx G_ub_t1 G_vm_ok_t1 (proj1 G_ledger_t1) (proj2 (proj2 G_ledger_t1))
                  touched touched_dec [] _ _ _ _ V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _ G_maps_wf_t1).
        - intros e He. left. rewrite <- G_fp_t1. exact He.
        - intros e He _. exact (G_L'_fp e He).
        - intros b Hb. exact (G_L'_ub b Hb).
        - intros e x [] _.
        - intros c Hc. exact (cell_spanI X R U G_t1 G_L' G_HI1 G_xraw_t1 G_layout_ok_t1 c Hc).
        - intros x Hx. exact (owned_spanI G_t1 G_L' G_layout_ok_t1 x Hx).
        - intros c Hc. exact (cell_w_posI G_t1 c Hc).
        - intros x T Himg. unfold touched in T. destruct T as [T|[T|T]].
          + right. unfold mc_errno. cbn [mc_tp C_U]. lia.
          + left. cbn [mc_ctx C_U]. unfold CTX_SIZE. lia.
          + exfalso. apply (G_grant_vs_image x); [exact Himg | rewrite <- lenZ_eq; exact T].
        - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
          unfold CTX_SIZE in Hx. clear - Hx. lia.
        - intros Hf. exfalso. pose proof G_t1_fields as (_ & _ & _ & _ & F5 & _). rewrite F5 in Hf. discriminate.
      Qed.

      Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
S12S6aQ40A1L_;S1fS64Z64M0SaVj;A1M1A2S69G1Z84A2A2S25VrhoF;S27Sa0S61G1G0A2A2A2S2fVrho;Vj;A2X12x2").
      Definition rho' : valuation := ltac2:(tb__ "0|0|
S50S11cS56VrhoF;A1S119A3").
      Lemma rw'_low j : ltac2:(tb__ "0|0|
S14bVj;P64A2S0S6aQ40A1S11cVj;A1S2fVrho;Vj;A2A3F_;").
      Proof using Hav Hev Hgd. intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity. Qed.
      Lemma rwF_low j : ltac2:(tb__ "0|0|
S14bVj;PaaA2S0S6aQ40A1S2fVrhoF;Vj;A2S2fVrho;Vj;A2A3F_;").
      Proof using Hav Hev Hgd VF. intros Hj. destruct VF as [(A & _ & _) _]. rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj. Qed.
      Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S10fScVrho;S11bA3").
      Proof using Hav Hev Hgd VF.
        split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
        intros l. cbn [rl rho']. destruct VF as [(_ & HL2 & _) _]. rewrite <- (HL2 l). reflexivity.
      Qed.
      Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S1S5dZ1Vz;A2S5dVz;Z1fA2A2S0S12SdS62Vz;A1M0A1S15A3S3S9S9S1S0S23SeG0A1S26R1A1A3S14bR1P64A2A2Lvv;A2F_;F_;").
      Proof using Hav Hev Hgd.
        intros Hr Hcs.
        pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
        cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
        destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
      Qed.
      Lemma reg_sv_null z : ltac2:(tb__ "0|2|
S1S5dZ1Vz;A2S5dVz;Z1fA2A2S0S23S27S140S103A1Vz;A2S12S23L_;M0S65Vz;ZaA2S21Z0A1G0SdS62Vz;A1M1A1SeG1A1S26S14cP64S14eG1A1A2A1X12x2X12x2A3F_;").
      Proof using Hav Hev Hgd.
        intros Hz.
        pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_null IEC_U) z)
                       (if (z =? 10) then SLit 0 else if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
        apply sv_eqb_sound in H. exact H.
      Qed.
      Lemma freg_sv_null z : ltac2:(tb__ "0|2|
S1S5dZ0M0Vz;A2S5dVz;Z1fA2A2S3S9S9S1S0S23S4eS140S103A1Vz;A2S26R1A1M1A3S1S0S23S144S23S62Vz;A1SfS21G0A1A4G1A3S1S14dP3cR1A2S14bR1P64A2A2A2A2Lvv;A2F_;").
      Proof using Hav Hev Hgd.
        intros Hz.
        pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
        unfold freg_sv. change (ss_fregs (L_am_null IEC_U)) with pre_fregs.
        destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
        apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
      Qed.
      Lemma EBs : ltac2:(tb__ "0|1|
S0S6aQ40A1S25S11bS26PaA1M0A2S25VrhoF;G0A2A3").
      Proof using Hav Hev Hgd VF. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
      Lemma ELs : ltac2:(tb__ "0|0|
S0S8S3aS11bS26S16cA1A2S3aVrhoF;S26PfA1A2A3").
      Proof using Hav Hev Hgd VF. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
      Lemma RSF : ltac2:(tb__ "0|1|
S0S17S8S8A2S29VrhoF;Sf1Sa8A1A2S11S8S8S5cS133Vrho;A1M0S132Vrho;A1A2G0A4A3").
      Proof using Hav Hev Hgd VF mW rhoW.
        rewrite (ReabKit.range_ag rhoW rhoF [O_stk stkRF2_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkRF2_cells) ltac:(left; reflexivity)).
        change (obj_range rhoW (O_stk stkRF2_cells)) with (obj_range (rho1 mW) (O_stk stkRF2_cells)). apply rng_stk.
      Qed.
      Lemma RS' : ltac2:(tb__ "0|1|
S0S17S8S8A2S29S11bS16eS142A1A2S11S8S8S5cS133Vrho;A1M0S132Vrho;A1A2G0A4A3").
      Proof using Hav Hev Hgd VF mW rhoW. rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity. Qed.

      Theorem smatch_null2 : ltac2:(tb__ "0|0|
S32SbS11bS140S103A1S11S14S128A1S138Vtr;S139VmsF;S9dA2A4A4").
      Proof using Hav Hev Hgd HsmF STK VF mW rhoW.
        pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
        unfold smatch. cbn [fst snd cfg_ms cfg_model].
        split; [vm_compute; reflexivity|].
        split; [exact F_pc|].
        split; [exact F_pend|]. split; [exact F_halt|]. split; [exact HromF|]. split; [exact HroF|].
        split.
        { intros r Hr0. rewrite (F_regs r Hr0).
          assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
          rewrite reg_sv_null by lia.
          destruct (bv_unsigned r =? 10) eqn:E10.
          - apply Z.eqb_eq in E10. destruct LRF2_misc as (_ & _ & _ & _ & _ & Ma0).
            replace r with (Z_to_bv 5 10) by (apply bv_eq; rewrite E10; reflexivity). change (bv_unsigned (Z_to_bv 5 10)) with 10. rewrite Ma0. reflexivity.
          - destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
            + destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100).
              rewrite (LRF2_cs (bv_unsigned r) ltac:(lia) CS), E.
              cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; lia.
            + cbn [eval rho' rw]. unfold rw'.
              replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
                by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
              replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
              reflexivity. }
        split.
        { intros r. rewrite (F_fregs r).
          assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
          destruct (freg_sv_null (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
          unfold freg_sv. destruct LRF2_misc as (_ & _ & Mfr & _). rewrite Mfr, E2.
          cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
        split; [exact F_fcsr|].
        split; [exact F_resv|].
        split.
        { assert (HOS : obj_holds segsU rhoF msF (O_stk stkRF2_cells)) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
          split; [|split].
          - constructor; [|constructor].
            apply obj_holds_drop_cells in HOS.
            destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
            cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
            rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
            intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
          - cbn [pairwise_disjoint]. split; [constructor|exact I].
          - intros x Hx. cbn [rm rho'].
            destruct (in_ranges_dec rhoF (UNCH2 ++ CHG2) x) as [IN|OUT].
            + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
            + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
              apply Forall_cons_iff in Hx as [HxS _]. cbn zeta in HxS. rewrite RS' in HxS.
              unfold OBJ2. constructor; [cbn zeta; rewrite RSF; exact HxS|].
              apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [|exact RR].
              revert Ho. clear. unfold UNCH2, CHG2. cbn [firstn skipn app In]. tauto. }
        unfold L_am_null. cbn [ss_facts].
        assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
        { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
        pose proof (smatch_facts_hold segsU _ _ _ HsmF) as HF1.
        assert (AGR1 : forall f, sprop_vars_all (fun j => (j <? NF)%positive) f = true -> SymState.holds rhoF f -> SymState.holds rho f).
        { intros f Hb Hh. refine (proj2 (holds_agree_vars (fun j => (j <? NF)%positive) rho rhoF f _ _ Hb) Hh).
          - intros j Hj. symmetry. apply rwF_low. apply Pos.ltb_lt in Hj. unfold NF in Hj. lia.
          - intros l. destruct VF as [(_ & HL2 & _) _]. rewrite <- (HL2 l). reflexivity. }
        repeat (constructor; [apply AGR; [reflexivity|]; apply AGR1; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF1); vm_compute; tauto|]). constructor.
      Qed.

      Lemma OBJ_rangesF o : ltac2:(tb__ "0|1|
Sb9S20Vo;S18S20S9cS9eA3A3Sb9S17S8S8A2M0S29VrhoF;Vo;A2S10G0S11S8S8Z28d50Z28d58A4S10G0S11S8S8Z5a338Z5a340A4S10G0S11S8S8Z5a360Z5a368A4S10G0S11S8S8Z5a388Z5a390A4S10G0S11S8S8Z5a3d0Z5a3dcA4S10G0S11S8S8Z5a768Z5a770A4S10G0S11S8S8Z3a02cZ3a030A4S10G0S11S8S8Z5a3e0Z5a420A4S16G0A1A3A3A3A3A3A3A3A3A3F_;").
      Proof using Hav Hev Hgd Htp STK VF mW.
        intros Ho. pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite map_app, UNCH_rangesF, CHG_ranges in M.
        cbn [app In] in M. cbn [In]. tauto.
      Qed.

      Theorem kept2 : ltac2:(tb__ "0|0|
S16dSbSacSe7Vs;VL;A2Se7S113Vs;A1S111Vs;VL;S9bA3A2S2aVrho;A1S119A6").
      Proof using EmW Evm HI HMI HXr HagL Hav Hev Hgd Hpl Htp MF STK VF.
        intros x Hx CA _ NE NS. pose proof Hctx' as HCX. rewrite <- EmW. pose proof lenZ_range as [LR _].
        pose proof grant_facts as (_ & _ & Hceil & _).
        destruct (in_ranges_dec rhoF (UNCH2 ++ CHG2) (Z_to_bv 64 x)) as [IN|OUT].
        - exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia. pose proof (OBJ_rangesF o Ho) as RNG.
          unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in NS, NE.
          assert (NCTX : ~ (369616 <= x < 369616 + CTX_SIZE)).
          { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
            - top_ranges. unfold CTX_SIZE in Hc. lia.
            - destruct (G_block_where b n x Hin Hr) as (e & pp & He & Ep & Rx).
              destruct (G_fp_where e x He Rx) as [[E1 _]|(p' & _ & _ & NI)]; [rewrite Ep in E1; discriminate|]. apply NI. cbn [mc_img_lo mc_img_hi C_U]. unfold CTX_SIZE in Hc. lia.
            - apply H. cbn [mc_ctx C_U]. exact Hc. }
          unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX.
          repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; lia|]). destruct RNG.
        - unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply MF. rewrite u64 by lia. intros G.
          destruct CA as [H|[(b & n & Hin & Hr)|(W & _)]].
          + clear - H Hceil G LR. cbn [ma_L] in H. top_ranges. lia.
          + apply (G_grant_vs_block b n x Hin Hr). rewrite <- lenZ_eq. exact G.
          + apply (G_grant_vs_image x); [|rewrite <- lenZ_eq; exact G]. exact (ClientLaws.wseg_in_image_U (Z_to_bv 64 x) W) || (pose proof (ClientLaws.wseg_in_image_U (Z_to_bv 64 x) W) as WI; rewrite u64 in WI by lia; exact WI).
      Qed.

      Theorem maps_kept2 : ltac2:(tb__ "0|0|
S105Se7Vs;VL;A2S2aVrho;A1S119A3").
      Proof using EmW Evm HMI HagL Hav Hev Hgd Hpl Htp MF STK VF.
        intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW. pose proof lenZ_range as [LR _].
        pose proof HVX as (_ & _ & X3 & X4). destruct (X4 k rg Hk Hl) as [B1 B2]. pose proof (X3 k rg Hk Hl) as SZ. top_ranges.
        assert (R64 : 0 <= x < 2 ^ 64) by (unfold PGSZ in B1; lia).
        assert (UB : bv_unsigned (Z_to_bv 64 (ly_reg L k)) = ly_reg L k) by (apply u64; unfold PGSZ in *; lia).
        assert (UL : bv_unsigned (Z_to_bv 64 (rg_len rg)) = rg_len rg) by (apply u64; unfold PGSZ in *; lia).
        pose proof HV as (V1' & _). pose proof (V1' k rg Hk Hl Hkd) as IN. pose proof (HLG _ IN) as (G1 & G2 & G3). cbn [fst snd] in G1, G2, G3.
        unfold wz in G1, G2, G3. rewrite ?UB, ?UL in G1. rewrite ?UB, ?UL in G2. rewrite ?UB, ?UL in G3. cbn [mc_img_lo mc_img_hi C_U] in G3.
        destruct (in_ranges_dec rhoF (UNCH2 ++ CHG2) (Z_to_bv 64 x)) as [INR|OUT].
        - exfalso. destruct INR as (o & Ho & RR). rewrite u64 in RR by lia. pose proof (OBJ_rangesF o Ho) as RNG.
          clear - RNG RR G3 Hx. repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; lia|]). destruct RNG.
        - unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply MF. rewrite u64 by lia.
          pose proof (G_old_region_vs_grant k rg x Hk Hl (or_introl Hkd) Hx) as NG. rewrite <- lenZ_eq in NG. exact NG.
      Qed.

      Theorem canary_kept2 : ltac2:(tb__ "0|0|
S104SbSacS2aVrho;A1S119A4").
      Proof using EmW Erd Ewok HMI Hav Hav_rd Hbrk Hev Hgd Hgd_rd Hinit Hrom HsmF STK VF rhoW'.
        intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
        pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH2] in R0, R1.
        destruct Hx as [Hx|Hx].
        - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
        - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
      Qed.

      Theorem post_null2 : ltac2:(tb__ "0|0|
S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8S11S14S128A1S138Vtr;S139VmsF;S9dA2A4A5").
      Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom HsmF Htp MF STK VF bv0 bv1 rhoW' rv0 rv1.
        exists (L_am_null IEC_U), (JL_am_null segsU C_U X R U (mkMA s L) Kc), rho'.
        split; [left; reflexivity|]. split; [exact agree_vals_rho'|]. split; [exact smatch_null2|].
        cbn [w_tr w_cfg fst snd cfg_model].
        exists (mkMA G_t1 G_L'). cbn [ma_s ma_L].
        pose proof G_am_frame_t1 as (AF & US & UB). pose proof G_t1_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        split; [unfold MInvIR; cbn [rm rho']; rewrite rdG, wokG, vm1_eq; exact minvI2|].
        split.
        { split; [exact G_xraw_t1|]. split; [exact F5|]. split; [exact AF|]. split; [repeat split; assumption|].
          split; [exact US|]. split; [exact UB|]. cbn [ma_s ma_L]. split; [rewrite G_keys_t1; intros q Hq; exact Hq | exact G_L'_ext]. }
        split; [exact kept2|]. split; [exact maps_kept2|]. split; [exact canary_kept2|].
        split; [|apply (Kc_vm md1 HKc); eexists; reflexivity].
        exists (tr_RES (s0 s) 1 0). pose proof (yields_NB s Hhd Hcnt Hac Hbrk 1 0) as Y.
        unfold r_RES in Y. cbn [Z.eqb] in Y. rewrite G_s0_t in Y. exact Y.
      Qed.

      Theorem post_null2x : ltac2:(tb__ "0|0|
S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8S11S14S128A1S138Vtr;S139VmsF;S9dA2A4A5").
      Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom HsmF Htp MF STK VF bv0 bv1 rhoW' rv0 rv1.
        exists (L_am_null IEC_U), (JL_am_null segsU C_U X R U (mkMA s L) Kc), rho'.
        split; [left; reflexivity|]. split; [exact agree_vals_rho'|]. split; [exact smatch_null2|].
        cbn [w_tr w_cfg fst snd cfg_model].
        exists (mkMA G_t1 G_L'). cbn [ma_s ma_L].
        pose proof G_am_frame_t1 as (AF & US & UB). pose proof G_t1_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        split; [unfold MInvIR; cbn [rm rho']; rewrite rdG, wokG, vm1_eq; exact minvI2|].
        split.
        { split; [exact G_xraw_t1|]. split; [exact F5|]. split; [exact AF|]. split; [repeat split; assumption|].
          split; [exact US|]. split; [exact UB|]. cbn [ma_s ma_L]. split; [rewrite G_keys_t1; intros q Hq; exact Hq | exact G_L'_ext]. }
        split; [exact kept2|]. split; [exact maps_kept2|]. split; [exact canary_kept2|].
        split; [|unfold md1; exact (proj1 HVI tr md _ HKc)].
        exists (tr_RES (s0 s) 1 0). pose proof (yields_NB s Hhd Hcnt Hac Hbrk 1 0) as Y.
        unfold r_RES in Y. cbn [Z.eqb] in Y. rewrite G_s0_t in Y. exact Y.
      Qed.
    End FailLeaf2.

    Theorem fail2_sound : ltac2:(tb__ "0|0|
S1aS73S74SbVok;R2S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw;A4S3S30S30S1Sa2R1A1S1Sa7S2aR1A1A1S13bSbS13cS131Vtr;S9dA2A1SeaSbSe8SedA3R1R3A5A2A2LrhoF;A2S75SbVok;R4R3A4F_;F_;Fw';Fm;").
    Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros m w' HQ (rhoF0 & VF0 & MF0 & Hw).
      assert (K1 : Kc tr md1) by (apply (Kc_vm md1 HKc); eexists; reflexivity).
      pose proof (alloc_meta_run_P A78_res_ok_fail ok (Kexact tr md1) rhoF0 (ok_frame_exact ok Kc tr md1 HOK K1)) as RUN2.
      refine (RUN2 m _ w' Hw).
      intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
      assert (ELF3 : lf_state L3 = LRF2) by (unfold LRF2; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok_fail) = 301%positive) by (vm_compute; reflexivity). rewrite NX in Hag3.
      apply HQ. apply (post_null2 ms3 rhoF).
      - exact (valU_ext rhoF0 rhoF 301 VF0 ltac:(reflexivity) Hag3).
      - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (MF0 x Hx).
      - exact Hsm3.
    Qed.

    Theorem granted_sound : ltac2:(tb__ "0|0|
S1aS73S74SbVok;R2S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A4S74SbVok;R3Sa3A4S13bSbS13cS131Vtr;S9dA2A1S147S125A1Sa1R3A5S75SbVok;R5R4A4F_;F_;F_;Fw;Fn;").
    Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros n w HQ HC Hw. apply (stepBC n w HQ HC); [|exact Hw].
      intros m w' Hm Hex. apply (fail2_sound m w'); [|exact Hex]. exact (@Safety.guards_mono segsU ok n m _ Hm HQ).
    Qed.

    Theorem granted_ex : ltac2:(tb__ "0|0|
S8S73S161S9dR2A2S13bSbS13cS131Vtr;S9dA2A1S147S125A1Sa1R2A5S76SbS73S0S73R1R4A3Lw';S73S1Sa3R1A1S161SaaR5A2A2Lw';A3F_;F_;Fw;FXb;").
    Proof using Evm HKc HMI HVI HagL Hav Hev Hgd Hpl Htp STK.
      intros Xb w HRb Hw w0 ->. pose proof grant_facts as (Hal & Hpos & Hceil & _). pose proof lenZ_range as [LR LA]. pose proof az64 as A64.
      assert (K1 : Kc tr md1) by (unfold md1; exact (proj1 HVI tr md _ HKc)).
      destruct (alloc_meta_run_ex_P A78_res_ok (Kexact tr md1) rhoU w (entry_resok w Hw))
        as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoX & HinL & HagX & HsmX & HK1).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LOK) by (unfold LOK; rewrite EP; reflexivity). rewrite ELF in HsmX. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmX.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagX.
      pose proof (valU_ext rhoU rhoX 301 valU_rhoU ltac:(reflexivity) HagX) as VX.
      assert (MX : memU (rm rhoX)).
      { intros x Hx. destruct HagX as (_ & _ & M). rewrite <- (M x). exact (memU_rhoU x Hx). }
      pose proof LOK_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
      pose proof (vm_room_mprotect md1 Xb (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) HRb) as [HB HR2].
      assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md1)) LOK rhoX)
                      (SPJ segsU (liftK (Kexact tr md2)) (S_ret_lit LOK 0)
                           (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))))).
      { apply (HeapEx.etriple_mprotect_expose_okJ segsU (liftK (Kexact tr md1)) (liftK (Kexact tr md2)) LOK rhoX LOK_ecall M17).
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
        change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
        rewrite M10, (evU300 rhoX VX) in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
        pose proof (LOK_objs_miss rhoX VX) as MISS. pose proof ro_addr_grant as ROG. pose proof EL as EL'. pose proof mmap_n_lenZ as MN.
        pose proof HB as HB'.
        clear Hsp HsmX HagX Hw VX ELF EP ST1 HRb HR2 HB.
        rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
        assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
        assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
        assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
        rewrite ?U1, ?U2, ?U3.
        split; [reflexivity|]. split; [unfold page_size; unfold PGSZ in Hal; clear - Hal; Z.to_euclidean_division_equations; lia|].
        split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
        split; [unfold two_pow_64; clear - Hceil LR A64; top_ranges; lia|].
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_noaccess]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_maps]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split; [rewrite <- mmap_n_4096 at 1; exact HB'|].
        split; [exact MISS|]. split; [intros x Hx; apply ROG; clear - Hx LR; lia|].
        split; reflexivity. }
      destruct (ST2 (tr, mkCfg ms1 md1) (conj HsmX (conj eq_refl eq_refl))) as (w2 & ST2' & HO2).
      exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2']|]. split; [|exact HR2].
      exists (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))).
      rewrite M10, M11, (evU300 rhoX VX). cbn [eval]. rewrite mmap_n_4096.
      assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
      split; [|split; [|split]].
      * destruct VX as [(A1 & A2 & A3) A4]. split; [split; [exact A1|split; [exact A2|intros x; reflexivity]]| exact A4].
      * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        destruct (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) eqn:E; [|exact (MX x Hx)].
        exfalso. apply in_range_spec in E. rewrite U1 in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. apply Hx. clear - E LR. lia.
      * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
        replace (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) with true; [reflexivity|].
        symmetry. apply in_range_spec. rewrite U1. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
      * rewrite Pre_resok_ok_eq. rewrite M10, M11, (evU300 rhoX VX) in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. exact HO2.
    Qed.

    Theorem granted_anyex : ltac2:(tb__ "0|0|
S73S13bSbS13cS131Vtr;S9dA2A1S147S125A1Sa1R1A5S76SbS73S0S73R1R3A3Lw';S73S4S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Sa3R1A1A2Lw';A3F_;Fw;").
    Proof using EmW Erd Evm Ewok HI HKc HMI HVI HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros w Hw w0 ->. pose proof grant_facts as (Hal & Hpos & Hceil & _). pose proof lenZ_range as [LR LA]. pose proof az64 as A64.
      assert (K1 : Kc tr md1) by (unfold md1; exact (proj1 HVI tr md _ HKc)).
      destruct (alloc_meta_run_ex_P A78_res_ok (Kexact tr md1) rhoU w (entry_resok w Hw))
        as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoX & HinL & HagX & HsmX & HK1).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LOK) by (unfold LOK; rewrite EP; reflexivity). rewrite ELF in HsmX. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmX.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagX.
      pose proof (valU_ext rhoU rhoX 301 valU_rhoU ltac:(reflexivity) HagX) as VX.
      assert (MX : memU (rm rhoX)).
      { intros x Hx. destruct HagX as (_ & _ & M). rewrite <- (M x). exact (memU_rhoU x Hx). }
      pose proof LOK_misc as (Mpc & M17 & M10 & M11 & M12 & Mnx).
      assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md1)) LOK rhoX)
                      (fun w2 => SPJ segsU (liftK (Kexact tr md1)) (S_ret_lit LOK enomem_ret) rhoX w2
                                 \/ SPJ segsU (liftK (Kexact tr md2)) (S_ret_lit LOK 0)
                                      (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))) w2)).
      { apply (HeapEx.etriple_mprotect_expose_anyJ segsU (liftK (Kexact tr md1)) (liftK (Kexact tr md1)) (liftK (Kexact tr md2)) LOK rhoX LOK_ecall M17).
        intros tr0 ms0 md0 Hsp [-> ->].
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 0 Hsp ltac:(repeat constructor)) as G0.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 1 Hsp ltac:(repeat constructor)) as G1.
        pose proof (smatch_pending_gpr segsU rhoX LOK tr ms0 md1 2 Hsp ltac:(repeat constructor)) as G2.
        change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
        rewrite M10, (evU300 rhoX VX) in G0. rewrite M11 in G1. rewrite M12 in G2. cbn [eval] in G1, G2.
        pose proof (LOK_objs_miss rhoX VX) as MISS. pose proof ro_addr_grant as ROG. pose proof EL as EL'. pose proof mmap_n_lenZ as MN.
        clear Hsp HsmX HagX Hw VX MX ELF EP ST1.
        rewrite G0, G1, G2. rewrite mmap_n_4096, mmap_nZ_4096. clear G0 G1 G2.
        assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
        assert (U2 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
        assert (U3 : bv_unsigned (Z_to_bv 64 3) = 3) by reflexivity.
        rewrite ?U1, ?U2, ?U3.
        split; [reflexivity|]. split; [unfold page_size; unfold PGSZ in Hal; clear - Hal; Z.to_euclidean_division_equations; lia|].
        split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U2 in E; discriminate|].
        split; [unfold two_pow_64; clear - Hceil LR A64; top_ranges; lia|].
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_noaccess]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split.
        { unfold md1. rewrite m_vmmaps_with_vmmaps. cbn [mmap_none_vm vm_maps]. rewrite EL', mmap_n_eq. apply map_contains_head; cbn [fst snd]; fold az; rewrite ?U1, ?U2, ?(u64 lenZ78) by (clear - LR; lia); clear - LR A64; lia. }
        split; [intros _; split; reflexivity|].
        intros _. split; [exact MISS|]. split; [intros x Hx; apply ROG; clear - Hx LR; lia|].
        split; reflexivity. }
      destruct (ST2 (tr, mkCfg ms1 md1) (conj HsmX (conj eq_refl eq_refl))) as (w2 & ST2' & [HF2 | HO2]).
      -
        rewrite <- Pre_resok_fail_eq in HF2.
        destruct (alloc_meta_run_ex_P A78_res_ok_fail (Kexact tr md1) rhoX w2 HF2) as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3).
        cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
        destruct (Posts_am_P_shape A78_res_ok_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
        assert (ELF3 : lf_state L3 = LRF2) by (unfold LRF2; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
        assert (NX3 : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok_fail) = 301%positive) by (vm_compute; reflexivity). rewrite NX3 in Hag3.
        exists (tr, mkCfg ms3 md1). split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
        left. apply (post_null2x ms3 rhoF).
        + exact (valU_ext rhoX rhoF 301 VX ltac:(reflexivity) Hag3).
        + intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (MX x Hx).
        + exact Hsm3.
      -
        exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2']|]. right.
        exists (set_rm rhoX (zero_range (rm rhoX) (eval rhoX (reg_sv LOK 10)) (mmap_n (eval rhoX (reg_sv LOK 11))))).
        rewrite M10, M11, (evU300 rhoX VX). cbn [eval]. rewrite mmap_n_4096.
        assert (U1 : bv_unsigned (Z_to_bv 64 (az + 4096)) = az + 4096) by (clear - Hceil A64 LR; apply u64; top_ranges; lia).
        split; [|split; [|split]].
        * destruct VX as [(A1 & A2 & A3) A4]. split; [split; [exact A1|split; [exact A2|intros x; reflexivity]]| exact A4].
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          destruct (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) eqn:E; [|exact (MX x Hx)].
          exfalso. apply in_range_spec in E. rewrite U1 in E. change (bv_unsigned (Z_to_bv 64 4096)) with 4096 in E. apply Hx. clear - E LR. lia.
        * intros x Hx. cbn [rm set_rm]. rewrite zero_range_at.
          replace (in_range (Z_to_bv 64 (az + 4096)) (Z_to_bv 64 4096) x) with true; [reflexivity|].
          symmetry. apply in_range_spec. rewrite U1. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact Hx.
        * rewrite Pre_resok_ok_eq. rewrite M10, M11, (evU300 rhoX VX) in HO2. cbn [eval] in HO2. rewrite mmap_n_4096 in HO2. exact HO2.
    Qed.
  End Granted.

  Theorem resok1_sound : ltac2:(tb__ "0|1|
S1aS74SbVok;R1S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A4S6aQ40M0A1S30S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R1A3S151S6bG0Z0A2Vmd;S25R2SecA2R3A4S74SbVok;R6S171R4R3A2A4F_;F_;FrhoL;Faw;S74SbVok;R3S126Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4F_;F_;Fn;").
  Proof using EmW Erd Evm Ewok HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Htp STK.
    intros n HQ HC w (aw & rhoL & HagL & Hpl & Hw). exact (granted_sound aw rhoL HagL Hpl n w HQ (HC aw rhoL HagL Hpl) Hw).
  Qed.

  Theorem resok1_S : ltac2:(tb__ "0|2|
S1aS6aQ40M0A1S30S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R1A3S151S6bG0Z0A2Vmd;S25R2SecA2R3A4S1S0S12S15aS173R4R3A2S6bG0S5cS172R4A1Z1000M1A2A2S6bG0G1A2A3S15A3S74SbVok;R5S171R4R3A2A4A2F_;F_;FrhoL;Faw;S74SbVok;R2S126Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4F_;Fn;").
  Proof using Evm HKc HMI HOK Hav Hev Hgd Htp STK.
    intros n HC w (aw & rhoL & HagL & Hpl & Hw). destruct (HC aw rhoL HagL Hpl) as [HB HCC]. exact (stepBC_S aw rhoL HagL Hpl n w HB HCC Hw).
  Qed.
End Cut78r.

End InstX.

End Mal_ameta_ROK.

Module Mal_ameta_R2E.

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
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G4.Mal_ameta_ROK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
Sc9VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S162SacVX;VR;VU;Se7Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§11§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§11§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§11§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HMW := (§11§ U.Mal_ameta__G1.Mal_ameta_I.HMW).
Local Abbreviation HLG := (§11§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation HB := (§11§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Abbreviation secZ := (@U.Mal_ameta__G1.Mal_ameta_I.secZ s L).
Local Notation "§12§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§13§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§13§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev1 := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ev1).
Local Abbreviation ze_v := (§12§ U.Mal_ameta__G1.Mal_ameta_I.ze_v).
Local Abbreviation ev186 := (§13§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0S6aQ40A1S13S6aQ8A1A1F_;Vrd0;S106SbVmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0S6aQ40A1S12F_;Vwok0;S107SbVmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
SafSadVrd0;S6aQ40A1S15L_;A2Sb1SacA1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S1aS14fR1U4A2S0S13S6aQ8M0A1M1A1S106SbVmW;S6bQ40S5cSb2SacA1S60R2A1A2A2A3S19G1S144G1R2Vevb;S6bG0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S1aS14fR1U8A2S0S13S6aQ8M0A1M1A1S106SbVmW;S6bQ40S5cSb0SacA1S60R2A1A2A2A3S19G1S144G1R2Vavb;S6bG0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
SadS106SbVmW;A2S107SbVmW;A2A2").
Local Abbreviation cell_rw0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_rw0 s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok).
Local Abbreviation cell_view0 := (@U.Mal_ameta__G1.Mal_ameta_I.cell_view0 s L X R U rho rd0 wok0 vm HMI gd evb avb mW Erd Ewok).
Hypothesis Htp : ltac2:(tb__ "0|1|
S0S6aQ40M0A1S2fVrho;P18A2S6bG0Sb3SacA1A2A3").
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0S6aQ40A1S13S6aQ8A1A1F_;VmW;S2aVrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S32SbVrho;S141S103A1S11S14S128A1S138Vtr;S139Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S16bSe7Vs;VL;A2Vrho;A2").
Local Abbreviation zr1_var := (§12§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation rw1_v := (@U.Mal_ameta__G1.Mal_ameta_I.rw1_v s L rho gd evb avb mW).

Section Cut78r.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S13S78A1S81Vs;A1S1dS78A1A3").
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : st_avail_meta_area_count s = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S0S7dS80Vs;A1S85A3").
  Hypothesis Hinit : st_init_done s = true.
  Variable Kc : ltac2:(tb__ "0|0|
S14S128A1S129OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S0S12aVvm;S12bVmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S16aSbVok;VKc;A3").

  Hypothesis HVI : vm_insensitive Kc.
  Hypothesis STK : ltac2:(tb__ "0|3|
S1S5dZ0S5cS133Vrho;A1M0S132Vrho;A1M1A2M2A2S1S5dSaeVL;A1G2A2S1S5dG0S5fZ2Z40A2A2S5dG1S68Sf8A1A2A2A2A2").

  Hypothesis HFpre : ltac2:(tb__ "0|0|
S143S2bS3eVrho;A1S35S141S103A1A1A3").

  Local Abbreviation lenZ78 := (U.Mal_ameta__G2.Mal_ameta_R78.lenZ s).

  Section Granted.
    Variables (aw : word) (rhoL : valuation).
    Hypothesis HagL : ltac2:(tb__ "0|0|
S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoL;A3").
    Hypothesis Hpl : ltac2:(tb__ "0|0|
S151S6bQ40Z0A2Vmd;S25VrhoL;SecA2Vaw;A4").

Local Abbreviation K_smatch_add_facts_app := (@U.Mal_ameta__G4.Mal_ameta_ROK.smatch_add_facts_app).
Local Notation "§14§ h__" := (h__ s) (at level 10, h__ global).
Local Abbreviation K_lenZ_eq := (§14§ U.Mal_ameta__G4.Mal_ameta_ROK.lenZ_eq).
Local Notation "§15§ h__" := (h__ s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation K_lenZ_range := (§15§ U.Mal_ameta__G4.Mal_ameta_ROK.lenZ_range).
Local Abbreviation K_LENX_val := (@U.Mal_ameta__G4.Mal_ameta_ROK.LENX_val s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation K_mmap_n_lenZ := (§15§ U.Mal_ameta__G4.Mal_ameta_ROK.mmap_n_lenZ).
Local Abbreviation K_mmap_nZ_lenZ := (§15§ U.Mal_ameta__G4.Mal_ameta_ROK.mmap_nZ_lenZ).
Local Abbreviation K_mmap_n_eq := (§15§ U.Mal_ameta__G4.Mal_ameta_ROK.mmap_n_eq).
Local Abbreviation K_ok_pframe_exact := (@U.Mal_ameta__G4.Mal_ameta_ROK.ok_pframe_exact tr Kc ok HOK).
Local Abbreviation K_Kc_vm := (@U.Mal_ameta__G4.Mal_ameta_ROK.Kc_vm tr md Kc ok HOK).
Local Abbreviation K_az := (@U.Mal_ameta__G4.Mal_ameta_ROK.az aw).
Local Notation "§16§ h__" := (h__ md aw rhoL) (at level 10, h__ global).
Local Abbreviation K_md1 := (§16§ U.Mal_ameta__G4.Mal_ameta_ROK.md1).
Local Abbreviation K_rhoU := (@U.Mal_ameta__G4.Mal_ameta_ROK.rhoU aw rhoL).
Local Abbreviation K_EL := (@U.Mal_ameta__G4.Mal_ameta_ROK.EL s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW rhoL HagL).
Local Notation "§17§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW md Evm aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_grant_facts := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.grant_facts).
Local Abbreviation K_az64 := (@U.Mal_ameta__G4.Mal_ameta_ROK.az64 aw).
Local Abbreviation K_aw_eq := (@U.Mal_ameta__G4.Mal_ameta_ROK.aw_eq aw).
Local Notation "§18§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation K_Hctx_C := (§18§ U.Mal_ameta__G4.Mal_ameta_ROK.Hctx_C).
Local Abbreviation K_G_al := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.G_al).
Local Abbreviation K_G_pos := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.G_pos).
Local Abbreviation K_G_ceil := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.G_ceil).
Local Abbreviation K_G_free := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.G_free).
Local Abbreviation K_HIRv := (§18§ U.Mal_ameta__G4.Mal_ameta_ROK.HIRv).
Local Abbreviation K_HIRX := (@U.Mal_ameta__G4.Mal_ameta_ROK.HIRX s L X R U rd0 wok0 vm HMI md Evm).
Local Notation "§19§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW md Evm aw rhoL HagL) (at level 10, h__ global).
Local Abbreviation K_vm1_eq := (§19§ U.Mal_ameta__G4.Mal_ameta_ROK.vm1_eq).
Local Abbreviation K_Pre_resok_eq := (@U.Mal_ameta__G4.Mal_ameta_ROK.Pre_resok_eq).
Local Abbreviation K_rhoU_300 := (@U.Mal_ameta__G4.Mal_ameta_ROK.rhoU_300 aw rhoL).
Local Abbreviation K_rhoU_low := (@U.Mal_ameta__G4.Mal_ameta_ROK.rhoU_low gd evb avb Hgd Hev Hav aw rhoL).
Local Notation "§20§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav mW aw rhoL HagL) (at level 10, h__ global).
Local Abbreviation K_agU := (§20§ U.Mal_ameta__G4.Mal_ameta_ROK.agU).
Local Abbreviation K_page_facts_hold := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.page_facts_hold).
Local Notation "§21§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW tr md Evm aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_entry_resok := (§21§ U.Mal_ameta__G4.Mal_ameta_ROK.entry_resok).
Local Abbreviation K_LOK := (@U.Mal_ameta__G4.Mal_ameta_ROK.LOK).
Local Abbreviation K_LOK_misc := (@U.Mal_ameta__G4.Mal_ameta_ROK.LOK_misc).
Local Abbreviation K_LOK_ecall := (@U.Mal_ameta__G4.Mal_ameta_ROK.LOK_ecall).
Local Abbreviation K_Pre_resok_fail_eq := (@U.Mal_ameta__G4.Mal_ameta_ROK.Pre_resok_fail_eq).
Local Abbreviation K_Pre_resok_ok_eq := (@U.Mal_ameta__G4.Mal_ameta_ROK.Pre_resok_ok_eq).
Local Abbreviation K_O_ctxOK := (@U.Mal_ameta__G4.Mal_ameta_ROK.O_ctxOK).
Local Abbreviation K_O_brkD := (@U.Mal_ameta__G4.Mal_ameta_ROK.O_brkD).
Local Abbreviation K_O_errF := (@U.Mal_ameta__G4.Mal_ameta_ROK.O_errF).
Local Abbreviation K_UNCH2 := (@U.Mal_ameta__G4.Mal_ameta_ROK.UNCH2).
Local Abbreviation K_stkOK_cells := (@U.Mal_ameta__G4.Mal_ameta_ROK.stkOK_cells).
Local Abbreviation K_LOK_objs := (@U.Mal_ameta__G4.Mal_ameta_ROK.LOK_objs).
Local Abbreviation K_valU := (@U.Mal_ameta__G4.Mal_ameta_ROK.valU s L rho gd evb avb aw).
Local Abbreviation K_valU_rhoU := (§20§ U.Mal_ameta__G4.Mal_ameta_ROK.valU_rhoU).
Local Abbreviation K_valU_ext := (@U.Mal_ameta__G4.Mal_ameta_ROK.valU_ext s L rho gd evb avb Hgd Hev Hav aw).
Local Abbreviation K_memU := (@U.Mal_ameta__G4.Mal_ameta_ROK.memU s mW aw).
Local Notation "§22§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW aw rhoL HagL) (at level 10, h__ global).
Local Abbreviation K_memU_rhoU := (§22§ U.Mal_ameta__G4.Mal_ameta_ROK.memU_rhoU).
Local Abbreviation K_evU := (@U.Mal_ameta__G4.Mal_ameta_ROK.evU s L rho gd evb avb mW aw).
Local Abbreviation K_evU300 := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.evU300).
Local Abbreviation K_LOK_ranges := (@U.Mal_ameta__G4.Mal_ameta_ROK.LOK_ranges s L rho gd evb avb Hgd Hev Hav mW Htp aw).
Local Abbreviation K_segs_inside := (@U.Mal_ameta__G4.Mal_ameta_ROK.segs_inside).
Local Abbreviation K_ro_addr_grant := (§17§ U.Mal_ameta__G4.Mal_ameta_ROK.ro_addr_grant).
Local Notation "§23§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Htp md Evm STK aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_LOK_objs_miss := (§23§ U.Mal_ameta__G4.Mal_ameta_ROK.LOK_objs_miss).
Local Abbreviation K_md2 := (§16§ U.Mal_ameta__G4.Mal_ameta_ROK.md2).
Local Abbreviation K_OKC := (@U.Mal_ameta__G4.Mal_ameta_ROK.OKC s L rho gd evb avb mW tr md aw rhoL).
Local Abbreviation K_mmap_nZ_4096 := (@U.Mal_ameta__G4.Mal_ameta_ROK.mmap_nZ_4096).
Local Abbreviation K_mmap_n_4096 := (@U.Mal_ameta__G4.Mal_ameta_ROK.mmap_n_4096).
Local Abbreviation K_map_contains_head := (@U.Mal_ameta__G4.Mal_ameta_ROK.map_contains_head).
Local Notation "§24§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Htp tr md Kc HKc Evm ok HOK STK aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_stepBC := (§24§ U.Mal_ameta__G4.Mal_ameta_ROK.stepBC).
Local Abbreviation K_LRF2 := (@U.Mal_ameta__G4.Mal_ameta_ROK.LRF2).
Local Abbreviation K_stkRF2_cells := (@U.Mal_ameta__G4.Mal_ameta_ROK.stkRF2_cells).
Local Abbreviation K_CHG2 := (@U.Mal_ameta__G4.Mal_ameta_ROK.CHG2).
Local Abbreviation K_OBJ2 := (@U.Mal_ameta__G4.Mal_ameta_ROK.OBJ2).
Local Abbreviation K_LRF2_objs := (@U.Mal_ameta__G4.Mal_ameta_ROK.LRF2_objs).
Local Abbreviation K_LRF2_misc := (@U.Mal_ameta__G4.Mal_ameta_ROK.LRF2_misc).
Local Notation "§25§ h__" := (h__ gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation K_LRF2_cs := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.LRF2_cs).
Local Abbreviation K_OBJ2_perm := (@U.Mal_ameta__G4.Mal_ameta_ROK.OBJ2_perm rho gd Hgd STK).
Local Abbreviation K_evM64 := (@U.Mal_ameta__G4.Mal_ameta_ROK.evM64 s L rho gd evb avb Hbrk).
Local Abbreviation K_Kcov := (@U.Mal_ameta__G4.Mal_ameta_ROK.Kcov).
Local Abbreviation K_Klits := (@U.Mal_ameta__G4.Mal_ameta_ROK.Klits).
Local Abbreviation K_Kdunk := (@U.Mal_ameta__G4.Mal_ameta_ROK.Kdunk).
Local Abbreviation K_Kvars301 := (@U.Mal_ameta__G4.Mal_ameta_ROK.Kvars301).
Local Abbreviation K_touched := (@U.Mal_ameta__G4.Mal_ameta_ROK.touched s aw).
Local Abbreviation K_touched_dec := (@U.Mal_ameta__G4.Mal_ameta_ROK.touched_dec s aw).
Local Abbreviation K_SC13 := (@U.Mal_ameta__G4.Mal_ameta_ROK.SC13).
Local Abbreviation K_ctx_cells_SC13 := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.ctx_cells_SC13).
Local Abbreviation K_ctx_cell_w8 := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.ctx_cell_w8).
Local Abbreviation K_Hctx' := (§18§ U.Mal_ameta__G4.Mal_ameta_ROK.Hctx').
Local Notation "§26§ h__" := (h__ s L X R U HI aw) (at level 10, h__ global).
Local Abbreviation K_old_head := (§26§ U.Mal_ameta__G4.Mal_ameta_ROK.old_head).
Local Abbreviation K_old_tail := (§26§ U.Mal_ameta__G4.Mal_ameta_ROK.old_tail).
Local Abbreviation K_old_avm := (§26§ U.Mal_ameta__G4.Mal_ameta_ROK.old_avm).
Local Notation "§27§ h__" := (h__ s L X R U HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav Hhd Hcnt Hac Hbrk Hinit aw) (at level 10, h__ global).
Local Abbreviation K_OLD := (§27§ U.Mal_ameta__G4.Mal_ameta_ROK.OLD).
Local Abbreviation K_pre_reg_cs := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.pre_reg_cs).
Local Abbreviation K_reg_sv_null := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.reg_sv_null).
Local Abbreviation K_freg_sv_null := (§25§ U.Mal_ameta__G4.Mal_ameta_ROK.freg_sv_null).
Local Notation "§28§ h__" := (h__ s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr md EmW Hhd Hcnt Hac Hbrk Hinit Kc HKc Evm ok HOK STK aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_fail2_sound := (§28§ U.Mal_ameta__G4.Mal_ameta_ROK.fail2_sound).
Local Abbreviation K_granted_sound := (§28§ U.Mal_ameta__G4.Mal_ameta_ROK.granted_sound).
Local Notation "§29§ h__" := (h__ s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr md EmW Hhd Hcnt Hac Hbrk Hinit Kc HKc Evm ok HOK STK) (at level 10, h__ global).
Local Abbreviation K_resok1_sound := (§29§ U.Mal_ameta__G4.Mal_ameta_ROK.resok1_sound).
Local Notation "§30§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Htp tr md Kc HKc Evm HVI STK aw rhoL HagL Hpl) (at level 10, h__ global).
Local Abbreviation K_granted_ex := (§30§ U.Mal_ameta__G4.Mal_ameta_ROK.granted_ex).

    Local Notation az := K_az.
    Local Notation HIRv := K_HIRv. Local Notation Hctx_C := K_Hctx_C.
    Local Notation G_al := K_G_al. Local Notation G_pos := K_G_pos. Local Notation G_ceil := K_G_ceil. Local Notation G_free := K_G_free.

Local Abbreviation G_rr := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rr).
Local Abbreviation G_lenZ := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.lenZ).
Local Abbreviation G_pnew := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.pnew).
Local Abbreviation G_mnew := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew).
Local Abbreviation G_t1 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t1).
Local Abbreviation G_t2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2).
Local Abbreviation G_rg1 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rg1).
Local Abbreviation G_rg2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.rg2).
Local Abbreviation G_s0_t := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_SPEC1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.SPEC1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_SPEC2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.SPEC2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_HI1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.HI1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_HI2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.HI2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Notation "§31§ h__" := (h__ s Hhd Hcnt Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_t1_fields := (§31§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t1_fields).
Local Abbreviation G_t2_eq := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_eq).
Local Notation "§32§ h__" := (h__ s Hhd Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_t2_fields := (§32§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_fields).
Local Abbreviation G_C_ac := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_ac).
Local Abbreviation G_C_sh := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_sh).
Local Abbreviation G_C_ars := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_ars).
Local Abbreviation G_CHG1 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.CHG1).
Local Abbreviation G_old_ctx1 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_ctx1).
Local Notation "§33§ h__" := (h__ X R U s HI) (at level 10, h__ global).
Local Abbreviation G_res_n_ge2 := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.res_n_ge2).
Local Abbreviation G_ctx_maps_loc := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_maps_loc).
Local Notation "§34§ h__" := (h__ X R U s HI Hhd Hcnt Hac Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_ctx_cells_t1 := (§34§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t1).
Local Abbreviation G_old_noctx_loc := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_noctx_loc X R U s HI HXr).
Local Notation "§35§ h__" := (h__ X R U s HI HXr Hhd Hcnt Hac Hbrk Hinit) (at level 10, h__ global).
Local Abbreviation G_image_t1 := (§35§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t1).
Local Abbreviation G_C_avm2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_avm2).
Local Abbreviation G_C_cnt2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_cnt2).
Local Abbreviation G_C_hd2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_hd2).
Local Abbreviation G_C_tl2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_tl2).
Local Abbreviation G_CHG2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.CHG2).
Local Abbreviation G_old_ctx2 := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_ctx2).
Local Abbreviation G_C_tn := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.C_tn).
Local Abbreviation G_fresh_slot := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fresh_slot).
Local Abbreviation G_pnew_fresh := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.pnew_fresh).
Local Abbreviation G_ctx_cells_t2 := (§34§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t2).
Local Abbreviation G_t2pre := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2pre).
Local Abbreviation G_t2_upd := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2_upd).
Local Abbreviation G_t2pre_fields := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.t2pre_fields).
Local Abbreviation G_mnew_prid := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew_prid).
Local Abbreviation G_area_cells_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.area_cells_t2 X R U s HI Hhd Hbrk Hinit).
Local Abbreviation G_image_t2 := (§35§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t2).
Local Abbreviation G_image_t2C := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.image_t2C X R U s HI HXr Hhd Hbrk Hinit).
Local Abbreviation G_ctx_cells_t2C := (§34§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ctx_cells_t2C).
Local Abbreviation G_fp_t1 := (§31§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_t1).
Local Abbreviation G_fp_t2 := (§32§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_t2).
Local Abbreviation G_ub_t1 := (§31§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ub_t1).
Local Abbreviation G_ub_t2 := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ub_t2).
Local Abbreviation G_footers_t1 := (§31§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.footers_t1).
Local Abbreviation G_footers_t2 := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.footers_t2).
Local Abbreviation G_L' := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L' s L az).
Local Abbreviation G_wa := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.wa az).
Local Abbreviation G_wn := (§14§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.wn).
Local Abbreviation G_vm1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm1 s vm az).
Local Abbreviation G_vm2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm2 s vm az).
Local Abbreviation G_lenZ_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.lenZ_facts s az HB G_al G_pos).
Local Abbreviation G_a_facts := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.a_facts s L az HB G_al G_pos G_ceil).
Local Abbreviation G_ua := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ua s L az HB G_al G_pos G_ceil).
Local Abbreviation G_un := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.un s L az HB G_al G_pos G_ceil).
Local Abbreviation G_grant_vs_image := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_image s C_U vm az HIRv G_al G_pos G_free).
Local Abbreviation G_grant_vs_maps := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_maps s vm az G_al G_pos G_free).
Local Abbreviation G_grant_vs_footprint := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_footprint s L C_U vm az Hctx_C statics_in_image_U HV HIRv G_al G_pos G_free).
Local Abbreviation G_fp_size := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_size s L vm az HV).
Local Abbreviation G_L'_ext := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ext s L az).
Local Abbreviation G_L'_ctx := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ctx s L az).
Local Abbreviation G_L'_reg_new := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_reg_new s L az).
Local Abbreviation G_L'_fp := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_fp X R U s L HI az).
Local Abbreviation G_L'_crange := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_crange X R U s L HI az).
Local Abbreviation G_L'_ub := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_ub X R U s L HI HXr az).
Local Abbreviation G_L'_addr_of := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_addr_of s L az).
Local Abbreviation G_L'_pnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_pnew s L az).
Local Abbreviation G_L'_mnew := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.L'_mnew s L az).
Local Abbreviation G_region_of_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_of_t1 s Hhd Hcnt Hbrk Hinit az G_al G_pos).
Local Abbreviation G_region_of_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_of_t2 s Hhd Hbrk Hinit az G_al G_pos).
Local Abbreviation G_layout_ok_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.layout_ok_t1 X R U s L HI Hhd Hcnt Hbrk Hinit HL az HB G_al G_pos G_ceil).
Local Abbreviation G_layout_ok_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.layout_ok_t2 X R U s L HI Hhd Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_region_live_t := (§33§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.region_live_t).
Local Abbreviation G_old_region_vs_grant := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.old_region_vs_grant s L vm az HV G_al G_pos G_free).
Local Abbreviation G_vm_okX_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_okX_t1 X R U s L HI Hhd Hcnt Hbrk Hinit vm az HV HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_ok_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_ok_t1 X R U s L HI Hhd Hcnt Hbrk Hinit C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_ledger_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ledger_t1 s L C_U vm az statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_okX_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_okX_t2 X R U s L HI Hhd Hcnt Hbrk Hinit vm az HV HB G_al G_pos G_ceil G_free).
Local Abbreviation G_vm_ok_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.vm_ok_t2 X R U s L HI Hhd Hcnt Hbrk Hinit C_U vm az Hctx_C statics_in_image_U HV HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_ledger_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.ledger_t2 s L C_U vm az statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_fp_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.fp_where s L C_U vm az HV HLG G_al G_pos).
Local Abbreviation G_maps_wf_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.maps_wf_t1 s L vm az HB HMW G_al G_pos G_ceil G_free).
Local Abbreviation G_maps_wf_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.maps_wf_t2 s L vm az HB HMW G_al G_pos G_ceil G_free).
Local Abbreviation G_block_where := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.block_where X R U s L HI HXr az G_pos).
Local Abbreviation G_grant_vs_block := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.grant_vs_block X R U s L HI HXr C_U vm az Hctx_C statics_in_image_U HV HIRv G_al G_pos G_free).
Local Abbreviation G_xraw_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.xraw_t1 X s HXr Hhd Hcnt Hbrk Hinit).
Local Abbreviation G_xraw_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.xraw_t2 X R U s HI HXr az).
Local Abbreviation G_mnew_notX := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.mnew_notX X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_keys_t1 := (§31§ OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.keys_t1).
Local Abbreviation G_keys_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.keys_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az).
Local Abbreviation G_am_frame_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.am_frame_t1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_am_frame_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.am_frame_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL).
Local Abbreviation G_bounded34 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34).
Local Abbreviation G_bounded34_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34_t1 s L Hhd Hcnt Hbrk Hinit az HB G_al G_pos G_ceil).
Local Abbreviation G_bounded34_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded34_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_bounded_t1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded_t1 s L Hhd Hcnt Hbrk Hinit az HB G_al G_pos G_ceil).
Local Abbreviation G_bounded_t2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.bounded_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL C_U vm az Hctx_C statics_in_image_U HV HLG HIRv HB G_al G_pos G_ceil G_free).
Local Abbreviation G_cell_where1 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.cell_where1 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az G_al G_pos).
Local Abbreviation G_cell_where2 := (@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.cell_where2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL az G_al G_pos).

    Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S167SbVok;S13cS131Vtr;Vmd';A2A1A3F_;").
    Proof using HOK. intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho). Qed.
    Lemma K2 : Kc tr K_md2.
    Proof using HKc HOK. destruct HOK as (_ & _ & [VI _]). unfold U.Mal_ameta__G4.Mal_ameta_ROK.md2, mprotect_model_next, U.Mal_ameta__G4.Mal_ameta_ROK.md1. apply VI. apply VI. exact HKc. Qed.

    Lemma K2x : Kc tr K_md2.
    Proof using HKc HVI. unfold U.Mal_ameta__G4.Mal_ameta_ROK.md2, mprotect_model_next, U.Mal_ameta__G4.Mal_ameta_ROK.md1. apply HVI. apply HVI. exact HKc. Qed.
    Lemma az64 : 0 <= K_az < 2 ^ 64. Proof using . exact K_az64. Qed.

    Definition LC0 : sstate := ltac2:(tb__ "0|0|
S15eSbbS15dS15fSeaSbSe8Sf0A3S15cA2Sf5Sf0A1A3A1").

    Definition LC : sstate := ltac:(let x := eval vm_compute in LC0 in exact x).
    Lemma LC_eq : LC0 = LC. Proof using . vm_cast_no_check (@eq_refl sstate LC). Qed.
    Definition pageK : sobj := ltac2:(tb__ "0|0|
SffS28S108S26P12cA1S21Z1000A1A3A1").

    Definition subC : list (positive * sv) := ltac2:(tb__ "0|5|
S10S17S9S23A2M0S11S9S23Pc9S27S6dZ9A2M1A4S10G0S11S9S23PccS27S6dZ1M2A2A4S10G0S11S9S23PcdS27S6dZ5A2A4S10G0S11S9S23PceS27S6dZ6A2A4S10G0S11S9S23PcfS27S6dZ7A2A4S10G0S11S9S23Pd0S27S6dZ8A2A4S10G0S11S9S23Pd2S27S6dZaA2A4S10G0S11S9S23Pd3S27S6dZbA2A4S10G0S11S9S23Pd4S27S6dZcA2A4S10G0S11S9S23Pd5S27S6dZdA2A4S10G0S11S9S23Pd6S27S6dZeA2A4S10G0S11S9S23Pd7S27S6dZfA2A4S10G0S11S9S23Pd8S27S6dZ10A2A4S10G0S11S9S23Pd9S27S6dZ11A2A4S10G0S11S9S23PdcS27S6dZ14A2A4S10G0S11S9S23Pe4S27S6dZ1cA2A4S10G0S11S9S23Pe5S27S6dZ1dA2A4S10G0S11S9S23Pe6S27S6dZ1eA2A4S10G0S11S9S23Pe7S27S6dZ1fA2A4S10G0S11S9S23Pb7S28S108S28S109S21Z2A1Se9Pb8M3A1M4A3S21N1A1A3A4S10G0S11S9S23G3S28S108G4S21G2A1A3A4S10G0S11S9S23Pb1G1A4S10G0S11S9S23PbbS21SeeA1A4S16G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
    Definition srcF : sstate := ltac2:(tb__ "0|0|
Sf3S39S34S6dA1S3cS6dA1S37S6dA1S36S6dA1S38S6dA1S18S20S2dS6dA1S10S20S6fS16S20A1A3A3S35S6dA1S33S6dA1S3bS6dA1A9S10S2bS4bS10bSe9PbaA1S21Z0A1A3S16S2bA1A3A2").
    Definition srcN : sstate := ltac2:(tb__ "0|2|
Sf3S39S34S6dA1S3cS6dA1S37S6dA1S36S6dA1S38S6dA1S18S20S2dS6dA1S10S20S6fS10S20Sf2S16S20A1A3A3A3S35S6dA1S33S6dA1S3bS6dA1A9S10S2bS102PbaM0A1S10S2bS4aG0Z3A2S10S2bS41S26G0A1M1S21S5fZ2Z2fA2A1A2S10S2bS41S21Z1000A1G1A2S16S2bA1A3A3A3A3A2").
    Lemma entF : ltac2:(tb__ "0|0|
S0S12S169S71SeaSbSe8Sf6A3S70A3S15A3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma entN : ltac2:(tb__ "0|0|
S0S12S169S72SeaSbSe8Sf7A3S70A3S15A3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma LC_misc : ltac2:(tb__ "0|0|
S1S0S8S34S6dA1Z20e3cA3S1S0S9S33S6dA1P12dA3S1S0S23S27S6dZ9A2S28S108S26P12cA1S21Z1000A1A3A3S0S14S20A1S2dS6dA1S2dS122A1A3A2A2A2").
    Proof using . vm_compute. repeat split; reflexivity. Qed.
    Lemma swfF : ltac2:(tb__ "0|0|
S0S12S49S39S34S6dA1S3cS6dA1S37S6dA1S36S6dA1S38S6dA1S18S20S2dS6dA1S10S20S6fS16S20A1A3A3S35S6dA1S33S6dA1S3bS6dA1A9A1S15A3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma swfN : ltac2:(tb__ "0|0|
S0S12S49S39S34S6dA1S3cS6dA1S37S6dA1S36S6dA1S38S6dA1S18S20S2dS6dA1S10S20S6fS10S20Sf2S16S20A1A3A3A3S35S6dA1S33S6dA1S3bS6dA1A9A1S15A3").
    Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

    Lemma tail_cell_image T : ltac2:(tb__ "0|0|
S0S13S78A1S79Vs;A1S19S78VT;A2A3Sb9SbcSbeScaS7cVT;Z8A2A1U8Sc3S1dS78A1A1A3Sc5Vs;A1A3F_;").
    Proof using HI.
      intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
      assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
      assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
      unfold image. apply in_app_iff. right. apply in_app_iff. left.
      rewrite ET. clear - Hne. induction (st_areas s) as [|a0 t0 IH]; [exfalso; exact (Hne eq_refl)|].
      cbn [areas_cells last]. destruct t0 as [|b0 t'].
      - apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. right. left. reflexivity.
      - apply in_app_iff. right. apply IH. discriminate.
    Qed.

    Section AtCut.
      Variables (msC : machine_state) (rhoC : valuation).
      Hypothesis VC : K_valU rhoC.
      Hypothesis MC : K_memU (rm rhoC).
      Hypothesis ZC : ltac2:(tb__ "0|6|
S6aQ40M0A1S1S5dS5cS11eVaw;A1Z1000M1A2M2S6cG0R1A2M3A2S5eG3S5cG2G1A2A2A2S0S13S6aQ8M4A1M5A1S2aVrhoC;R2A2S19G5S6bG4Z0A2A2A3F_;Fx;").
      Hypothesis HsmC : ltac2:(tb__ "0|0|
S32SbVrhoC;S6dS11S14S128A1S138Vtr;S139VmsC;S11fVmd;Vaw;VrhoL;A3A2A4A4").

      Lemma HromC : rom_ok segsU msC. Proof using HsmC. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmC))))). Qed.
      Lemma pageK_range : ltac2:(tb__ "0|1|
S0S17S8S8A2S29VrhoC;S6fA2S11S8S8S5cS11eVaw;A1Z1000A2M0S5cG0Z40A2A4A3").
      Proof using Evm HMI HagL Hav Hev Hgd Hpl VC.
        clear HsmC ZC MC. unfold obj_range, obj_lo_of, obj_hi_of, pageK, O_page. cbn [ob_base ob_lo ob_hi]. rewrite (K_evU300 rhoC VC). rewrite !soff_lit_small by lia.
        pose proof K_grant_facts as (_ & _ & Hc & _). pose proof K_lenZ_range as [LR _]. pose proof az64. rewrite u64 by (top_ranges; lia). f_equal; lia.
      Qed.

      Lemma hold_pageK : ltac2:(tb__ "0|0|
S31SbVrhoC;S155VmsC;S2aVrhoC;A1A2S6fA4").
      Proof using Evm HMI HagL Hav Hev Hgd Hpl HsmC VC ZC.
        pose proof HromC as HromC. clear HsmC. pose proof K_grant_facts as (_ & _ & Hc & _). pose proof K_lenZ_range as [LR _]. pose proof az64 as A64. top_ranges.
        change pageK with (carved (SAlu ALU_ADD (SVar 300) (SLit 4096)) 0 64
          [(0, 8%nat, SLit 0); (8, 8%nat, SLit 0); (16, 4%nat, SLit 0); (20, 4%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0); (40, 8%nat, SLit 0); (48, 4%nat, SLit 0); (52, 4%nat, SLit 0); (56, 8%nat, SLit 0)]).
        assert (B : bv_unsigned (eval rhoC (SAlu ALU_ADD (SVar 300) (SLit 4096))) = az + 4096) by (rewrite (K_evU300 rhoC VC); apply u64; lia).
        assert (ZB : forall off, 0 <= off < 64 -> rm rhoC (Z_to_bv 64 (az + 4096 + off)) = Some (Z_to_bv 8 0)).
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
S0S13S6aQ8A1A1M0Vm1;Vx;A1Vm2;Vx;A1A3S1S0S12S107SbVm1;Vx;A3S107SbVm2;Vx;A3A3S0G0S106SbVm1;Vx;A3S106SbVm2;Vx;A3A3A2F_;").
      Proof using . intros E. unfold Glue.wok_of, Glue.rd_of. rewrite E. auto. Qed.

      Lemma hold_tailK T : ltac2:(tb__ "0|0|
S0S13S78A1S79Vs;A1S19S78VT;A2A3S31SbVrhoC;S155VmsC;S2aVrhoC;A1A2Sf2A4F_;").
      Proof using Erd Evm Ewok HI HMI HagL Hav Hev Hgd Hpl HsmC MC VC.
        pose proof HromC as HromC. clear HsmC ZC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
        assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
        assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
        assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
        pose proof (area_R T HinT) as (RT1 & RT2 & RT3). top_ranges.
        assert (B : bv_unsigned (eval rhoC (v 186)) = zA T) by (rewrite (K_evU rhoC (v 186) VC eq_refl), ev186, HT; cbn [optrZ]; apply u64; lia).
        assert (NG : forall off, 8 <= off < 16 -> ~ (az <= zA T + off < az + lenZ78)).
        { intros off Hoff G. pose proof K_lenZ_range as [LR _]. rewrite K_lenZ_eq in G.
          apply (G_grant_vs_footprint (LMem T, PGSZ) (zA T + off) (e_area_In s T HinT)); [|exact G]. cbn [fst snd]. unfold zA, addr_of in *. unfold PGSZ. clear - Hoff. lia. }
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

      Lemma LC_objs_miss o : ltac2:(tb__ "0|2|
Sb9S20Vo;S2dS6dA1A3S48S29VrhoC;Vo;A2S11S8S8S5cS11eVaw;A1Z1000M0A2M1S5cG1G0A2A4A2F_;").
      Proof using Evm HMI HagL Hav Hev Hgd Hpl Htp STK VC. intros Ho. pose proof LC_misc as (_ & _ & _ & EO). rewrite EO in Ho. exact (K_LOK_objs_miss rhoC VC o Ho). Qed.

      Lemma enter_first : ltac2:(tb__ "0|0|
S0S13S78A1S79Vs;A1S1dS78A1A3S32SbS170SeaSbSe8Sf6A3S11S14S128A1S138Vtr;S139VmsC;S11fVmd;Vaw;VrhoL;A3A2A4A4F_;").
      Proof using Evm HMI HagL Hav Hev Hgd Hpl HsmC Htp STK VC ZC.
        intros HT. unfold rhoE. apply (entails_sound segsU srcF _ subC rhoC _ entF).
        unfold srcF. apply K_smatch_add_facts_app; [| |vm_compute; reflexivity].
        - apply (smatch_extend_objs segsU rhoC LC tr msC K_md2 [pageK] (ss_next LC) HsmC swfF).
          + constructor; [apply hold_pageK | constructor].
          + constructor; [|constructor]. apply Forall_forall. intros o' Ho'. rewrite pageK_range.
            pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
          + cbn. split; [constructor | exact I].
        - constructor; [|constructor]. cbn [SymState.holds]. unfold branch_taken, bv_eqb. rewrite (K_evU rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ eval]. reflexivity.
      Qed.

      Lemma area_aligned a0 : ltac2:(tb__ "0|0|
Sb9S78Va0;S7aVs;A1A3S0S8S63S135VL;Va0;A2Z1000A2Z0A3F_;").
      Proof using HI HMI.
        clear HsmC ZC MC VC. intros Ha. pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a0 Ha) as (r & o & rga & Ea & Hoo & _ & Hra & Hla & _).
        pose proof HL as (_ & Halign & _). pose proof (Halign _ _ Hra Hla) as RA.
        subst a0. unfold zA, addr_of, loc_addr. cbn [padd prid poff]. clear - Hoo RA. unfold PGSZ in *. Z.to_euclidean_division_equations; lia.
      Qed.
      Lemma tail_range T : ltac2:(tb__ "0|3|
S0S13S78A1S79Vs;A1S19S78VT;A2A3S1S0S17S8S8A2S29VrhoC;Sf2A2S11S8S8S5cS135VL;VT;A2M0Z8M1A2S5cG0Z10A2A4A3S1Sb9S78VT;S7aVs;A1A3S1S5dZ1000M2G0A2S1S5dS5cG0G2A2SaeVL;A1A2S0S8S63G0G1A2Z0A3A2A2A2A2F_;").
      Proof using HI HMI Hav Hev Hgd VC mW.
        clear HsmC ZC MC. intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
        assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
        assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
        assert (HinT : In T (st_areas s)) by (rewrite ET; apply In_last; exact Hne).
        pose proof (area_R T HinT) as (RT1 & RT2 & RT3 & _). top_ranges. pose proof (area_aligned T HinT) as AL.
        split; [|split; [exact HinT|split; [exact RT1|split; [exact RT2|clear - AL; Z.to_euclidean_division_equations; lia]]]].
        unfold obj_range, obj_lo_of, obj_hi_of, O_tail. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
        rewrite (K_evU rhoC (v 186) VC eq_refl), ev186, HT. cbn [optrZ]. rewrite u64 by lia. reflexivity.
      Qed.

      Lemma enter_next T : ltac2:(tb__ "0|0|
S0S13S78A1S79Vs;A1S19S78VT;A2A3S32SbS170SeaSbSe8Sf7A3S11S14S128A1S138Vtr;S139VmsC;S11fVmd;Vaw;VrhoL;A3A2A4A4F_;").
      Proof using Erd Evm Ewok HI HMI HagL Hav Hev Hgd Hpl HsmC Htp MC STK VC ZC.
        pose proof HsmC as SMC. pose proof (hold_tailK T) as HTK. pose proof hold_pageK as HPK. clear HsmC ZC. intros HT. pose proof (tail_range T HT) as (RT & HinT & T1 & T2 & T3). pose proof K_grant_facts as (_ & _ & Hc & _). pose proof K_lenZ_range as [LR _]. pose proof az64 as A64.
        unfold rhoE. apply (entails_sound segsU srcN _ subC rhoC _ entN).
        unfold srcN. apply K_smatch_add_facts_app; [| |vm_compute; reflexivity].
        - apply (smatch_extend_objs segsU rhoC LC tr msC K_md2 [pageK; O_tail] (ss_next LC) SMC swfN).
          + constructor; [apply HPK | constructor; [exact (HTK HT) | constructor]].
          + constructor; [|constructor; [|constructor]]; apply Forall_forall; intros o' Ho'.
            * rewrite pageK_range. pose proof (LC_objs_miss o' Ho') as D. unfold SymState.ranges_disjoint in *. cbn [fst snd] in *. clear - D. lia.
            *
              rewrite RT. pose proof LC_misc as (_ & _ & _ & EO). rewrite EO in Ho'. pose proof (in_map (obj_range rhoC) _ _ Ho') as RO. rewrite (K_LOK_ranges rhoC VC) in RO.
              pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
              assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
              destruct (G_fp_where (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as [[E _]|(pp & _ & _ & NI)]; [discriminate|].
              cbn [mc_img_lo mc_img_hi C_U] in NI. clear - RO S2 T1 T2 NI. top_ranges.
              unfold SymState.ranges_disjoint. cbn [fst snd].
              destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|].
              repeat (destruct RO as [E|RO]; [rewrite <- E; cbn [fst snd]; lia|]). destruct RO.
          + cbn. split; [constructor; [|constructor]|split; [constructor|exact I]].
            rewrite pageK_range, RT. unfold SymState.ranges_disjoint. cbn [fst snd].
            assert (RX : loc_addr L (fst (LMem T, PGSZ)) <= zA T + 8 < loc_addr L (fst (LMem T, PGSZ)) + snd (LMem T, PGSZ)) by (cbn [fst snd]; clear; unfold zA, addr_of, PGSZ; lia).
            pose proof (G_grant_vs_footprint (LMem T, PGSZ) (zA T + 8) (e_area_In s T HinT) RX) as NG.
            rewrite <- K_lenZ_eq in NG. clear - NG LR. lia.
        - pose proof (K_evU rhoC (v 186) VC eq_refl) as E186. rewrite ev186, HT in E186. cbn [optrZ] in E186. change (v 186) with (SVar 186) in E186. cbn [eval] in E186.
          assert (U186 : bv_unsigned (Z_to_bv 64 (zA T)) = zA T) by (apply u64; clear - T1 T2; top_ranges; lia).
          clear MC.
          unfold nz_fact. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [SymState.holds eval v]; rewrite ?E186, ?U186.
          + unfold branch_taken, bv_eqb. rewrite ?U186. change (bv_unsigned (Z_to_bv 64 0)) with 0. replace (zA T =? 0) with false by (symmetry; apply Z.eqb_neq; clear - T1; lia). discriminate.
          + split; [clear; lia|]. change (2 ^ 3) with 8. exact T3.
          + change (bv_unsigned (Z_to_bv 64 (2 ^ 47))) with (2 ^ 47). clear - T2. top_ranges. lia.
          + change (bv_unsigned (Z_to_bv 64 4096)) with 4096. exact T1.
      Qed.
    End AtCut.

    Local Abbreviation PZ := (az + 4096).
    Local Abbreviation W183 := (res_n s - 1).
    Local Abbreviation W184 := (st_meta_alloc_shift s + 1).
    Local Abbreviation VALF := (U.Mal_ameta__G2.Mal_ameta_C2E.valF s L rho gd evb avb mW PZ W183 W184 (-1)).
    Definition GRr (x : Z) : Prop := ltac2:(tb__ "0|1|
S1S5dS11eVaw;A1M0Vx;A2S5eVx;S5cG0S124Vs;A1A2A2A2").

    Lemma ev_acountX rhoX : ltac2:(tb__ "0|1|
S121Vs;VL;Vrho;Vgd;Vevb;Vavb;Vaw;VrhoX;A8S0S6aQ40M0A1S25VrhoX;S28S108S28S109S21Z2A1Se9Pb8A1A3S21N1A1A3A2S6bG0S61S156Vs;A1Z1A2A2A3F_;").
    Proof using HI HMI Hav Hev Hgd mW.
      intros VX. pose proof HB as (_ & SH & _). pose proof G_res_n_ge2 as R2.
      rewrite (K_evU rhoX (SAlu ALU_ADD (SAlu ALU_SLL (SLit 2) (v 184)) (SLit (-1))) VX eq_refl). rewrite (ev1 mW) by reflexivity. f_equal.
      cbn [zeval zalu]. rewrite ze_v, (zr1_var 184 _ eq_refl).
      assert (P27 : 2 <= 2 * 2 ^ st_meta_alloc_shift s <= 2 ^ 35).
      { split; [assert (1 <= 2 ^ st_meta_alloc_shift s) by (apply (Z.pow_le_mono_r 2 0); lia); lia|].
        change (2 ^ 35) with (2 * 2 ^ 34). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
      rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia. rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia.
      rewrite (Z.mod_small (st_meta_alloc_shift s) 64) by lia. change (2 mod 2 ^ 64) with 2.
      rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (2 * _)) by lia. unfold res_n. rewrite Z.shiftl_mul_pow2 by lia.
      change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
      replace (2 * 2 ^ st_meta_alloc_shift s + (2 ^ 64 - 1)) with ((2 * 2 ^ st_meta_alloc_shift s - 1) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    Qed.
    Lemma ev_shiftX rhoX : ltac2:(tb__ "0|2|
S121Vs;VL;Vrho;Vgd;Vevb;Vavb;Vaw;VrhoX;A8S0S6aQ40M0A1S25VrhoX;S28S108Se9Pb8A1S21Z1M1A1A3A2S6bG0S5cS7bVs;A1G1A2A2A3F_;").
    Proof using HMI Hav Hev Hgd mW.
      intros VX. pose proof HB as (_ & SH & _).
      rewrite (K_evU rhoX (SAlu ALU_ADD (v 184) (SLit 1)) VX eq_refl). rewrite (ev1 mW) by reflexivity. f_equal.
      cbn [zeval zalu]. rewrite ze_v, (zr1_var 184 _ eq_refl). change (1 mod 2 ^ 64) with 1.
      rewrite !(Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia. apply Z.mod_small. lia.
    Qed.

    Lemma valF_enter rhoC : ltac2:(tb__ "0|1|
S121Vs;VL;Vrho;Vgd;Vevb;Vavb;Vaw;VrhoC;A8S17dVs;VL;Vrho;Vgd;Vevb;Vavb;VmW;S5cS11eVaw;A1Z1000A2S61S156Vs;A1Z1M0A2S5cS7bVs;A1G0A2N1S178VrhoC;S70A2AcF_;").
    Proof using Evm HI HMI HagL Hav Hev Hgd Hinit Hpl STK.
      intros VC. pose proof VC as [(A1 & A2 & A3) A4].
      assert (LOW : forall j, (j < 300)%positive -> ~ In j [177; 183; 184; 187; 201; 204; 205; 206; 207; 208; 210; 211; 212; 213; 214; 215; 216; 217; 220; 228; 229; 230; 231]%positive ->
                    rw (rho_sub rhoC subC) j = rw rhoC j).
      { intros j Hj NI. unfold rho_sub. cbn [rw].
        assert (E : wsub_get subC j = SVar j).
        { unfold subC. cbn [wsub_get].
          repeat match goal with |- context [Pos.eqb ?a ?b] => let e := fresh in destruct (Pos.eqb a b) eqn:e; [apply Pos.eqb_eq in e; exfalso; apply NI; rewrite <- e; cbn; tauto|] end.
          reflexivity. }
        rewrite E. reflexivity. }
      split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - intros j Hj. rewrite LOW; [| unfold AM_NEXT; lia | cbn; intros HH; repeat (destruct HH as [HH|HH]; [lia|]); exact HH].
        rewrite <- (A1 j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj.
      - intros j Hj. cbn in Hj.
        assert (Hj' : (j < 300)%positive /\ ~ In j [177; 183; 184; 187; 201; 204; 205; 206; 207; 208; 210; 211; 212; 213; 214; 215; 216; 217; 220; 228; 229; 230; 231]%positive).
        { repeat (destruct Hj as [<-|Hj]; [split; [reflexivity | cbn; intros HH; repeat (destruct HH as [HH|HH]; [discriminate|]); exact HH]|]). destruct Hj. }
        destruct Hj' as [H1 H2]. rewrite (LOW j H1 H2). rewrite <- (A1 j H1). reflexivity.
      -   rewrite LOW; [| unfold AM_NEXT; lia | cbn; intros HH; repeat (destruct HH as [HH|HH]; [lia|]); exact HH].
        rewrite <- (A1 175%positive) by (unfold AM_NEXT; lia). transitivity (Z_to_bv 64 secZ); [exact (rw1_v 175 _ eq_refl) | unfold U.Mal_ameta__G1.Mal_ameta_I.secZ; rewrite Hinit; reflexivity].
      - unfold rho_sub. cbn [rw wsub_get subC Pos.eqb]. pose proof LC_misc as (_ & _ & E9 & _). cbn. rewrite E9 || idtac. exact (K_evU300 rhoC VC).
      - unfold rho_sub. cbn. exact (ev_acountX rhoC VC).
      - unfold rho_sub. cbn. exact (ev_shiftX rhoC VC).
      - unfold rho_sub. cbn. apply bv_eq. reflexivity.
      - intros l. unfold rho_sub. cbn [rl]. rewrite <- A2. reflexivity.
    Qed.

    Lemma vm2_eq : ltac2:(tb__ "0|0|
S0S12aS12bS11fVmd;Vaw;VrhoL;A3A1S118Vs;Vvm;S11eVaw;A1A3A3").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl.
      unfold U.Mal_ameta__G4.Mal_ameta_ROK.md2, mprotect_model_next. rewrite m_vmmaps_with_vmmaps. rewrite K_vm1_eq.
      unfold AllocMetaGrow.vm2, AllocMetaGrow.vm1. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base].
      rewrite (u64 (az + 4096)) by (pose proof K_grant_facts as (_ & _ & Hc & _); pose proof K_lenZ_range as [LR _]; pose proof az64; top_ranges; lia).
      change (bv_unsigned (Z_to_bv 64 4096)) with 4096. unfold PGSZ. reflexivity.
    Qed.
    Lemma R_HF : ltac2:(tb__ "0|6|
S1S0S14S78A1S7aS114Vs;A1M0A1S18S78S7aVs;A1S10S78S115Vs;A1M1S16S78A1A3A3A3S1S0S12S90G0A1S15A3S1S0S13S78A1M2S81G0A1S1dS78A1A3S1S0S78S7fG0A1S7cS112Vs;A1S86A2A3S1S0S8S8eG0A1S61S93Z1M3A2A3S1S0S8S8cG0A1S61S61S156Vs;A1G3A2G3A2A3S1S0S8S7bG0A1S5cS7bVs;A1G3A2A3S1S0G2S7eG0A1G2G2Lx;S7eVs;A1S78S19S78R1A2Ls0;S19S78G1A2M4X13x2A3S1S0G2S79G0A1G4A3S1S0S78S8dG0A1S7cG1Z1000A2A3S1S0S14G2A1S8bG0A1S8bVs;A1A3S1S0S14S8A1M5S92G0A1S92Vs;A1A3S1S0G5S91G0A1S91Vs;A1A3S1S0G5S8fG0A1S8fVs;A1A3S1S0S8S83G0A1S83Vs;A1A3S0S8S82G0A1S82Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
    Proof using Hbrk Hhd Hinit. pose proof G_t2_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19). repeat split; assumption. Qed.
    Lemma R_brk2 : ltac2:(tb__ "0|0|
S0S8Sc1S111Vs;VL;S11eVaw;A1A3S17cS114Vs;A1A1A2N1A3").
    Proof using Hbrk Hhd Hinit. unfold U.Mal_ameta__G2.Mal_ameta_C2E.brk_sval. pose proof G_t2_fields as (_ & _ & _ & F4 & _). rewrite F4. reflexivity. Qed.
    Lemma R_V183 : 1 <= W183 < 2 ^ 62.
    Proof using HI HMI Hav Hev Hgd.
      pose proof G_res_n_ge2 as R2. pose proof HB as (_ & SH & _). unfold res_n in *. rewrite Z.shiftl_mul_pow2 in * by lia.
      assert (2 ^ st_meta_alloc_shift s <= 2 ^ 34) by (apply Z.pow_le_mono_r; lia). lia.
    Qed.
    Lemma R_V184 : 0 <= W184 < 2 ^ 62. Proof using HMI Hav Hev Hgd. pose proof HB as (_ & SH & _). lia. Qed.
    Lemma R_fresh j : ltac2:(tb__ "0|0|
S5dZ0Vj;A2S0S13S89A1SdeVs;S7cS115Vs;A1S5cS84S66S86Vj;A2A2A2A2S1dS89A1A3F_;").
    Proof using HI. intros Hj. apply G_fresh_slot. reflexivity. Qed.
    Lemma R_mnew : ltac2:(tb__ "0|0|
S0S78S112Vs;A1S7cS115Vs;A1Z18A2A3"). Proof using . reflexivity. Qed.
    Lemma R_Lsec : ltac2:(tb__ "0|0|
S0S8ScfS111Vs;VL;S11eVaw;A1A3A1ScfVL;A1A3"). Proof using . reflexivity. Qed.
    Lemma R_PZ : ltac2:(tb__ "0|1|
S0S8Sc2S111Vs;VL;S11eVaw;A1M0A3ScaS115Vs;A1A1A2S5cG0Z1000A2A3"). Proof using . pose proof G_L'_pnew as E. unfold PGSZ in E. exact E. Qed.
    Lemma R_addr : ltac2:(tb__ "0|1|
S0S8Sb4S111Vs;VL;S11eVaw;A1M0A3S112Vs;A1A2S5cS5cG0Z1000A2S84A2A3"). Proof using . pose proof G_L'_mnew as E. unfold PGSZ in E. exact E. Qed.
    Lemma R_pzR : ltac2:(tb__ "0|3|
S1S5dZ1000M0S5cS11eVaw;A1G0A2M1A2S1S5dS5cG1G0A2SaeVL;A1A2S1S0S8S63G1G0A2Z0M2A3S1S5dG2G1A2S5eG1S5fZ2Z40A2A2A2A2A2A2").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl STK.
      pose proof K_grant_facts as (Hal & Hpos & Hc & _). pose proof K_lenZ_range as [LR _]. pose proof az64 as A64. top_ranges. unfold PGSZ in Hal.
      split; [lia|]. split; [lia|]. split; [Z.to_euclidean_division_equations; lia | lia].
    Qed.
    Lemma R_cw2 c x : ltac2:(tb__ "0|7|
Sb9SbcVc;S18SbcSc5S114Vs;A1M0A1S159G0A1A3A3S1S5dSc2S111Vs;VL;S11eVaw;A1M1A3Sc7Vc;A1A2M2Vx;A2S5eVx;S5cG2S60Sd0Vc;A1A1A2A2A2S4S3S17Sc0S8A2M3G3S1Sb9G3R1ScdVs;A1A3S1S5dSc2VL;S1bSc0S8R1A3A2M4Vx;A2S5eVx;S5cG4S1cSc0S8R1A3A2A2A2A2Le;A2S1S5dS5cG1Z1000M5A2M6Vx;A2S5eVx;S5cG6G5A2A2A2A2F_;F_;").
    Proof using Evm HI HMI HXr Hac HagL Hav Hbrk Hcnt Hev Hgd Hhd Hinit Hpl. intros Hc Hx. destruct (G_cell_where2 c x Hc Hx) as [H|H]; [left; exact H | right; unfold PGSZ in H; lia]. Qed.
    Lemma R_GRdec x : ltac2:(tb__ "0|1|
S163S6eVx;A1M0S2G0A1A2"). Proof using . unfold GRr. apply range_dec. Qed.
    Lemma R_GRpage x : ltac2:(tb__ "0|2|
S1S5dS5cS11eVaw;A1Z1000M0A2M1Vx;A2S5eVx;S5cG1G0A2A2A2S6eVx;A1F_;"). Proof using HMI Hav Hev Hgd. pose proof K_lenZ_range as [LR _]. unfold GRr. lia. Qed.
    Lemma R_GRimg x : ltac2:(tb__ "0|0|
S6eVx;A1S2S1S5dSb8SacA1Vx;A2S5eVx;Sb7SacA1A2A2A1F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl. intros G Hi. apply (G_grant_vs_image x Hi). rewrite <- K_lenZ_eq. exact G. Qed.
    Lemma R_GRfp e x : ltac2:(tb__ "0|1|
Sb9S17Sc0S8A2Ve;ScdVs;A1A3S1S5dSc2VL;S1bSc0S8Ve;A3A2M0Vx;A2S5eVx;S5cG0S1cSc0S8Ve;A3A2A2A2S2S6eVx;A1A1F_;F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl. intros He Hx G. apply (G_grant_vs_footprint e x He Hx). rewrite <- K_lenZ_eq. exact G. Qed.
    Lemma R_GRceil x : ltac2:(tb__ "0|0|
S6eVx;A1S1S5dZ1000Vx;A2S5eVx;SaeVL;A1A2A2F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl. pose proof K_grant_facts as (Hal & Hpos & Hc & _). unfold GRr, PGSZ in *. intros G. split; [Z.to_euclidean_division_equations; lia | lia]. Qed.
    Lemma R_GRmaps k rg x : ltac2:(tb__ "0|1|
S0S13S8aA1Se5Vs;Vk;A2S19S8aVrg;A2A3S0S12S99Vrg;A1S15A3S0S9aS97Vrg;A1S94A3S1S5dSe2VL;Vk;A2M0Vx;A2S5eVx;S5cG0S98Vrg;A1A2A2A2S2S6eVx;A1A1F_;F_;F_;F_;").
    Proof using Evm HMI HagL Hav Hev Hgd Hpl. intros Hk Hl Hkd Hx G. apply (G_old_region_vs_grant k rg x Hk Hl (or_introl Hkd) Hx). rewrite <- K_lenZ_eq. exact G. Qed.
    Lemma R_GRblock b n x : ltac2:(tb__ "0|0|
Sb9S17S8S8A2S11S8S8Vb;Vn;A4Sb5VL;Vs;A2A3S1S5dVb;Vx;A2S5eVx;S5cVb;Vn;A2A2A2S2S6eVx;A1A1F_;F_;").
    Proof using Evm HI HMI HXr HagL Hav Hev Hgd Hpl. intros Hin Hx G. apply (G_grant_vs_block b n x Hin Hx). rewrite <- K_lenZ_eq. exact G. Qed.
    Lemma R_notX : ltac2:(tb__ "0|1|
S1S0S12Se4S112Vs;A1M0VX;A2S1eA3Sb9S78G0Se1S114Vs;A1A1A3A2"). Proof using HI HMI HXr Hac Hbrk Hcnt Hhd Hinit. pose proof G_mnew_notX as (A & B & _). auto. Qed.
    Lemma R_Y : ltac2:(tb__ "0|2|
Se6S17S13S78A1M0S88A2S96Vs;A1S158S157Vs;A1Z1M1G1A3S11G0S88S19S78S112Vs;A1A2S114Vs;A1A4A4").
    Proof using HI HMI HXr Hac Hbrk Hcnt Hhd Hinit. pose proof (yields_NB s Hhd Hcnt Hac Hbrk 1 1) as Y. unfold r_RES in Y. cbn [Z.eqb] in Y. rewrite G_s0_t in Y. exact Y. Qed.

    Local Ltac c2e_args tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_sound s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc ok K_md2 G_vm2 HOK K2 vm2_eq STK HFpre G_t2 G_L' G_pnew G_mnew PZ W183 W184 (-1) (tr_RES (s0 s) 1 1)
             G_HI2 G_xraw_t2 G_layout_ok_t2 G_vm_ok_t2 (proj1 G_ledger_t2) (proj2 (proj2 G_ledger_t2)) G_bounded_t2 G_maps_wf_t2
             R_HF R_brk2 R_V183 R_V184 G_image_t2C G_ctx_cells_t2C G_area_cells_t2 R_fresh G_pnew_fresh R_mnew G_fp_t2 G_ub_t2
             G_L'_ext G_L'_ctx R_Lsec G_L'_fp G_L'_ub G_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRr R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock G_block_where G_fp_where
             R_notX (AllocMetaGrow.keys_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) G_am_frame_t2 R_Y).

    Theorem okc_sound : ltac2:(tb__ "0|0|
S1aS73S74SbVok;R2S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A4S120Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;Vaw;VrhoL;R2AcS75SbVok;R4R3A4F_;F_;Fw;Fn;").
    Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HOK HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros n w HQ (rhoK & VK & MK & ZK & Hw).
      pose proof (alloc_meta_run_P A78_res_ok_ok ok (Kexact tr K_md2) rhoK (ok_frame_exact ok Kc tr K_md2 HOK K2)) as RUN1.
      refine (RUN1 n _ w Hw).
      intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (K_valU_ext rhoK rhoC 301 VK ltac:(reflexivity) HagC) as VC.
      assert (MC : K_memU (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MK x Hx)).
      assert (ZC : forall x : word, az + 4096 <= bv_unsigned x < az + 4096 + 4096 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZK x Hx)).
      pose proof (valF_enter rhoC VC) as VE.
      assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 K_md2) ->
                   Safety.safe segsU ok n (tr, mkCfg ms1 K_md2)).
      { intros HE. c2e_args ltac:(fun t => apply (t n ms1 (rho_sub rhoC subC) HQ VE)); [| |exact HE].
        - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
        - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
      apply GO. unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
      - exact (enter_next ms1 rhoC VC MC ZC HsmC T HT).
      - exact (enter_first ms1 rhoC VC ZC HsmC HT).
    Qed.

    Local Ltac c2e_argsK tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_soundK s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc ok K_md2 G_vm2 HOK K2 vm2_eq STK HFpre G_t2 G_L' G_pnew G_mnew PZ W183 W184 (-1) (tr_RES (s0 s) 1 1)
             G_HI2 G_xraw_t2 G_layout_ok_t2 G_vm_ok_t2 (proj1 G_ledger_t2) (proj2 (proj2 G_ledger_t2)) G_bounded_t2 G_maps_wf_t2
             R_HF R_brk2 R_V183 R_V184 G_image_t2C G_ctx_cells_t2C G_area_cells_t2 R_fresh G_pnew_fresh R_mnew G_fp_t2 G_ub_t2
             G_L'_ext G_L'_ctx R_Lsec G_L'_fp G_L'_ub G_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRr R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock G_block_where G_fp_where
             R_notX (AllocMetaGrow.keys_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) G_am_frame_t2 R_Y).

    Theorem okc_soundK : ltac2:(tb__ "0|1|
S1aS73S73S10dSbScVrho;S10S17S2cS10eA2M0S11S2cS10eS13fS103A1S13eSbSacVX;VR;VU;Se7Vs;VL;A2VKc;A7A4S16G0A1A3R1A5S0S129S13aS77R2A1A1S11fVmd;Vaw;VrhoL;A3A3S75SbVok;R5R3A4F_;F_;Fw';S120Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;Vaw;VrhoL;R2AcS75SbVok;R4R3A4F_;F_;Fw;Fn;").
    Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HOK HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros n w HQ (rhoK & VK & MK & ZK & Hw).
      pose proof (alloc_meta_run_P A78_res_ok_ok ok (Kexact tr K_md2) rhoK (ok_frame_exact ok Kc tr K_md2 HOK K2)) as RUN1.
      refine (RUN1 n _ w Hw).
      intros [tr1 [ms1 mdx]] (Lf & rhoC & HinL & HagC & HsmC & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (K_valU_ext rhoK rhoC 301 VK ltac:(reflexivity) HagC) as VC.
      assert (MC : K_memU (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MK x Hx)).
      assert (ZC : forall x : word, az + 4096 <= bv_unsigned x < az + 4096 + 4096 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZK x Hx)).
      pose proof (valF_enter rhoC VC) as VE.
      assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 K_md2) ->
                   Safety.safe segsU ok n (tr, mkCfg ms1 K_md2)).
      { intros HE. c2e_argsK ltac:(fun t => apply (t n ms1 (rho_sub rhoC subC) HQ VE)); [| |exact HE].
        - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
        - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
      apply GO. unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
      - exact (enter_next ms1 rhoC VC MC ZC HsmC T HT).
      - exact (enter_first ms1 rhoC VC ZC HsmC HT).
    Qed.

    Local Ltac c2e_ex_args tac :=
      tac (U.Mal_ameta__G2.Mal_ameta_C2E.c2e_ex s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr EmW
             Kc K_md2 G_vm2 K2x vm2_eq STK HFpre G_t2 G_L' G_pnew G_mnew PZ W183 W184 (-1) (tr_RES (s0 s) 1 1)
             G_HI2 G_xraw_t2 G_layout_ok_t2 G_vm_ok_t2 (proj1 G_ledger_t2) (proj2 (proj2 G_ledger_t2)) G_bounded_t2 G_maps_wf_t2
             R_HF R_brk2 R_V183 R_V184 G_image_t2C G_ctx_cells_t2C G_area_cells_t2 R_fresh G_pnew_fresh R_mnew G_fp_t2 G_ub_t2
             G_L'_ext G_L'_ctx R_Lsec G_L'_fp G_L'_ub G_L'_addr_of R_PZ R_addr R_pzR R_cw2
             GRr R_GRdec R_GRpage R_GRimg R_GRfp R_GRceil R_GRmaps R_GRblock G_block_where G_fp_where
             R_notX (AllocMetaGrow.keys_t2 X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) G_am_frame_t2 R_Y).

    Theorem okc_ex : ltac2:(tb__ "0|1|
S73S120Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;Vaw;VrhoL;R1AcS76SbS73S0S73R1R3A3Lw';S73S1S10dSbScVrho;S10S17S2cS10eA2M0S11S2cS10eS13fS103A1S13eSbSacVX;VR;VU;Se7Vs;VL;A2VKc;A7A4S16G0A1A3R1A5S0S129S13aS77R1A1A1S11fVmd;Vaw;VrhoL;A3A3A2Lw';A3F_;Fw;").
    Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HVI HXr Hac HagL Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hpl Hrom Htp STK.
      intros w (rhoK & VK & MK & ZK & Hw) w0 ->.
      destruct (alloc_meta_run_ex_P A78_res_ok_ok (Kexact tr K_md2) rhoK w Hw)
        as ([tr1 [ms1 mdx]] & ST1 & Lf & rhoC & HinL & HagC & HsmC & HK1).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
      destruct (Posts_am_P_shape A78_res_ok_ok) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
      assert (ELF : lf_state L0 = LC) by (rewrite <- LC_eq; unfold LC0; rewrite EP; reflexivity). rewrite ELF in HsmC. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmC.
      assert (NX : ss_next (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P A78_res_ok_ok) = 301%positive) by (vm_compute; reflexivity). rewrite NX in HagC.
      pose proof (K_valU_ext rhoK rhoC 301 VK ltac:(reflexivity) HagC) as VC.
      assert (MC : K_memU (rm rhoC)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (MK x Hx)).
      assert (ZC : forall x : word, az + 4096 <= bv_unsigned x < az + 4096 + 4096 -> rm rhoC x = Some (Z_to_bv 8 0)) by (intros x Hx; destruct HagC as (_ & _ & M); rewrite <- (M x); exact (ZK x Hx)).
      pose proof (valF_enter rhoC VC) as VE.
      assert (GO : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 K_md2) ->
                   etriple segsU (fun w' => w' = (tr, mkCfg ms1 K_md2))
                     (fun w' => LQP segsU NF rho [(L_am_ok IEC_U, JL_am_ok segsU C_U X R U (mkMA s L) Kc)] w' /\ cfg_model (w_cfg w') = K_md2)).
      { intros HE. c2e_ex_args ltac:(fun t => apply (t ms1 (rho_sub rhoC subC) VE)); [| |exact HE].
        - intros x Hx. cbn [rho_sub rm]. apply MC. exact Hx.
        - intros x Hx. cbn [rho_sub rm]. apply ZC. exact Hx. }
      assert (HE : smatch segsU (rho_sub rhoC subC) (U.Mal_ameta__G1.Mal_ameta_runs.Pre_am segsU AM_P (U.Mal_ameta__G2.Mal_ameta_C2E.segF (U.Mal_ameta__G2.Mal_ameta_C2E.bT s))) (tr, mkCfg ms1 K_md2)).
      { unfold U.Mal_ameta__G2.Mal_ameta_C2E.bT. destruct (st_area_tail s) as [T|] eqn:HT.
        - exact (enter_next ms1 rhoC VC MC ZC HsmC T HT).
        - exact (enter_first ms1 rhoC VC ZC HsmC HT). }
      destruct (GO HE (tr, mkCfg ms1 K_md2) eq_refl) as (w3 & ST3 & HQ3).
      exists w3. split; [eapply wsteps_trans; [exact ST1 | exact ST3] | exact HQ3].
    Qed.
  End Granted.

  Theorem resok_ex : ltac2:(tb__ "0|1|
S8S73S127Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;R2R1AbS76SbS73S0S73R1R3A3Lw';S73S1S10dSbScVrho;S10S17S2cS10eA2M0S11S2cS10eS13fS103A1S13eSbSacVX;VR;VU;Se7Vs;VL;A2VKc;A7A4S16G0A1A3R1A5S161S13aS77R1A1A1R4A2A2Lw';A3F_;Fw;FXb;").
  Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HVI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Htp STK.
    intros Xb w (aw & rhoL & HagL & Hpl & Hw & HRb) w0 ->.
    destruct (U.Mal_ameta__G4.Mal_ameta_ROK.granted_ex s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Htp tr md Kc HKc Evm HVI STK aw rhoL HagL Hpl
                Xb w HRb Hw w eq_refl) as (w2 & ST2 & HC2 & HR2).
    destruct (okc_ex aw rhoL HagL Hpl w2 HC2 w2 eq_refl) as (w3 & ST3 & HQ3 & E3).
    exists w3. split; [eapply wsteps_trans; [exact ST2 | exact ST3]|]. split; [exact HQ3|]. rewrite E3. exact HR2.
  Qed.

  Theorem resok_S : ltac2:(tb__ "0|3|
S1aS6aQ40M0A1S30S2eSebS130Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R1A3S151S6bG0Z0A2Vmd;S25R2SecA2R3A4S1S0S12S15aS123Vmd;R4R3A3S6bG0S5cS11eR4A1Z1000M1A2A2S6bG0G1A2A3S15A3S73S10dSbScVrho;S10S17S2cS10eA2M2S11S2cS10eS13fS103A1S13eSbSacVX;VR;VU;Se7Vs;VL;A2VKc;A7A4S16G2A1A3R1A5S0S129S13aS77R2A1A1S11fVmd;R6R5A3A3S75SbVok;R8R3A4F_;F_;Fw';A2F_;F_;FrhoL;Faw;S74SbVok;R2S126Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4F_;Fn;").
  Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Htp STK.
    intros n HC. apply (U.Mal_ameta__G4.Mal_ameta_ROK.resok1_S s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Htp tr md Kc HKc Evm ok HOK STK n).
    intros aw rhoL HagL Hpl. destruct (HC aw rhoL HagL Hpl) as [HB HK]. split; [exact HB|].
    intros w HCw. exact (okc_soundK aw rhoL HagL Hpl n w HK HCw).
  Qed.

  Theorem resok_anyex : ltac2:(tb__ "0|0|
S73S126Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;R1AaS76SbS73S0S73R1R3A3Lw';S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A3F_;Fw;").
  Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HVI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Htp STK.
    intros w (aw & rhoL & HagL & Hpl & Hw) w0 ->.
    destruct (U.Mal_ameta__G4.Mal_ameta_ROK.granted_anyex s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr md EmW
                Hhd Hcnt Hac Hbrk Hinit Kc HKc Evm HVI STK aw rhoL HagL Hpl w Hw w eq_refl) as (w2 & ST2 & [HL2 | HC2]).
    - exists w2. split; [exact ST2 | exact HL2].
    - destruct (okc_ex aw rhoL HagL Hpl w2 HC2 w2 eq_refl) as (w3 & ST3 & HQ3 & _).
      exists w3. split; [eapply wsteps_trans; [exact ST2 | exact ST3]|].
      destruct HQ3 as (L0 & JL0 & rho' & Hin0 & Hrest). destruct Hin0 as [E0|[]].
      exists L0, JL0, rho'. split; [right; left; exact E0 | exact Hrest].
  Qed.

  Theorem resok_sound : ltac2:(tb__ "0|0|
S1aS74SbVok;R1S73S10dSbScVrho;S13dSbSacS103VX;VR;VU;Se7Vs;VL;A2VKc;A8R1A5Lw';A4S74SbVok;R2S126Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;Vtr;Vmd;A9A4F_;Fn;").
  Proof using EmW Erd Evm Ewok HFpre HI HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom Htp STK.
    intros n HQ. apply (U.Mal_ameta__G4.Mal_ameta_ROK.resok1_sound s L X R U rho HI HXr rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom Hgd_rd Hav_rd Htp tr md EmW
             Hhd Hcnt Hac Hbrk Hinit Kc HKc Evm ok HOK STK n HQ).
    intros aw rhoL HagL Hpl w HC. exact (okc_sound aw rhoL HagL Hpl n w HQ HC).
  Qed.
End Cut78r.

End InstX.

End Mal_ameta_R2E.
