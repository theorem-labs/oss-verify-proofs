(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "True"; "iff"; "False"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "list"; "option"; "prod"; "nil"; "app"; "true"; "Some"; "fst"; "nat"; "None"; "snd"; "false"; "andb"; "length"; "orb"; "negb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "cell"; "mkCell"; "SVar"; "sv"; "eval"; "obj_range"; "rw"; "rm"; "reg_sv"; "SAlu"; "smatch"; "sstate"; "obj_holds"; "agree_below"; "valuation"; "DUnknown"; "mkObj"; "soff"; "ss_objs"; "FcsrFrm0"; "odefault"; "rl"; "ss_next"; "ss_pc"; "c_width"; "ob_cells"; "c_off"; "c_val"; "fcsr_match"; "freg_sv"; "fregs_match"; "mkVal"; "ob_base"; "ob_dflt"; "obj_wf"; "outside_all"; "regs_match"; "resv_match"; "sfcsr"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "tfact"; "enc_bytes"; "holds"; "ranges_disjoint"; "sprop"; "ss_facts"; "sv_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_reg"; "pre_fregs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "to_nat"; "pow"; "of_nat"; "sub"; "mul"; "modulo"; "eqb"; "leb"; "ltb"; "opp"; "shiftl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "padd"; "st_area_tail"; "st_areas"; "brkst"; "region"; "st_area_head"; "PGSZ"; "SP"; "st_brk"; "st_free_meta_head"; "st_meta_alloc_shift"; "st_mmap_counter"; "st_seq"; "AREA_HDR"; "META_SIZE"; "astate"; "mslot"; "st_active"; "st_avail_meta"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_bounces"; "st_init_done"; "st_regions"; "st_unmap_seq"; "st_usage"; "BrkDead"; "METAS_PER_AREA"; "RkMap"; "alloc_meta"; "ameta"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "hd"; "last"; "existsb"; "incl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "loc"; "MCell"; "LCtx"; "loc_addr"; "LMem"; "VZ"; "image"; "sval"; "footprint"; "VP"; "sval_num"; "ctx_cells"; "mc_loc"; "optr"; "cell_holds"; "ly_ctx"; "ly_sec"; "Inv"; "area_cells"; "keys"; "user_blocks"; "CTX_SIZE"; "CTX_avail_meta_areas"; "CTX_seq"; "alloc_owned"; "mc_w"; "usedX"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_count"; "CTX_brk"; "CTX_free_meta_head"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "MT"; "VSec"; "ly_reg"; "mc_val"; "memb"; "region_of"; "yields"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "topL"; "mc_img_hi"; "mc_img_lo"; "addr_of"; "blocks"; "holds"; "mc_auxv"; "mc_chk_guard"; "mc_errno"; "mc_tp"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs"; "AM_P"; "v"; "AM_NEXT"; "Pre_am"; "O_brk"; "O_errno"; "O_sec"; "O_stk"; "M64"; "A78_res"; "LENX"; "frame_cells"; "A78_res_fail"; "Posts_am_P"; "AM_D"; "O_auxvp"; "O_got"; "O_guard"; "O_pgsz"; "O_ctxB"; "am_ctx";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E.InstX.C2E"; "bT"; "CHGF"; "UNCHF"; "valF"; "LF"; "ctxF"; "tailF"; "pageF"; "segF"; "OBJF"; "LF0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "layout_extends"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "Model"; "vm_reserved"; "VmMaps"; "with_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "canary_kept"; "maps_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78.InstX.Cut78r"; "UNCH_R"; "L78"; "lenZ"; "LRF"; "CHG_R"; "OKP"; "OBJ_R"; "OKPX"; "stkR_cells"; "O_brkD"; "O_ctx78"; "stk78_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E.InstX.C2E.FinalLeaf"; "mF"; "touched"; "rho'"; "rw'"; "SC13"; "fU"; "tailword"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "safe"; "etriple"; "guards"; "w_cfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I"; "rho1"; "D0"; "sp0"; "Kexact"; "zA"; "brkZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_R78.InstX.Cut78r.FailLeaf"; "mF"; "touched"; "rho'"; "rw'"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "firstn"; "skipn"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "instr"; "Ecall"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "agree_vals"; "sv_vars_all"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "add"; "le"; "ltb"; "of_nat"; "eqb"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM"; "L_am_ok"; "Posts_am"; "L_am_null"; "JL_am_ok"; "Pre_am"; "AM_D"; "JL_am_null"; "meta_obj0"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_place_ok_none"; "mmap_none_vm"; "mmap_nZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "liftK"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@Corelib.Init.Specif"; "sumbool"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_pc"; "ms_svc_pending"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsFuel"; "leaf"; "lf_state"; "mkLeaf"; "instr_at"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "rho_after_unmap"; "S_ret_lit"; "enomem_ret"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "mem_kept"; "ok_sideK"; "stack_win"; "top_high"; "V_RES"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_room"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow"; "gmeets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit"; "fully_covered"; "m'"; "obj_lits_ok";
"@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable"; "mmap_reserve_refusable"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric"; "meets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G2.Mal_ameta_C2E.InstX"; "brk_sval"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Refusable.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XLia.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_ameta_C2E.

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
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AreaZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf.

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
Sa5VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S146Sc2VX;VR;VU;Sf4Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§1§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§1§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation Hctx := (§1§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation optrZ := (@U.Mal_ameta__G1.Mal_ameta_I.optrZ L).
Local Abbreviation rho1 := (@U.Mal_ameta__G1.Mal_ameta_I.rho1 s L rho gd evb avb).
Local Notation "§2§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§2§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev173 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev185 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§2§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S8aQ40A1SfS8aQ8A1A1F_;Vrd0;SefS51VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S8aQ40A1SdF_;Vwok0;Sf0S51VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
Sc9Sc3Vrd0;S8aQ40A1S13L_;A2ScbSc2A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S16S135R1U4A2S3SfS8aQ8M0A1M1A1SefS51VmW;S8bQ40S57SccSc2A1S5bR2A1A2A2A3S14G1S122G1R2Vevb;S8bG0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S16S135R1U8A2S3SfS8aQ8M0A1M1A1SefS51VmW;S8bQ40S57ScaSc2A1S5bR2A1A2A2A3S14G1S122G1R2Vavb;S8bG0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51VmW;A2Sf0S51VmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§3§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§3§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S26Vrho;P18A2S8bG0ScdSc2A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (@U.Mal_ameta__G1.Mal_ameta_I.rng_stk s L rho gd evb avb Hgd Hev Hav mW).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S8aQ40A1SfS8aQ8A1A1F_;VmW;S27Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2aS51Vrho;S13cSfcA1ScSeSf6A1Sf1Vtr;Sf2Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S15cSf4Vs;VL;A2Vrho;A2").
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Ltac in_list := solve [ cbn; repeat first [ left; reflexivity | right ] ].

Ltac qlia := let QQ := fresh in pose proof I as QQ; clear - QQ; lia.

Definition brk_sval (u : astate) : sval := ltac2:(tb__ "0|0|
S68S9bLx;S6dVu;A1S99Z0A1S99N1A1S16S0S9dS6cR2S5dS6bR1A2A2A1Lp;Lr;X68x3").

Section C2E.

  Variables (Kc : list event -> Model -> Prop) (ok : world -> Prop) (md2 : Model) (vm2 : VmMaps).
  Hypothesis HOK : ltac2:(tb__ "0|0|
S15aS51Vok;VKc;A3").
  Hypothesis K2 : Kc tr md2.
  Hypothesis Evm2 : ltac2:(tb__ "0|0|
S3SfaSf7Vmd2;A1Vvm2;A3").
  Hypothesis STK : ltac2:(tb__ "0|3|
S4S56Z0S57S119Vrho;A1M0S118Vrho;A1M1A2M2A2S4S56Sc4VL;A1G2A2S4S56G0S5aZ2Z40A2A2S56G1S62SddA1A2A2A2A2").

  Hypothesis HFpre : ltac2:(tb__ "0|0|
S121S4eS4cVrho;A1S4fS13cSfcA1A1A3").

  Variables (t2 : astate) (L2 : layout) (pnew mnew : sptr) (pz V183 V184 V187 : Z) (ktr : list (kreq * Z)).
  Hypothesis HI2 : ltac2:(tb__ "0|0|
Sa5SbS64Vmnew;VX;A3VR;VU;Vt2;A4").
  Hypothesis HX2 : ltac2:(tb__ "0|0|
S167SbS64Vmnew;VX;A3Vt2;A2").
  Hypothesis HL2 : layout_ok L2 t2.
  Hypothesis HV2 : ltac2:(tb__ "0|0|
SceVL2;Vt2;Vvm2;A3").
  Hypothesis HLG2 : ledger_ok C_U vm2.
  Hypothesis HRES2 : ltac2:(tb__ "0|1|
S3SeS10S8aQ40A1M0G0A2A1Sf9Vvm2;A1Sf9Vvm;A1A3").
  Hypothesis HB2 : bounded t2.
  Hypothesis HMW2 : maps_wf vm2.
  Hypothesis HF : ltac2:(tb__ "0|4|
S4S3SeS64A1S67Vt2;A1S12S64S67Vs;A1SbS64Vpnew;S11S64A1A3A3A3S4S3SdS7cVt2;A1S13A3S4S3SfS64A1M0S6eVt2;A1S17S64A1A3S4S3S64S77Vt2;A1S65Vmnew;S73A2A3S4S3S0S7aVt2;A1S5cS81Z1M1A2A3S4S3S0S78Vt2;A1S5cVV183;G1A2A3S4S3S0S6fVt2;A1VV184;A3S4S3G0S6aVt2;A1G0G0Lx;S6aVs;A1S64S14S64R1A2Ls0;S14S64Vpnew;A2M2Xfx2A3S4S3G0S66Vt2;A1G2A3S4S3S64S79Vt2;A1S65Vpnew;Z1000A2A3S4S3SeG0A1S76Vt2;A1S76Vs;A1A3S4S3SeS0A1M3S7fVt2;A1S7fVs;A1A3S4S3G3S7eVt2;A1S7eVs;A1A3S4S3G3S7bVt2;A1S7bVs;A1A3S4S3S0S71Vt2;A1S71Vs;A1A3S3S0S70Vt2;A1S70Vs;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Hypothesis Hbrk2 : ltac2:(tb__ "0|0|
S3S0S9eVL2;S168Vt2;A1A2VV187;A3").
  Hypothesis HV183 : 1 <= V183 < 2 ^ 62.
  Hypothesis HV184 : 0 <= V184 < 2 ^ 62.
  Hypothesis HIMG2 : ltac2:(tb__ "0|1|
S93S8dS93R1S12S93S9aVt2;A1S137Vt2;A1A3A3S7S8dS93R2S9fVt2;A1A3S7S4S6S3SeS64A1S67Vs;A1M0S11S64A1A3A1S3S93R2S95S98S65S90S64G0S6cU0Z0A2A3Z8A2A1U8S9dVpnew;A1A3A3A2S7S8dS93R2Sa6Vt2;Vpnew;S17S64A1A3A3S4S8dS93R2S12S93S9aVs;A1S137Vs;A1A3A3S5S64S64S3S94Sa0R3A1S98R1A1A3Lq;A2A2A2A2A2F_;Fc;").
  Hypothesis HCTX2 : ltac2:(tb__ "0|1|
S93S8dS93R1S9fVt2;A1A3S7S5S0S0S5S16S16S5S9bS9bS4S3S93R5S95S96R3A1R2R1A3A3S4S135U0R2A2S7S4S56Z0R3A2S56S57R3S5bR2A1A2M0ZcA2A2S7S4S56Z10R3A2S56G0Z50A2A2S4S56Z398R3A2S56G0Z3a0A2A2A2A2A2A2Lval;A2Lw;A2Lo;A2S4S8dS93R2S9fVs;A1A3S6S3S94Sa0R2A1S96SaaA1A3A1A2A2F_;Fc;").
  Hypothesis HAC2 : ltac2:(tb__ "0|1|
S3SeS93A1Sa6Vt2;Vpnew;S17S64A1M0A3Sa6Vs;Vpnew;G0A3A3").
  Hypothesis HFRESH : ltac2:(tb__ "0|0|
S0S56Z0R1A2S3SfS75A1SbbVs;S65Vpnew;S57S72S5dS73R2A2A2A2A2S17S75A1A3F_;Fj;").
  Hypothesis HPN : ltac2:(tb__ "0|0|
S6S8dS64Vpnew;S67Vs;A1A3A1").
  Hypothesis Hmnew : ltac2:(tb__ "0|0|
S3S64Vmnew;S65Vpnew;Z18A2A3").
  Hypothesis HFP2 : ltac2:(tb__ "0|1|
S10S94S0A2M0S9S8dG0R1S9cVt2;A1A3S7S8dG0R1S9cVs;A1A3S3G0R1ScS94S0S98Vpnew;A1S6bA4A3A2A2Fe;").
  Hypothesis HUB2 : ltac2:(tb__ "0|0|
S3SeS10S64S0A2A1Sa8Vt2;A1Sa8Vs;A1A3").
  Hypothesis HLext : ltac2:(tb__ "0|0|
Sf5VL;VL2;S1bS69S7dVs;A1A2A3").
  Hypothesis HLctx : ltac2:(tb__ "0|0|
S3S0Sa3VL2;A1Sa3VL;A1A3").
  Hypothesis HLsec : ltac2:(tb__ "0|0|
S3S0Sa4VL2;A1Sa4VL;A1A3").
  Hypothesis HLfp : ltac2:(tb__ "0|2|
S10S94S0A2M0S8dG0R1S9cVs;A1A3S3S0S97VL2;S15S94S0R2A3M1A2S97VL;G1A2A3F_;Fe;").
  Hypothesis HLub : ltac2:(tb__ "0|2|
S10S64S0A2M0S8dG0R1Sa8Vs;A1A3S3S0S97VL2;S98S15S64S0R2A3A1M1A2S97VL;G1A2A3F_;Fb;").
  Hypothesis HLold : ltac2:(tb__ "0|0|
S64S135S85R1A1S1bS69S7dVs;A1A2A2S3S0Sc7VL2;R2A2Sc7VL;R2A2A3F_;Fq;").
  Hypothesis HPZ : ltac2:(tb__ "0|0|
S3S0S97VL2;S98Vpnew;A1A2Vpz;A3").
  Hypothesis Haddr : ltac2:(tb__ "0|0|
S3S0Sc7VL2;Vmnew;A2S57Vpz;S72A2A3").
  Hypothesis HpzR : ltac2:(tb__ "0|2|
S4S56Z1000M0Vpz;A2S4S56S57Vpz;G0A2Sc4VL;A1A2S4S3S0S5eVpz;G0A2Z0M1A3S4S56G1Vpz;A2S58Vpz;S5aZ2Z40A2A2A2A2A2A2").
  Hypothesis HCW2 : ltac2:(tb__ "0|3|
S93S0S8dS93R2S12S93S9aVt2;A1S137Vt2;A1A3A3S4S56S97VL2;Sa0R3A1A2M0R2A2S58R2S57G0S5bSadR3A1A1A2A2A2S7S5S10S94S0A2M1G1S4S8dG1R1S9cVs;A1A3S4S56S97VL;S15S94S0R1A3A2M2R4A2S58R4S57G2S18S94S0R1A3A2A2A2A2Le;A2S4S56Vpz;R3A2S58R3S57Vpz;Z1000A2A2A2A2F_;F_;Fx;Fc;").

  Variable GR : Z -> Prop.
  Hypothesis GRdec : ltac2:(tb__ "0|1|
S0S147VGR;R1A1M0S6G0A1A2Fx;").
  Hypothesis HGRpage : ltac2:(tb__ "0|0|
S0S4S56Vpz;R1A2S58R1S57Vpz;Z1000A2A2A2VGR;R2A1F_;Fx;").
  Hypothesis HGRimg : ltac2:(tb__ "0|0|
S0VGR;R1A1S6S4S56Sc6Sc2A1R2A2S58R2Sc5Sc2A1A2A2A1F_;Fx;").
  Hypothesis HGRfp : ltac2:(tb__ "0|2|
S10S94S0A2M0S0S8dG0R2S9cVs;A1A3S4S56S97VL;S15S94S0R3A3A2M1R2A2S58R2S57G1S18S94S0R3A3A2A2A2S6VGR;R3A1A1F_;F_;Fx;Fe;").
  Hypothesis HGRceil : ltac2:(tb__ "0|0|
S0VGR;R1A1S4S56Z1000R2A2S58R2Sc4VL;A1A2A2F_;Fx;").
  Hypothesis HGRmaps : ltac2:(tb__ "0|1|
S16S69S0S3SfS69A1Sc0Vs;R3A2S14S69R2A2A3S3SdS88R3A1S13A3S3S89S86R4A1S82A3S4S56SbdVL;R6A2M0R4A2S58R4S57G0S87R5A1A2A2A2S6VGR;R5A1A1F_;F_;F_;F_;Fx;Frg;Fk;").
  Hypothesis HGRblock : ltac2:(tb__ "0|0|
S0S0S0S8dS10S0S0A2ScS0S0R3R2A4Sc8VL;Vs;A2A3S4S56R4R2A2S58R2S57R4R3A2A2A2S6VGR;R3A1A1F_;F_;Fx;Fn;Fb;").

  Hypothesis HBW : ltac2:(tb__ "0|3|
S0S0S0S8dS10S0S0A2ScS0S0R3R2A4Sc8VL;Vs;A2A3S4S56R4R2A2S58R2S57R4R3A2A2A2S5S10S94S0A2M0G0S5S64S64S4S8dG0R2S9cVs;A1A3S4S3S94S15S94S0R2A3M1S98R1A1A3S4S56S97VL;G1A2M2R5A2S58R5S57G2S18S94S0R2A3A2A2A2A2A2Lp;A2Le;A2F_;F_;Fx;Fn;Fb;").
  Hypothesis HFPW : ltac2:(tb__ "0|3|
S10S94S0A2M0S0S8dG0R2S9cVs;A1A3S4S56S97VL;S15S94S0R3A3A2M1R2A2S58R2S57G1S18S94S0R3A3A2A2A2S7S4S3S94S15S94S0R4A3S96Z0A1A3S4S56Sa3VL;A1M2R3A2S58R3S57G2Sa9A2A2A2A2S5S64S64S4S3S94S15S94S0R5A3S98R1A1A3S4S4S56S6bR4A2S58R4Sc4VL;A1A2A2S6S4S56Sc6Sc2A1R4A2S58R4Sc5Sc2A1A2A2A1A2A2Lp;A2A2F_;F_;Fx;Fe;").

  Hypothesis HNOTX : ltac2:(tb__ "0|0|
S4S3SdSbfVmnew;VX;A2S19A3S8dS64Vmnew;Sa7Vt2;A1A3A2").
  Hypothesis HKEYS : ltac2:(tb__ "0|0|
S92S64Sa7Vs;A1Sa7Vt2;A1A3").
  Hypothesis HAMF : ltac2:(tb__ "0|0|
S4S166Vs;Vt2;A2S4S64S84S9SaeSbS64Vmnew;VX;A3Vt2;R2R1A4SaeVX;Vs;R2R1A4A2Fgm;Fg;S165Vs;Vt2;A2A2A2").
  Hypothesis HY : ltac2:(tb__ "0|1|
Sc1S10SfS64A1M0S74A2S83Vs;A1Vktr;ScG0S74S14S64Vmnew;A2Vt2;A4A4").

  Lemma Hpz8 : ltac2:(tb__ "0|0|
S3S0S5eS57Vpz;Z18A2Z8A2Z0A3").
  Proof using HV184 Hav Hev Hgd HpzR. pose proof HpzR as (_ & _ & M & _). Z.to_euclidean_division_equations; lia. Qed.
  Lemma ok_pframe_exact md' : ltac2:(tb__ "0|0|
VKc;Vtr;Vmd';A2S152S51Vok;S144S11aVtr;Vmd';A2A1A3F_;").
  Proof using HOK. intros HK. destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md' x8 HK Hp Ho). Qed.

    Definition segF (b : bool) : am_seg := if b then A2e4_next else A2e4_first.
    Definition LF0 (b : bool) : sstate := ltac2:(tb__ "0|1|
S14eS8fS14dS14fSd2S51ScfSecVb;A1M0A3S14cA2SdcG0A1A3A1").
    Definition LF_t : sstate := ltac:(let x := eval vm_compute in (LF0 true) in exact x).
    Definition LF_f : sstate := ltac:(let x := eval vm_compute in (LF0 false) in exact x).
    Definition LF (b : bool) : sstate := if b then LF_t else LF_f.
    Lemma LF_eq b : ltac2:(tb__ "0|0|
S3S2bSeeVb;A1Se8Vb;A1A3").
    Proof using . destruct b; [vm_cast_no_check (@eq_refl sstate LF_t) | vm_cast_no_check (@eq_refl sstate LF_f)]. Qed.
    Definition ctxF (b : bool) : sobj := ltac2:(tb__ "0|c|
S30S1fSe3ScfA1A1S1fZ18A1M0S1fZ58A1SdSeS20A1Lb;Vb;SbS20S21S1fZ28A1Z8M1S1fZ64A1A3M2SbS20S21S1fZ20A1G1S29S127S22Pc9A1M3S1fZ40A1M4A3A3M5SbS20S21S1fZ48A1G1G3A3M6SbS20S21S1fZ50A1G1S29S127G3S1fZ1000A1A3A3M7SbS20S21S1fZ30A1G1S29S127S22Pb7A1S1fN1A1A3A3M8SbS20S21G0G1S1fZ0A1A3M9SbS20S21S1fZ38A1G1S22Pb8A1A3MaSbS20S21G4G1S22Pb9A1A3S11S20A1MbA3A3A3A3A3A3A3A3SbS20G2SbS20G5SbS20G6SbS20S21G4G1G3A3SbS20G7SbS20G8SbS20G9SbS20GaGbA3A3A3A3A3A3A3A3Xdx2S2fA5").
    Definition pageF : sobj := ltac2:(tb__ "0|3|
S30S22Pc9A1S1fZ0A1M0S1fZ40A1SbS20S21S1fZ18A1Z8M1G0A3SbS20S21S1fZ20A1G1G0A3SbS20S21S1fZ10A1Z4M2S1fZ65A1A3SbS20S21G0G1Sd0PafA1A3SbS20S21S1fG1A1G1G0A3SbS20S21S1fZ14A1G2G0A3SbS20S21S1fZ28A1G1G0A3SbS20S21S1fZ30A1G2G0A3SbS20S21S1fZ34A1G2G0A3SbS20S21S1fZ38A1G1G0A3S11S20A1A3A3A3A3A3A3A3A3A3A3S2fA5").
    Definition pageF_lo : sobj := ltac2:(tb__ "0|3|
S30S22Pc9A1S1fZ0A1M0S1fZ18A1SbS20S21S1fZ10A1Z4M1S1fZ65A1A3SbS20S21G0Z8M2Sd0PafA1A3SbS20S21S1fG2A1G2G0A3SbS20S21S1fZ14A1G1G0A3S11S20A1A3A3A3A3S2fA5").
    Definition pageF_hi : sobj := ltac2:(tb__ "0|4|
S30S22Pc9A1S1fZ18A1M0S1fZ40A1SbS20S21G0Z8M1S1fZ0A1M2A3SbS20S21S1fZ20A1G1G2A3SbS20S21S1fZ28A1G1G2A3SbS20S21S1fZ30A1Z4M3G2A3SbS20S21S1fZ34A1G3G2A3SbS20S21S1fZ38A1G1G2A3S11S20A1A3A3A3A3A3A3S2fA5").
    Definition tailF : sobj := ltac2:(tb__ "0|2|
S30Sd0PbaA1S1fZ8M0A1M1S1fZ10A1SbS20S21G1G0S22Pc9A1A3S11S20A1A3S2fA5").

    Definition UNCHF : list sobj := ltac2:(tb__ "0|0|
SbS1eSdfScfA1SbS1eSe0SbS1eSdeScfA1SbS1eSe1ScfA1S11S1eA1A3A3A3A3").

    Definition CHGF (b : bool) : list sobj := ltac2:(tb__ "0|1|
S12S1eSbS1eSd4SbS1eSd5ScfSd0PafA1Z1A3SbS1eSe9Vb;A1SbS1eSd3ScfSd0PbbA1A2SbS1eSebS11S1eA1M0A3A3A3A3A3SdSeS1eA1Lb;Vb;SbS1eSeaG0A3G0Xdx2A3").
    Definition OBJF (b : bool) : list sobj := ltac2:(tb__ "0|1|
SbS1eSd6SdaA1S12S1eSe6S12S1eSbS1eSd4SbS1eSd5ScfSd0PafA1Z1A3SbS1eSe9Vb;A1SbS1eSd3ScfSd0PbbA1A2SbS1eSebS11S1eA1M0A3A3A3A3A3SdSeS1eA1Lb;Vb;SbS1eSeaG0A3G0Xdx2A3A3A3").
    Lemma LF_objs b : ltac2:(tb__ "0|0|
S3SeS1eA1S32Se8Vb;A1A1SedVb;A1A3").
    Proof using . destruct b; vm_compute; reflexivity. Qed.
    Lemma LF_misc b : ltac2:(tb__ "0|1|
S4S3S0S37Se8Vb;A1M0A1Z20ec8A3S4S3S1S36G0A1Sd1A3S4S3SeS23A1S48G0A1S55A3S4S3S46S47G0A1S33A3S4S3SfS23A1S49G0A1S17S23A1A3S3S23S28G0ZaA2S29S127S22Pc9A1S1fZ18A1A3A3A2A2A2A2A2").
    Proof using . destruct b; vm_compute; repeat split; reflexivity. Qed.
    Lemma LF_cs_chk b : ltac2:(tb__ "0|1|
S3SdS8eS0S0S1cS1dS53S59R1A1M0A1A1S50S28Se8Vb;A1R1A2S54G0A1A2A2Lz;S123S16S0S16S57Z1S5bR1A1A2Lk;S126U0U1fA2A4A3S13A3").
    Proof using . destruct b; vm_cast_no_check (@eq_refl bool true). Qed.
    Lemma LF_cs b : ltac2:(tb__ "0|0|
S0S4S56Z1R1A2S56R1Z1fA2A2S3SdS53S59R2A1A1S13A3S3S23S28Se8Vb;A1R3A2S54S59R3A1A1A3F_;F_;Fz;").
    Proof using HV184 Hav Hev Hgd pz.
      intros z Hz Hcs.
      pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv (LF b) z) (pre_reg (Z.to_nat z)))%bool 1 31 (LF_cs_chk b) z ltac:(lia)) as XX.
      cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
    Qed.
    Lemma OBJF_perm b o : ltac2:(tb__ "0|0|
S9S8dS1eVo;SedVb;A1A3S8dS1eVo;SbS1eSd6SdaA1S12S1eSe6Se5Vb;A1A3A3A3A2").
    Proof using . unfold OBJF, CHGF. split; intros H; exact H. Qed.
    Lemma OBJF_tail b o : ltac2:(tb__ "0|1|
S8dS1eVo;S12S1eSe6S12S1eSbS1eSd4SbS1eSd5ScfSd0PafA1Z1A3SbS1eSe9Vb;A1SbS1eSd3ScfSd0PbbA1A2SbS1eSebS11S1eA1M0A3A3A3A3A3SdSeS1eA1Lb;Vb;SbS1eSeaG0A3G0Xdx2A3A3A3S8dS1eVo;S12S1eSe6Se5Vb;A1A3A3F_;").
    Proof using . unfold CHGF. intros H; exact H. Qed.
    Lemma NXF b : ltac2:(tb__ "0|0|
S3S1S36Sd2S51ScfSecVb;A1A3A1Sd1A3").
    Proof using . destruct b; vm_compute; reflexivity. Qed.

    Definition valF (rhoX : valuation) : Prop := ltac2:(tb__ "0|4|
S4S1S12fR1PaaM0A2S3S8aQ40M1A1M2S26VrhoX;R2A2M3S26Vrho;R2A2A3F_;Fj;S4S1S8dS1R1SbS1G0SbS1PadSbS1PaeSbS1Pb0SbS1Pb9SbS1PbaS11S1A1A3A3A3A3A3A3A3S3G2G3S26S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R2A2A3F_;Fj;S4S3G2S26VrhoX;PafA2S8bG1Sa4VL;A1A2A3S4S3G2S26VrhoX;Pc9A2S8bG1Vpz;A2A3S4S3G2S26VrhoX;Pb7A2S8bG1VV183;A2A3S4S3G2S26VrhoX;Pb8A2S8bG1VV184;A2A3S4S3G2S26VrhoX;PbbA2S8bG1VV187;A2A3S1S3SeS8aQ8A1A1S35VrhoX;R1A2S35Vrho;R1A2A3Fl;A2A2A2A2A2A2A2").

    Lemma valF_ext rhoX rhoY : ltac2:(tb__ "0|0|
Se7VrhoX;A1S2dSd1VrhoX;VrhoY;A3Se7VrhoY;A1F_;F_;").
    Proof using HV184 Hav Hev Hgd.
      intros (F1 & F2 & F8 & F3 & F4 & F5 & F6 & F7) (B1 & B2 & B3). unfold AM_NEXT in B1.
      split; [intros j Hj; rewrite <- (B1 j) by lia; exact (F1 j Hj)|].
      split; [intros j Hj; rewrite <- (B1 j) by (cbn in Hj; repeat (destruct Hj as [<-|Hj]; [reflexivity|]); destruct Hj); exact (F2 j Hj)|].
      split; [rewrite <- (B1 175%positive) by reflexivity; exact F8|].
      split; [rewrite <- (B1 201%positive) by reflexivity; exact F3|].
      split; [rewrite <- (B1 183%positive) by reflexivity; exact F4|].
      split; [rewrite <- (B1 184%positive) by reflexivity; exact F5|].
      split; [rewrite <- (B1 187%positive) by reflexivity; exact F6|].
      intros l. rewrite <- B2. exact (F7 l).
    Qed.

    Lemma evF_low rhoX e : ltac2:(tb__ "0|0|
Se7VrhoX;A1S3SdS12eS1S132R1PaaA2Lj;Ve;A2S13A3S3S8aQ40A1S24VrhoX;Ve;A2S24S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Ve;A2A3F_;F_;").
    Proof using Hav Hev Hgd.
      intros (F1 & _ & _ & _ & _ & _ & _ & F7) Hb. apply (eval_agree_vars (fun j => (j <? 170)%positive) rhoX (rho1 mW)); [| |exact Hb].
      - intros j Hj. apply Pos.ltb_lt in Hj. rewrite (F1 j Hj). cbn [rho1 rw]. symmetry. apply rw1_low. exact Hj.
      - intros l. rewrite (F7 l). reflexivity.
    Qed.
    Lemma evF_F2 rhoX j : ltac2:(tb__ "0|1|
Se7VrhoX;A1S8dS1Vj;SbS1PaaSbS1PadSbS1PaeSbS1Pb0SbS1Pb9SbS1PbaS11S1A1A3A3A3A3A3A3A3S3S8aQ40A1S24VrhoX;Sd0Vj;A1M0A2S24S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7G0A2A3F_;F_;").
    Proof using . intros (_ & F2 & _) Hj. cbn [eval v]. exact (F2 j Hj). Qed.
    Lemma evF_175 rhoX : ltac2:(tb__ "0|1|
Se7VrhoX;A1S3S8aQ40M0A1S24VrhoX;Sd0PafA1A2S8bG0Sa4VL;A1A2A3F_;").
    Proof using . intros (_ & _ & F8 & _). cbn [eval v]. exact F8. Qed.
    Lemma evF_201 rhoX : ltac2:(tb__ "0|1|
Se7VrhoX;A1S3S8aQ40M0A1S24VrhoX;S22Pc9A1A2S8bG0Vpz;A2A3F_;").
    Proof using . intros (_ & _ & _ & F3 & _). cbn [eval]. exact F3. Qed.
    Lemma U201 : ltac2:(tb__ "0|1|
S3S0S8cQ40M0S8bG0Vpz;A2A2Vpz;A3").
    Proof using HpzR. pose proof HpzR as (P1 & P2 & P3 & P4). apply u64. exact P4. Qed.
    Lemma evF_201o rhoX d : ltac2:(tb__ "0|1|
Se7VrhoX;A1S4S56Z0Vd;A2S58Vd;S5aZ2Z20A2A2A2S3S8aQ40M0A1S24VrhoX;S29S127S22Pc9A1S1fVd;A1A3A2S8bG0S57Vpz;Vd;A2A2A3F_;F_;").
    Proof using HV184 Hav Hev Hgd HpzR.
      intros VX Hd. pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges.
      pose proof (evF_201 rhoX VX) as E201. cbn [eval] in E201 |- *. rewrite E201. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite U201, (u64 d) by lia. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?q) with (q mod bv_modulus 64). change (bv_modulus 64) with (2 ^ 64). reflexivity.
    Qed.
    Lemma evF_183m1 rhoX : ltac2:(tb__ "0|1|
Se7VrhoX;A1S3S8aQ40M0A1S24VrhoX;S29S127S22Pb7A1S1fN1A1A3A2S8bG0S5cVV183;Z1A2A2A3F_;").
    Proof using HV183 HV184 Hav Hev Hgd.
      intros (_ & _ & _ & _ & F4 & _). pose proof HV183 as RR.
      cbn [eval]. rewrite F4. unfold alu64, alu. apply bv_eq. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (u64 V183) by lia. rewrite !Z_to_bv_unsigned. change (bv_wrap 64 ?q) with (q mod bv_modulus 64). change (bv_modulus 64) with (2 ^ 64).
      change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
      replace (V183 + (2 ^ 64 - 1)) with ((V183 - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
    Qed.
    Lemma evF_184 rhoX : ltac2:(tb__ "0|1|
Se7VrhoX;A1S3S8aQ40M0A1S24VrhoX;S22Pb8A1A2S8bG0VV184;A2A3F_;").
    Proof using . intros (_ & _ & _ & _ & _ & F5 & _). cbn [eval]. exact F5. Qed.
    Lemma evF_187 rhoX : ltac2:(tb__ "0|1|
Se7VrhoX;A1S3S8aQ40M0A1S24VrhoX;Sd0PbbA1A2S8bG0VV187;A2A3F_;").
    Proof using . intros (_ & _ & _ & _ & _ & _ & F6 & _). cbn [eval v]. exact F6. Qed.
    Definition bT : bool := ltac2:(tb__ "0|0|
SfS64A1SdLx;S66Vs;A1S64S13Ls0;S19Xfx2").

    Lemma tail_cell_image T : ltac2:(tb__ "0|0|
S3SfS64A1S66Vs;A1S14S64VT;A2A3S8dS93S95S98S65VT;Z8A2A1U8Sa1S17S64A1A1A3S9aVs;A1A3F_;").
    Proof using HF HI HIMG2 HPN.
      intros HT. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _). rewrite HT in Etail.
      assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
      assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
      unfold image. apply in_app_iff. right. apply in_app_iff. left.
      rewrite ET. clear - Hne. induction (st_areas s) as [|a0 t0 IH]; [exfalso; exact (Hne eq_refl)|].
      cbn [areas_cells last]. destruct t0 as [|b0 t'].
      - apply in_app_iff. left. unfold area_cells. apply in_app_iff. left. cbn. right. left. reflexivity.
      - apply in_app_iff. right. apply IH. discriminate.
    Qed.

    Section FinalLeaf.
      Variables (msF : machine_state) (rhoF : valuation).
      Hypothesis VF : valF rhoF.
      Hypothesis MF : ltac2:(tb__ "0|1|
S8aQ40M0A1S6VGR;S8cG0R1A2A1A1S3SfS8aQ8A1A1S27VrhoF;R2A2VmW;R2A1A3F_;Fx;").
      Hypothesis ZF : ltac2:(tb__ "0|4|
S8aQ40M0A1S4S56Vpz;S8cG0R1A2M1A2S58G1S57Vpz;Z1000A2A2A2S3SfS8aQ8M2A1M3A1S27VrhoF;R2A2S14G3S8bG2Z0A2A2A3F_;Fx;").
      Hypothesis HsmF : ltac2:(tb__ "0|0|
S2aS51VrhoF;Se8Se4A1ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd2;A2A4A4").

      Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
      Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
      Lemma HOF : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3SedSe4A1A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. rewrite LF_objs in Hall. exact Hall. Qed.
      Lemma HfrF : ltac2:(tb__ "0|0|
S8aQ40A1S43VrhoF;SedSe4A1R1A3S3SfS8aQ8A1A1S149VmsF;R2A2S27VrhoF;R2A2A3F_;Fx;").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. rewrite LF_objs in Hfr. exact Hfr. Qed.
      Lemma F_pc : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S14aVmsF;A1S8bG0Z20ec8A2A3").
      Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct (LF_misc bT) as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
      Lemma F_pend : ltac2:(tb__ "0|1|
S3SfS8aQ40A1M0A1S14bVmsF;A1S17G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
      Lemma F_halt : model_idle md2. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
      Lemma F_regs : ltac2:(tb__ "0|0|
S44VrhoF;Se8Se4A1VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
      Lemma F_fregs : ltac2:(tb__ "0|0|
S3eVrhoF;Se8Se4A1VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
      Lemma F_fcsr : ltac2:(tb__ "0|0|
S3cVrhoF;S33VmsF;A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct (LF_misc bT) as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
      Lemma F_resv : ltac2:(tb__ "0|0|
S45VrhoF;S17S23A1VmsF;A3").
      Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct (LF_misc bT) as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

      Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S161VrhoF;VmsF;Se6Se5Se4A1A4").

      Definition fU (j : positive) : bool := ltac2:(tb__ "0|1|
S1cS132Vj;PaaM0A2S91S1S134Vj;A1SbS1G0SbS1PadSbS1PaeSbS1Pb0SbS1Pb9SbS1PbaS11S1A1A3A3A3A3A3A3A3A2").
      Lemma fU_agree j : ltac2:(tb__ "0|0|
S3SdS110Vj;A1S13A3S3S8aQ40A1S26S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Vj;A2S26VrhoF;Vj;A2A3F_;").
      Proof using HAMF HF HNOTX HV183 HV184 Hav Hev Hgd HpzR STK VF.
        intros Hj. unfold fU in Hj. apply Bool.orb_true_iff in Hj as [Hj|Hj].
        - apply Pos.ltb_lt in Hj. pose proof VF as (F1 & _). rewrite (F1 j Hj). cbn [rho1 rw]. apply rw1_low. exact Hj.
        - apply existsb_exists in Hj as (y & Hy & E). apply Pos.eqb_eq in E. subst y.
          cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
            match goal with |- rw _ ?jj = _ => symmetry; exact (proj1 (proj2 VF) jj ltac:(cbn; tauto)) end.
      Qed.
      Lemma KU_entry' : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;S151Vms;VmW;A2A3Se6A3").
      Proof using Erd Ewok HAMF HF HMI HNOTX HV183 HV184 Hav Hav_rd Hev Hgd Hgd_rd HpzR Hrom STK VF.
        unfold UNCHF.
        assert (AG : forall o, obj_vars_all fU o = true -> obj_holds segsU (rho1 mW) (with_mem ms mW) o -> obj_holds segsU rhoF (with_mem ms mW) o).
        { intros o Hv Ho. apply (obj_holds_agree_vars segsU fU (rho1 mW) rhoF (with_mem ms mW) o fU_agree); [|exact Hv|exact Ho].
          intros l. pose proof VF as (_ & _ & _ & _ & _ & _ & _ & F7). rewrite (F7 l). reflexivity. }
        repeat (constructor; [apply AG; [vm_compute; reflexivity|]|]);
          [apply hold_got | apply hold_guard | apply hold_auxvp | apply hold_pgsz | constructor].
      Qed.
      Lemma KU_leaf : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3Se6A3").
      Proof using HsmF. apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). apply OBJF_perm. right. apply in_app_iff. left. exact Ho. Qed.
      Lemma KC_leaf : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3Se5Se4A1A3").
      Proof using HsmF. apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) HOF). apply OBJF_perm. right. apply in_app_iff. right. exact Ho. Qed.
      Lemma Kcov : ltac2:(tb__ "0|0|
S3SdS8eS1eS160Se6A3S13A3"). Proof using . vm_compute. reflexivity. Qed.
      Lemma Klits : ltac2:(tb__ "0|0|
S3SdS8eS1eS162S12S1eSe6Se5Se4A1A3A3S13A3"). Proof using . unfold bT. destruct (st_area_tail s); vm_compute; reflexivity. Qed.
      Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdS8eS1eS1eS34SdLx;S41R1A1S13S19S19S1S19Ll;M0G0S0S23SeS10S0S0A2A1SeS4aA1S19Ltmpl;Lflds;Lcnt;Lesz;X34x6Lo;S12S1eSe6Se5Se4A1A3A3S13A3"). Proof using . unfold bT. destruct (st_area_tail s); reflexivity. Qed.
      Lemma Kvars : ltac2:(tb__ "0|0|
S3SdS8eS1eS42Sd1A1S12S1eSe6Se5Se4A1A3A3S13A3"). Proof using . unfold bT. destruct (st_area_tail s); vm_compute; reflexivity. Qed.
      Lemma HagFF : ltac2:(tb__ "0|0|
S2dSd1VrhoF;VrhoF;A3"). Proof using . split; [|split]; intros; reflexivity. Qed.

      Lemma KIT_unch : ltac2:(tb__ "0|2|
S1eS0S8dS1eR2Se6A3S4S56S15S0S0S25VrhoF;R3A2M0A3R2A2S58R2S18S0S0G0A3A2A2S4S3SfS8aQ8A1A1SefS51S10bS8bQ40R3A2M1A3SefS51VmW;G1A3A3S3SdSf0S51S10bG1A3Sf0S51VmW;G1A3A3A2F_;F_;Fx;Fo;").
      Proof using Erd Ewok HAMF HF HMI HNOTX HV183 HV184 Hav Hav_rd Hev Hgd Hgd_rd HpzR Hrom HsmF STK VF. exact (ReabKit.unch_same segsU rhoF rhoF ms msF mW Hrom HromF UNCHF (CHGF bT) KU_entry' KU_leaf AM_NEXT HagFF Kvars Kcov Klits Kdunk). Qed.
      Lemma KIT_chgb : ltac2:(tb__ "0|3|
S1eS0S8dS1eR2Se5Se4A1A3S4S56S15S0S0S25VrhoF;R3A2M0A3R2A2S58R2S18S0S0G0A3A2A2S4S3SdSf0S51S10bS8bQ40M1R3A2A3S13A3S5S8aQ8A1M2G2S3SfG2A1SefS51S10bS8bG1R4A2A3S14G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
      Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCHF (CHGF bT) KC_leaf Kdunk). Qed.
      Lemma KIT_chgc : ltac2:(tb__ "0|3|
S1eS20S16S8dS1eR3Se5Se4A1A3S8dS20R3S39R4A1A3S135R3S59S38R4A1A1A2S3SfS8aQ8M0A1M1A1SefS51S10bS8bQ40M2S57S57S8cG2S24VrhoF;S40R6A1A2A2S31VrhoF;S3aR5A1A2A2S5bR4A1A2A2A3S14G1S122G1R4S4bS59S38R5A1A1S24VrhoF;S3bR5A1A2A2S8bG0Z0A2A4A2A3F_;F_;F_;Fj;Fc;Fo;").
      Proof using HsmF. exact (ReabKit.chg_cell segsU rhoF rhoF msF HromF UNCHF (CHGF bT) KC_leaf AM_NEXT HagFF Kvars). Qed.

      Definition tailword (x : Z) : Prop := ltac2:(tb__ "0|1|
SfS64A1OLx;S66Vs;A1S64S4S56S57S11bVL;R1A2M0Z8A2Vx;A2S58Vx;S57G0Z10A2A2A2LT;SaXfx2").
      Definition touched (x : Z) : Prop := ltac2:(tb__ "0|0|
S7S7S4S56Z3a02cVx;A2S58Vx;Z3a030A2A2S7S4S56Z5a3d0Vx;A2S58Vx;Z5a3dcA2A2S7S4S56Z5a3e0Vx;A2S58Vx;Z5a420A2A2S4S56Z5a768Vx;A2S58Vx;Z5a770A2A2A2A2A2S7VGR;Vx;A1S111Vx;A1A2A2").
      Lemma touched_dec x : ltac2:(tb__ "0|1|
S147S10cVx;A1M0S6G0A1A2").
      Proof using GRdec HAMF HF HNOTX HV183 HV184 Hgd HpzR STK.
        unfold touched, tailword. apply or_dec; [apply or_dec; [apply range_dec | apply or_dec; [apply range_dec | apply or_dec; apply range_dec]]|]. apply or_dec; [apply GRdec|].
        destruct (st_area_tail s); [apply range_dec | right; tauto].
      Qed.
      Lemma evF_lit z : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S24VrhoF;S1fVz;A1A2S8bG0Vz;A2A3"). Proof using . reflexivity. Qed.
      Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.

      Lemma tail_facts T : ltac2:(tb__ "0|4|
S3SfS64A1M0S66Vs;A1S14S64VT;A2A3S4S8dS64VT;S67Vs;A1M1A3S4S3S64VT;S90S64G1S6cU0Z0A2A3A3S4S6S3SeS64A1G1S11S64A1A3A1S4S56Z1000M2S11bVL;VT;A2M3A2S4S56S57G3G2A2Sc4VL;A1A2S4S3S0S8cQ40S24VrhoF;Sd0PbaA1A2A2G3A3S5S64S64S3G0S6aVs;A1S14S64R1A2A3Lh;A2A2A2A2A2A2A2F_;").
      Proof using HAMF HF HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR STK VF.
        intros HT. pose proof (inv_areas HI) as (_ & _ & Ehead & Etail & _). rewrite HT in Etail.
        assert (Hne : st_areas s <> []) by (intros E; rewrite E in Etail; discriminate).
        assert (ET : T = last (st_areas s) (SP 0%nat 0)) by (destruct (st_areas s); [exfalso; exact (Hne eq_refl) | injection Etail as E; exact E]).
        assert (HinT : In T (st_areas s)) by (rewrite ET; apply MallocLemmasRing.In_last; exact Hne).
        pose proof (area_R T HinT) as (RT1 & RT2 & _). top_ranges.
        split; [exact HinT|]. split; [exact ET|]. split; [exact Hne|]. split; [exact RT1|]. split; [exact RT2|]. split.
        - rewrite (evF_F2 rhoF 186 VF) by (cbn; tauto). rewrite ev186, HT. cbn [optrZ]. apply u64. lia.
        - destruct (st_areas s) as [|a0 l]; [exfalso; exact (Hne eq_refl)|]. exists a0. exact Ehead.
      Qed.
      Lemma notail_facts : ltac2:(tb__ "0|2|
S3SfS64A1M0S66Vs;A1S17S64A1M1A3S4S3SeS64A1S67Vs;A1S11S64A1A3S3G0S6aVs;A1G1A3A2F_;").
      Proof using HF HI HIMG2 HPN.
        intros HT. pose proof (inv_areas HI) as (_ & _ & Ehead & Etail & _). rewrite HT in Etail.
        destruct (st_areas s) as [|a0 l]; [split; [reflexivity | exact Ehead] | discriminate].
      Qed.

      Lemma rng_errF : ltac2:(tb__ "0|0|
S3S10S0S0A2S25VrhoF;Sd4A2ScS0S0Z3a02cZ3a030A4A3").
      Proof using HV184 Hav Hev Hgd Htp VF. unfold obj_range, obj_lo_of, obj_hi_of, O_errno. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite (evF_low rhoF (SVar 24) VF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity. Qed.
      Lemma rng_secF : ltac2:(tb__ "0|0|
S3S10S0S0A2S25VrhoF;Sd5ScfSd0PafA1Z1A3A2ScS0S0Z5a3d0Z5a3dcA4A3").
      Proof using HV184 Hav Hev Hgd pz. unfold obj_range, obj_lo_of, obj_hi_of, O_sec. cbn [ob_base ob_lo ob_hi am_ctx AM_P]. rewrite !evF_lit, !soff_lit_small by lia. rewrite u64 by lia. reflexivity. Qed.
      Lemma rng_brkF : ltac2:(tb__ "0|0|
S3S10S0S0A2S25VrhoF;Sd3ScfSd0PbbA1A2A2ScS0S0Z5a768Z5a770A4A3").
      Proof using HV184 Hav Hev Hgd pz. unfold obj_range, obj_lo_of, obj_hi_of, O_brk. cbn [ob_base ob_lo ob_hi am_ctx AM_P]. rewrite !evF_lit, !soff_lit_small by lia. rewrite u64 by lia. reflexivity. Qed.
      Lemma rng_ctxF : ltac2:(tb__ "0|0|
S3S10S0S0A2S25VrhoF;Se9Se4A1A2ScS0S0Z5a3e0Z5a420A4A3").
      Proof using HV184 Hav Hev Hgd pz. unfold obj_range, obj_lo_of, obj_hi_of, ctxF. cbn [ob_base ob_lo ob_hi am_ctx AM_P]. rewrite !evF_lit, !soff_lit_small by lia. rewrite u64 by lia. reflexivity. Qed.
      Lemma rng_pageF : ltac2:(tb__ "0|0|
S3S10S0S0A2S25VrhoF;SebA2ScS0S0Vpz;S57Vpz;Z40A2A4A3").
      Proof using HV184 Hav Hev Hgd HpzR VF. unfold obj_range, obj_lo_of, obj_hi_of, pageF. cbn [ob_base ob_lo ob_hi]. rewrite (evF_201 rhoF VF), !soff_lit_small by lia. rewrite U201. f_equal. lia. Qed.
      Lemma rng_tailF T : ltac2:(tb__ "0|1|
S3SfS64A1S66Vs;A1S14S64VT;A2A3S3S10S0S0A2S25VrhoF;SeaA2ScS0S0S57S11bVL;VT;A2M0Z8A2S57G0Z10A2A4A3F_;").
      Proof using HAMF HF HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR STK VF. intros HT. pose proof (tail_facts T HT) as (_ & _ & _ & _ & _ & E & _). unfold obj_range, obj_lo_of, obj_hi_of, tailF. cbn [ob_base ob_lo ob_hi]. rewrite E, !soff_lit_small by lia. reflexivity. Qed.
      Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3SeS10S0S0A2M0A1S123S1eG0S25VrhoF;A1Se6A4SbG0ScS0S0Z28d50Z28d58A4SbG0ScS0S0Z5a338Z5a340A4SbG0ScS0S0Z5a360Z5a368A4SbG0ScS0S0Z5a388Z5a390A4S11G0A1A3A3A3A3A3").
      Proof using HAMF HF HNOTX HV183 HV184 Hav Hev Hgd HpzR STK VF.
        cbn [map UNCHF]. unfold O_got, O_guard, O_auxvp, O_pgsz. cbn [am_got am_libc am_ctx AM_P].
        unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
        rewrite (evF_F2 rhoF 173 VF) by (cbn; tauto). rewrite ev173. rewrite !u64 by (cbn; lia). reflexivity.
      Qed.
      Lemma CHG_in o : ltac2:(tb__ "0|0|
S8dS1eVo;Se5Se4A1A3S7S3S1eVo;Sd4A3S7S3S1eVo;Sd5ScfSd0PafA1Z1A3A3S7S3S1eVo;Se9Se4A1A3S7S3S1eVo;Sd3ScfSd0PbbA1A2A3S7S3S1eVo;SebA3S4S3S1eVo;SeaA3S5S64S64S3SfS64A1S66Vs;A1S14S64R1A2A3LT;A2A2A2A2A2A2A2F_;").
      Proof using .
        unfold CHGF, bT. destruct (st_area_tail s) as [T|]; cbn [app In]; intros Ho.
        - destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; [left | right; left | right; right; left | right; right; right; left | do 4 right; left | do 5 right; split; [|exists T]]; reflexivity.
        - destruct Ho as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [left | right; left | right; right; left | right; right; right; left | do 4 right; left]; reflexivity.
      Qed.
      Lemma CHG_touched o x : ltac2:(tb__ "0|1|
S8dS1eVo;Se5Se4A1A3S4S56S15S0S0S25VrhoF;Vo;A2M0A3Vx;A2S58Vx;S18S0S0G0A3A2A2S10cVx;A1F_;F_;").
      Proof using HAMF HF HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp STK VF.
        intros Ho RR. unfold touched, tailword.
        destruct (CHG_in o Ho) as [->|[->|[->|[->|[->|[-> [T HT]]]]]]].
        - rewrite rng_errF in RR. cbn [fst snd] in RR. lia.
        - rewrite rng_secF in RR. cbn [fst snd] in RR. lia.
        - rewrite rng_ctxF in RR. cbn [fst snd] in RR. lia.
        - rewrite rng_brkF in RR. cbn [fst snd] in RR. lia.
        - rewrite rng_pageF in RR. cbn [fst snd] in RR. right; left. apply HGRpage. lia.
        - rewrite (rng_tailF T HT) in RR. rewrite HT. cbn [fst snd] in RR. lia.
      Qed.
      Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S56Z0Vx;A2S58Vx;S5aZ2Z40A2A2A2S153VrhoF;S12S1eSe6Se5Se4A1A3S8bQ40Vx;A2A3S7S5S1eS1eS4S8dS1eR1Se6A3S4S56S15S0S0S25VrhoF;R1A2M0A3Vx;A2S58Vx;S18S0S0G0A3A2A2A2Lo;A2S10cVx;A1A2F_;F_;").
      Proof using HAMF HF HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp STK VF.
        intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
        exact (CHG_touched o x Ho RR).
      Qed.

      Lemma touched_in x : ltac2:(tb__ "0|1|
S10cVx;A1S7S5S1eS1eS4S8dS1eR1Se5Se4A1A3S4S56S15S0S0S25VrhoF;R1A2M0A3Vx;A2S58Vx;S18S0S0G0A3A2A2A2Lo;A2S4VGR;Vx;A1S6S4S56Vpz;Vx;A2S58Vx;S57Vpz;Z40A2A2A2A1A2A2F_;").
      Proof using HAMF HF HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp STK VF.
        intros T. unfold touched, tailword in T.
        destruct T as [[T|[T|[T|T]]]|[T|T]].
        - left. exists O_errno. split; [unfold CHGF; apply in_app_iff; left; cbn; tauto|]. rewrite rng_errF. cbn [fst snd]. lia.
        - left. exists (O_sec AM_P (v 175) 1). split; [unfold CHGF; apply in_app_iff; left; cbn; tauto|]. rewrite rng_secF. cbn [fst snd]. lia.
        - left. exists (ctxF bT). split; [unfold CHGF; apply in_app_iff; left; cbn; tauto|]. rewrite rng_ctxF. cbn [fst snd]. lia.
        - left. exists (O_brk AM_P (v 187)). split; [unfold CHGF; apply in_app_iff; left; cbn; tauto|]. rewrite rng_brkF. cbn [fst snd]. lia.
        - destruct (range_dec (pz) (pz + 64) x) as [IN|OUT].
          + left. exists pageF. split; [unfold CHGF; apply in_app_iff; left; cbn; tauto|]. rewrite rng_pageF. cbn [fst snd]. lia.
          + right. split; [exact T | exact OUT].
        - destruct (st_area_tail s) as [T0|] eqn:HT; [|destruct T].
          left. exists tailF. split; [unfold CHGF, bT; rewrite HT; apply in_app_iff; right; left; reflexivity|]. rewrite (rng_tailF T0 HT). cbn [fst snd]. lia.
      Qed.

      Let bv1 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51S10bA2Sf0S51S10bA2A2").
      Let rv1 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51S10bA2S8aQ40A1S13L_;A2").
      Let rv0 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51VmW;A2S8aQ40A1S13L_;A2").

      Theorem V1 : ltac2:(tb__ "0|1|
S0S4S56Z0R1A2S58R1S5aZ2Z40A2A2A2S6S10cR2A1A1S4S3SfS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
      Proof using Erd Ewok HAMF HF HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hav_rd Hev Hgd Hgd_rd HpzR Hrom HsmF Htp MF STK VF.
        intros x Hx NT.
        assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
        { destruct (in_ranges_dec rhoF (UNCHF ++ CHGF bT) (Z_to_bv 64 x)) as [IN|OUT].
          - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
          - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCHF (CHGF bT) _ OUT).
            rewrite (MF (Z_to_bv 64 x)) by (rewrite u64 by lia; intros G; apply NT; right; left; exact G). auto. }
        destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
      Qed.

      Lemma page_zero x : ltac2:(tb__ "0|0|
S4S56S57Vpz;Z40A2Vx;A2S58Vx;S57Vpz;Z1000A2A2A2S3SfS0A1Vbv1;Vx;A1S14S0Z0A2A3F_;").
      Proof using HAMF HF HGRfp HGRimg HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp STK VF ZF msF.
        intros Hx. pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges.
        assert (R64 : 0 <= x < 2 ^ 64) by lia.
        destruct (in_ranges_dec rhoF (UNCHF ++ CHGF bT) (Z_to_bv 64 x)) as [IN|OUT].
        - exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho].
          + pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite UNCH_rangesF in M.
            pose proof (HGRimg x (HGRpage x ltac:(lia))) as GI. cbn [mc_img_lo mc_img_hi C_U] in GI.
            cbn in M. destruct M as [E|[E|[E|[E|[]]]]]; rewrite <- E in RR; cbn [fst snd] in RR; apply GI; lia.
          + pose proof (HGRimg x (HGRpage x ltac:(lia))) as GI. cbn [mc_img_lo mc_img_hi C_U] in GI.
            destruct (CHG_in o Ho) as [->|[->|[->|[->|[->|[-> [T HT]]]]]]].
            * rewrite rng_errF in RR. cbn [fst snd] in RR. apply GI; lia.
            * rewrite rng_secF in RR. cbn [fst snd] in RR. apply GI; lia.
            * rewrite rng_ctxF in RR. cbn [fst snd] in RR. apply GI; lia.
            * rewrite rng_brkF in RR. cbn [fst snd] in RR. apply GI; lia.
            * rewrite rng_pageF in RR. cbn [fst snd] in RR. lia.
            * rewrite (rng_tailF T HT) in RR. cbn [fst snd] in RR. pose proof (tail_facts T HT) as (HinT & _).
              refine (HGRfp (LMem T, PGSZ) x (e_area_In s T HinT) _ (HGRpage x ltac:(lia))). cbn [fst snd]. unfold zA, addr_of, PGSZ in *. lia.
        - unfold bv1, byteview_of.
          replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          unfold mF, Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCHF (CHGF bT) _ OUT). rewrite (ZF (Z_to_bv 64 x)) by (rewrite u64 by lia; lia).
          reflexivity.
      Qed.

      Theorem VM : ltac2:(tb__ "0|0|
S0S4S56Z0R1A2S58R1S5aZ2Z40A2A2A2S10cR2A1SacVL2;Vt2;R3A3S6S3SfS0A1Vbv1;R4A1S17S0A1A3A1F_;F_;F_;Fx;").
      Proof using HAMF HF HFP2 HGRfp HGRimg HGRpage HI HIMG2 HLfp HMI HNOTX HPN HPZ HV183 HV184 Hav Hev Hgd HpzR HsmF Htp STK VF ZF.
        intros x Hx T [(e & He & Rx) _].
        destruct (touched_in x T) as [(o & Ho & RR)|[G NP]].
        - destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
          unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. rewrite W, Hb. discriminate.
        -
          apply HFP2 in He as [He| ->].
          + exfalso. rewrite (HLfp e He) in Rx. exact (HGRfp e x He Rx G).
          + cbn [fst snd] in Rx. rewrite HPZ in Rx. rewrite (page_zero x) by (unfold PGSZ in Rx; lia). discriminate.
      Qed.

      Lemma leaf_cell (oF : sobj) (cF : cell) (lc : loc) (w : nat) (val : sval) (z : Z) : ltac2:(tb__ "0|4|
S8dS1eVoF;Se5Se4A1A3S8dS20VcF;S39VoF;A1A3S3S0S38VcF;A1S5bVw;A1M0A3S136Vw;U8A2S9bOLval;Vval;S0S8Lz0;S64S8Lp;S0SaLz0;S8X9bx4S3S0S9eVL2;Vval;A2Vz;A3S3S0S57S8cQ40M1S24VrhoF;S40VoF;A1A2A2S31VrhoF;S3aVcF;A1A2A2S97VL2;Vlc;A2M2A3S4S56S15S0S0S25VrhoF;VoF;A2M3A3G2A2S56S57G2G0A2S18S0S0G3A3A2A2S3S8aG1A1S24VrhoF;S3bVcF;A1A2S8bG1Vz;A2A3Sa2VL2;Vbv1;S95Vlc;Vw;Vval;A3A3F_;F_;F_;F_;F_;F_;F_;F_;F_;").
      Proof using HV184 Hav Hev Hgd HpzR HsmF.
        intros HoF HcF Hw Hw8 Hval Hz Hca Hrng Hevl. subst z.
        unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w].
        assert (BYTE : forall k, (k < w)%nat -> bv1 (loc_addr L2 lc + Z.of_nat k) = Some (le_byte (sval_num L2 val) w k)).
        { intros k Hk.
          pose proof (KIT_chgc oF cF k HoF HcF ltac:(rewrite Hw, Nat2Z.id; exact Hk)) as RD. rewrite Hca, Hw, Nat2Z.id, Hevl in RD.
          rewrite nth_enc_bytes in RD by assumption.
          destruct (KIT_chgb oF (loc_addr L2 lc + Z.of_nat k) HoF ltac:(lia)) as [W _].
          unfold bv1, byteview_of.
          assert (R64 : 0 <= loc_addr L2 lc + Z.of_nat k < 2 ^ 64).
          { pose proof (proj1 (Forall_forall _ _) KC_leaf oF HoF) as ((R0 & R1 & _) & _). unfold obj_range, obj_lo_of, obj_hi_of in Hrng, R0, R1. cbn [fst snd] in Hrng. lia. }
          replace ((0 <=? loc_addr L2 lc + Z.of_nat k) && (loc_addr L2 lc + Z.of_nat k <? 2 ^ 64))%bool with true
            by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          cbn [andb]. rewrite W, RD. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
          change (bv_modulus 8%N) with 256. unfold le_byte. apply Z.mod_pos_bound. lia. }
        destruct val; try (exact BYTE); destruct Hval.
      Qed.

      Lemma zero_cell (lc : loc) (w : nat) : ltac2:(tb__ "0|1|
S136Vw;U8A2S56S57Vpz;Z40A2S97VL2;Vlc;A2M0A2S56S57G0S5bVw;A1A2S57Vpz;Z1000A2A2Sa2VL2;Vbv1;S95Vlc;Vw;S99Z0A1A3A3F_;F_;F_;").
      Proof using HAMF HF HGRfp HGRimg HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp STK VF ZF msF.
        intros Hw H1 H2. unfold MallocInv.cell_holds. cbn [mc_loc mc_val mc_w sval_num]. intros j Hj.
        rewrite page_zero by lia. f_equal. unfold le_byte. rewrite Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity.
      Qed.

      Definition SC13 (u : astate) : list mcell := ltac2:(tb__ "0|9|
SbS93S95S96SbaA1U8M0SdS9bL_;M1S7cVu;A1M2SbcS99Z0M3A1M4Xdx2A3SbS93S95S96Sb5A1U4M5S99SdS0L_;G2Z1G3Xdx2A1A3SbS93S95S96Sb9A1G5S99S70Vu;A1A1A3SbS93S95S96Sb4A1G0Sa1S6eVu;A1A1A3SbS93S95S96Sb0A1G0SeS64A1M6S9bLx;S67Vu;A1M7G4S64G6S9dS77Vu;A1A1Ll;Ls0;Xex2A3SbS93S95S96Sb2A1G0S99S7aVu;A1A1A3SbS93S95S96Sb1A1G0S99S78Vu;A1M8A1A3SbS93S95S96Sb6A1G0S99S6fVu;A1A1A3SbS93S95S96Sb7A1G0Sa1S6aVu;A1A1A3SbS93S95S96Sb8A1G0Sa1S66Vu;A1A1A3SbS93S95S96SaaA1G0G1S1aG6SdLx;G7S13S64G6S19Ll;Ls0;Xex2S5fG8G3A2A2G4S9dS79Vu;A1A1Xdx2A3SbS93S95S96SabA1U1S99S71Vu;A1A1A3SbS93S95S96Sb3A1G0S68S9bLx;S6dVu;A1G4S99N1A1S16S0S9dS6cR2S5dS6bR1A2A2A1Lp;Lr;X68x3A3S11S93A1A3A3A3A3A3A3A3A3A3A3A3A3A3").
      Lemma ctx_cells_SC13 u c o : ltac2:(tb__ "0|0|
S8dS93Vc;S9fVu;A1A3S3S94Sa0Vc;A1S96Vo;A1A3S7S58Vo;SafA2S56SabVo;A2A2S8dS93Vc;S10fVu;A1A3F_;F_;F_;").
      Proof using HV184 Hav Hev Hgd HpzR.
        intros Hin Hloc Ho. unfold ctx_cells in Hin.
        apply in_app_iff in Hin as [Hin|Hin]; [exact Hin|]. exfalso.
        unfold CTX_active, CTX_seq, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
        apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
          apply in_map_iff in H1 as (k & E & Hk); subst c; apply in_seq in Hk; cbn [mc_loc] in Hloc; injection Hloc as Hloc; lia.
      Qed.
      Lemma ctx_cell_w8 u c : ltac2:(tb__ "0|0|
S8dS93Vc;S9fVu;A1A3S136SadVc;A1U8A2F_;").
      Proof using HV184 Hav Hev Hgd pz.
        intros Hin. unfold ctx_cells in Hin.
        apply in_app_iff in Hin as [Hin|Hin].
        { cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn; lia. }
        apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|Hin]; [|apply in_app_iff in Hin as [H1|H1]]];
          apply in_map_iff in H1 as (k & E & Hk); subst c; cbn; lia.
      Qed.

      Lemma B_ctxF : ltac2:(tb__ "0|1|
S3S0S8cQ40S24VrhoF;S1fZ5a3c8M0A1A2A2G0A3"). Proof using HV184 Hav Hev Hgd pz. cbn [eval]. apply u64. lia. Qed.
      Lemma B_pageF : ltac2:(tb__ "0|0|
S3S0S8cQ40S24VrhoF;S22Pc9A1A2A2Vpz;A3"). Proof using HpzR VF. rewrite (evF_201 rhoF VF). exact U201. Qed.
      Lemma ctxF_cell_in cl : ltac2:(tb__ "0|2|
S8dS20Vcl;SbS20S21S1fZ28A1Z8M0S1fZ64A1A3SbS20S21S1fZ20A1G0S29S127S22Pc9A1M1S1fZ40A1A3A3SbS20S21S1fZ48A1G0G1A3SbS20S21S1fZ50A1G0S29S127G1S1fZ1000A1A3A3SbS20S21S1fZ30A1G0S29S127S22Pb7A1S1fN1A1A3A3SbS20S21S1fZ18A1G0S1fZ0A1A3SbS20S21S1fZ38A1G0S22Pb8A1A3S11S20A1A3A3A3A3A3A3A3A3S8dS20Vcl;S39Se9Se4A1A1A3F_;").
      Proof using HAMF HF HNOTX HV183 HV184 Hgd HpzR STK. intros H. unfold ctxF, bT. destruct (st_area_tail s); cbn [ob_cells]; cbn in H; cbn; tauto. Qed.
      Lemma ctxF_in : ltac2:(tb__ "0|0|
S8dS1eSe9Se4A1Se5Se4A1A3"). Proof using HAMF HF HNOTX HV183 HV184 Hgd HpzR STK. unfold CHGF. apply in_app_iff. left. cbn. tauto. Qed.
      Lemma pageF_in : In pageF (CHGF bT). Proof using HAMF HF HNOTX HV183 HV184 Hgd HpzR STK. unfold CHGF. apply in_app_iff. left. cbn. tauto. Qed.
      Lemma secF_in : ltac2:(tb__ "0|0|
S8dS1eSd5ScfSd0PafA1Z1A3Se5Se4A1A3"). Proof using HAMF HF HNOTX HV183 HV184 Hgd HpzR STK. unfold CHGF. apply in_app_iff. left. cbn. tauto. Qed.
      Lemma brkF_in : ltac2:(tb__ "0|0|
S8dS1eSd3ScfSd0PbbA1A2Se5Se4A1A3"). Proof using HAMF HF HNOTX HV183 HV184 Hgd HpzR STK. unfold CHGF. apply in_app_iff. left. cbn. tauto. Qed.
      Lemma tailF_in T : ltac2:(tb__ "0|0|
S3SfS64A1S66Vs;A1S14S64VT;A2A3S8dS1eSeaSe5Se4A1A3F_;"). Proof using . intros HT. unfold CHGF, bT. rewrite HT. apply in_app_iff. right. left. reflexivity. Qed.

      Lemma addr_pnew d : ltac2:(tb__ "0|0|
S3S0S97VL2;S98S65Vpnew;Vd;A2A1A2S57Vpz;Vd;A2A3").
      Proof using HAC2 HF HFP2 HFRESH HIMG2 HPN HPZ HV184 Hav Hev Hgd Hmnew HpzR. pose proof HPZ as E. unfold loc_addr in *. destruct pnew as [pr po]. cbn [padd] in *. lia. Qed.
      Lemma sval_pnew d : ltac2:(tb__ "0|0|
S3S0S9eVL2;S9dS65Vpnew;Vd;A2A1A2S57Vpz;Vd;A2A3").
      Proof using HAC2 HF HFP2 HFRESH HIMG2 HPN HPZ HV184 Hav Hev Hgd Hmnew HpzR. cbn [sval_num]. unfold addr_of. apply addr_pnew. Qed.
      Lemma addr_pnew0 : ltac2:(tb__ "0|0|
S3S0S97VL2;S98Vpnew;A1A2Vpz;A3").
      Proof using HPZ. exact HPZ. Qed.
      Lemma sval_pnew0 : ltac2:(tb__ "0|0|
S3S0S9eVL2;Sa1S14S64Vpnew;A2A1A2Vpz;A3").
      Proof using HPZ. cbn [sval_num optr]. unfold addr_of. apply addr_pnew0. Qed.
      Lemma mnew_eq : ltac2:(tb__ "0|0|
S3S64Vmnew;S65Vpnew;Z18A2A3"). Proof using Hmnew. exact Hmnew. Qed.
      Lemma addr_pnew2 d1 d2 : ltac2:(tb__ "0|0|
S3S0S97VL2;S98S65S65Vpnew;Vd1;A2Vd2;A2A1A2S57S57Vpz;Vd1;A2Vd2;A2A3").
      Proof using HAC2 HF HFP2 HFRESH HIMG2 HPN HPZ HV184 Hav Hev Hgd Hmnew HpzR. pose proof HPZ as E. unfold loc_addr in *. destruct pnew as [pr po]. cbn [padd] in *. lia. Qed.
      Lemma areas_t2_ne : ltac2:(tb__ "0|0|
S6S3SeS64A1S67Vt2;A1S11S64A1A3A1").
      Proof using HF HIMG2 HPN. pose proof HF as (F2 & _). rewrite F2. destruct (st_areas s); discriminate. Qed.
      Lemma NoDup_areas : List.NoDup (st_areas s). Proof using HI. exact (proj1 (inv_areas HI)). Qed.

      Ltac leaf_addr := cbn [ob_base ctxF pageF tailF O_sec O_brk c_off am_ctx AM_P]; rewrite ?B_ctxF, ?B_pageF; rewrite soff_lit_small by qlia;
                        first [ cbn [loc_addr]; rewrite HLctx, Hctx'; qlia | rewrite addr_pnew; qlia | rewrite addr_pnew0; qlia ].
      Ltac leaf_rng := first [ rewrite rng_ctxF; cbn [fst snd loc_addr]; rewrite HLctx, Hctx'; qlia | rewrite rng_pageF, addr_pnew; cbn [fst snd]; qlia
                             | rewrite rng_pageF, addr_pnew0; cbn [fst snd]; qlia
                             | rewrite rng_secF; cbn [fst snd loc_addr]; rewrite HLctx, Hctx'; qlia | rewrite rng_brkF; cbn [fst snd loc_addr]; rewrite HLctx, Hctx'; qlia ].
      Ltac leaf_close := lazymatch goal with
        | |- In _ (CHGF _) => first [ exact ctxF_in | exact pageF_in | exact secF_in | exact brkF_in ]
        | |- In _ (ob_cells (ctxF _)) => apply ctxF_cell_in; in_list
        | |- In _ (ob_cells _) => in_list
        | |- c_width _ = _ => reflexivity
        | |- (_ <= _)%nat => qlia
        | |- sval_num _ _ = _ => first [ reflexivity | exact sval_pnew0 | exact (sval_pnew _)
                                       | solve [rewrite mnew_eq; unfold META_SIZE; cbn [sval_num]; unfold addr_of; rewrite addr_pnew2; lia] ]
        | |- bv_unsigned _ + _ = loc_addr _ _ => leaf_addr
        | |- fst _ <= _ /\ _ => leaf_rng
        | |- eval _ _ = _ => cbn [c_val]; first [ reflexivity | exact (evF_201 rhoF VF) | exact (evF_183m1 rhoF VF) | exact (evF_184 rhoF VF) | apply (evF_201o rhoF _ VF); lia ]
        | |- _ => first [ exact I | reflexivity | lia ]
        end.

      Theorem VIN : ltac2:(tb__ "0|0|
S93S8dS93R1S12S93S9aVt2;A1S137Vt2;A1A3A3S15fVL2;S10cR2A3Sa2VL2;Vbv1;R3A3F_;F_;Fc;").
      Proof using HAC2 HAMF HCW2 HF HFP2 HFPW HFRESH HGRfp HGRimg HGRpage HI HI2 HIMG2 HL2 HLctx HLold HLsec HMI HNOTX HPN HPZ HV183 HV184 HX2 Hav Hbrk2 Hev Hgd Hmnew HpzR HsmF Htp STK VF ZF.
        intros c Hc (k & Hk & T). pose proof Hctx' as HCX. pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges. pose proof HV183 as R183. pose proof HV184 as R184.
        pose proof HF as (F2 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        unfold touched in T. destruct T as [T|[T|T]].
        - destruct T as [T|T].
          {
            exfalso. destruct (HCW2 c (loc_addr L2 (mc_loc c) + Z.of_nat k) Hc ltac:(lia)) as [(e & He & Re)|Rp].
            - destruct (HFPW e _ He Re) as [[_ Rc]|(pp & _ & Rk & NI)]; [rewrite HCX in Rc; unfold CTX_SIZE in Rc; lia | apply NI; cbn [mc_img_lo mc_img_hi C_U]; lia].
            - apply (HGRimg _ (HGRpage _ Rp)). cbn [mc_img_lo mc_img_hi C_U]. lia. }

          assert (Z3 : exists off n, (0 <= off /\ off + n <= CTX_SIZE) /\ cmeets L2 c (ly_ctx L2 + off) n /\
                    ((off = 0 /\ n = 12) \/ (off = 16 /\ n = 64) \/ (off = 920 /\ n = 8))).
          { destruct T as [T|[T|T]].
            - exists 0, 12. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | rewrite HLctx, HCX; lia]|]. left; auto.
            - exists 16, 64. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | rewrite HLctx, HCX; lia]|]. right; left; auto.
            - exists 920, 8. split; [unfold CTX_SIZE; lia|]. split; [exists k; split; [exact Hk | rewrite HLctx, HCX; lia]|]. right; right; auto. }
          destruct Z3 as (off & n & [Ho1 Ho2] & CM & ZONE).
          destruct (ctx_zone (mnew :: X) R U t2 L2 HI2 HX2 HL2 c off n Hc Ho1 Ho2 CM) as [Hcc (o & Eloc & O1 & O2)].
          pose proof (ctx_cell_w8 t2 c Hcc) as W8.
          assert (Ho : o < CTX_active \/ CTX_seq <= o) by (unfold CTX_active, CTX_seq; destruct ZONE as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
          pose proof (ctx_cells_SC13 t2 c o Hcc Eloc Ho) as H13.
          unfold SC13 in H13. rewrite F2, F5, F6, F7, F8, F9, F10, F11, F12, F13, F18, F19 in H13.
          unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
            CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in H13.
          destruct H13 as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; subst c; cbn [mc_loc mc_w] in Eloc, O1, O2; injection Eloc as Eo; subst o;
            try (exfalso; clear - O1 O2 ZONE; lia); clear T O1 O2 CM W8 Hcc Hc ZONE Ho Ho1 Ho2.
          +
            apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 8) 8 (v 175)) (LCtx 0) 8 VSec (ly_sec L));
              first [ exact secF_in | exact I | reflexivity
                    | solve [cbn; tauto]
                    | solve [cbn [sval_num]; exact HLsec]
                    | solve [leaf_addr] | solve [leaf_rng]
                    | solve [cbn [c_val]; exact (evF_175 rhoF VF)]
                    | lia ].
          +
            apply (leaf_cell (O_sec AM_P (v 175) 1) (mkCell (SLit 16) 4 (SLit 1)) (LCtx 8) 4 (VZ 1) 1);
              first [ exact secF_in | exact I | reflexivity
                    | solve [cbn; tauto]
                    | solve [leaf_addr] | solve [leaf_rng]
                    | lia ].
          +
            apply (leaf_cell (ctxF bT) (mkCell (SLit 24) 8 (SLit 0)) (LCtx 16) 8 (optr None) 0); leaf_close.
          +
            replace (match st_areas s ++ [pnew] with [] => VZ 0 | _ :: _ => VP (padd mnew META_SIZE) end) with (VP (padd mnew META_SIZE)) by (destruct (st_areas s); reflexivity).
            apply (leaf_cell (ctxF bT) (mkCell (SLit 32) 8 (SAlu ALU_ADD (SVar 201) (SLit 64))) (LCtx 24) 8 (VP (padd mnew META_SIZE)) (pz + 64)); leaf_close.
          +
            apply (leaf_cell (ctxF bT) (mkCell (SLit 40) 8 (SLit 100)) (LCtx 32) 8 (VZ (METAS_PER_AREA - 1)) 100); leaf_close.
          +
            apply (leaf_cell (ctxF bT) (mkCell (SLit 48) 8 (SAlu ALU_ADD (SVar 183) (SLit (-1)))) (LCtx 40) 8 (VZ (V183 - 1)) (V183 - 1)); leaf_close.
          +
            apply (leaf_cell (ctxF bT) (mkCell (SLit 56) 8 (SVar 184)) (LCtx 48) 8 (VZ V184) V184); leaf_close.
          +
            destruct (st_area_tail s) as [T0|] eqn:HT.
            * pose proof (tail_facts T0 HT) as (HinT & ET & Hne & T1 & T2 & E186 & [h Eh]). rewrite Eh.
              pose proof (inv_areas HI) as (_ & _ & Ehead & _). rewrite Eh in Ehead.
              assert (Hh : In h (st_areas s)) by (destruct (st_areas s); [discriminate | injection Ehead as ->; left; reflexivity]).
              apply (leaf_cell (ctxF bT) (mkCell (SLit 64) 8 (SVar 185)) (LCtx 56) 8 (optr (Some h)) (zA h));
                first [ exact ctxF_in | exact I | reflexivity
                      | solve [unfold ctxF, bT; rewrite HT; cbn; tauto]
                      | solve [cbn [sval_num optr]; unfold zA; apply HLold; exact (area_below X R U s HI h Hh)]
                      | solve [leaf_addr] | solve [leaf_rng]
                      | solve [cbn [c_val]; change (SVar 185) with (v 185); rewrite (evF_F2 rhoF 185 VF ltac:(cbn; tauto)), ev185, Eh; reflexivity]
                      | lia ].
            * pose proof (notail_facts HT) as [Ea Eh]. rewrite Eh.
              apply (leaf_cell (ctxF bT) (mkCell (SLit 64) 8 (SVar 201)) (LCtx 56) 8 (optr (Some pnew)) (pz));
                first [ exact ctxF_in | exact I | reflexivity
                      | solve [unfold ctxF, bT; rewrite HT; cbn; tauto]
                      | solve [exact sval_pnew0]
                      | solve [leaf_addr] | solve [leaf_rng]
                      | solve [cbn [c_val]; exact (evF_201 rhoF VF)]
                      | lia ].
          +
            apply (leaf_cell (ctxF bT) (mkCell (SLit 72) 8 (SVar 201)) (LCtx 64) 8 (optr (Some pnew)) (pz)); leaf_close.
          +
            replace (if match st_areas s ++ [pnew] with [] => true | _ :: _ => false end && (V183 - 1 =? 0) then VZ 0 else VP (padd pnew 4096)) with (VP (padd pnew 4096))
              by (destruct (st_areas s); reflexivity).
            apply (leaf_cell (ctxF bT) (mkCell (SLit 80) 8 (SAlu ALU_ADD (SVar 201) (SLit 4096))) (LCtx 72) 8 (VP (padd pnew 4096)) (pz + 4096)); leaf_close.
          +
            apply (leaf_cell (O_brk AM_P (v 187)) (mkCell (SLit 928) 8 (v 187)) (LCtx 920) 8 (brk_sval t2) V187);
              first [ exact brkF_in | reflexivity
                    | solve [cbn; tauto]
                    | solve [unfold brk_sval; destruct (st_brk t2); exact I]
                    | solve [exact Hbrk2]
                    | solve [leaf_addr] | solve [leaf_rng]
                    | solve [cbn [c_val]; exact (evF_187 rhoF VF)]
                    | lia ].
        -
          destruct (HCW2 c (loc_addr L2 (mc_loc c) + Z.of_nat k) Hc ltac:(lia)) as [(e & He & Rx)|NP].
          { exfalso. exact (HGRfp e _ He Rx T). }
          assert (Hpn : In pnew (st_areas t2)) by (rewrite F2; apply in_app_iff; right; left; reflexivity).
          assert (ZI : range_incl (pz, 4096) (crange L2 (e_area pnew))).
          { unfold range_incl, crange, e_area. cbn [fst snd]. rewrite HPZ. unfold PGSZ. lia. }
          pose proof (AreaZone.area_zone (mnew :: X) R U t2 L2 HI2 HX2 HL2 pnew c (pz) 4096 Hpn Hc ZI
                        ltac:(exists k; split; [exact Hk | unfold PGSZ in NP; lia])) as AC.
          rewrite F2, (AreaZone.succ_in_app_last (st_areas s) pnew HPN) in AC.
          rewrite HAC2 in AC.
          unfold area_cells in AC. apply in_app_iff in AC as [AC|AC].
          + cbn in AC. destruct AC as [<-|[<-|[<-|[]]]].
            *
              apply (leaf_cell pageF (mkCell (SLit 0) 8 (v 175)) (LMem pnew) 8 VSec (ly_sec L));
                first [ exact pageF_in | exact I | reflexivity
                      | solve [cbn; tauto]
                      | solve [leaf_addr] | solve [leaf_rng]
                      | solve [cbn [c_val]; change (SVar 175) with (v 175); exact (evF_175 rhoF VF)]
                      | lia ].
            *
              apply (leaf_cell pageF (mkCell (SLit 8) 8 (SLit 0)) (LMem (padd pnew 8)) 8 (optr None) 0); leaf_close.
            *
              apply (leaf_cell pageF (mkCell (SLit 16) 4 (SLit 101)) (LMem (padd pnew 16)) 4 (VZ METAS_PER_AREA) 101); leaf_close.
          +
            apply in_flat_map in AC as [j [Hj AC]]. apply in_seq in Hj.
            pose proof (HFRESH (Z.of_nat j) ltac:(lia)) as FR. unfold MT in FR.
            rewrite FR in AC. cbn [meta_slot_cells] in AC. unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, AREA_HDR, META_SIZE, METAS_PER_AREA in *.
            assert (PP : forall d1 d2, padd (padd pnew d1) d2 = padd pnew (d1 + d2)) by (intros; destruct pnew; cbn [padd]; f_equal; lia).
            rewrite !PP in AC.
            destruct (Nat.eq_dec j 0) as [->|Hj0].
            * cbn [Z.of_nat Z.mul Z.add] in AC.
              destruct AC as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
                [ apply (leaf_cell pageF (mkCell (SLit 24) 8 (SLit 0)) (LMem (padd pnew 24)) 8 (VZ 0) 0)
                | apply (leaf_cell pageF (mkCell (SLit 32) 8 (SLit 0)) (LMem (padd pnew 32)) 8 (VZ 0) 0)
                | apply (leaf_cell pageF (mkCell (SLit 40) 8 (SLit 0)) (LMem (padd pnew 40)) 8 (VZ 0) 0)
                | apply (leaf_cell pageF (mkCell (SLit 48) 4 (SLit 0)) (LMem (padd pnew 48)) 4 (VZ 0) 0)
                | apply (leaf_cell pageF (mkCell (SLit 52) 4 (SLit 0)) (LMem (padd pnew 52)) 4 (VZ 0) 0)
                | apply (leaf_cell pageF (mkCell (SLit 56) 8 (SLit 0)) (LMem (padd pnew 56)) 8 (VZ 0) 0) ]; leaf_close.
            * assert (J1 : 1 <= Z.of_nat j <= 100) by lia.
              destruct AC as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (apply zero_cell; [lia| rewrite addr_pnew; lia | rewrite addr_pnew; lia]).
        -
          unfold tailword in T. revert T. destruct (st_area_tail s) as [T0|] eqn:HT; intros T; [|destruct T].
          pose proof (tail_facts T0 HT) as (HinT & ET & Hne & T1 & T2 & E186 & _).
          assert (HinT2 : In T0 (st_areas t2)) by (rewrite F2; apply in_app_iff; left; exact HinT).
          assert (AT : loc_addr L2 (LMem T0) = zA T0).
          { unfold zA. pose proof (HLold T0 (area_below X R U s HI T0 HinT)) as E. unfold addr_of in E. exact E. }
          assert (ZI : range_incl (zA T0 + 8, 8) (crange L2 (e_area T0))).
          { unfold range_incl, crange, e_area. cbn [fst snd]. rewrite AT. unfold PGSZ. lia. }
          pose proof (AreaZone.area_zone (mnew :: X) R U t2 L2 HI2 HX2 HL2 T0 c (zA T0 + 8) 8 HinT2 Hc ZI
                        ltac:(exists k; split; [exact Hk | lia])) as AC.
          rewrite F2, ET, (AreaZone.succ_in_app_prev (st_areas s) pnew (SP 0%nat 0) Hne NoDup_areas) in AC. rewrite <- ET in AC.
          pose proof (AreaZone.area_cells_next_word t2 L2 T0 (Some pnew) c AC ltac:(rewrite AT; exists k; split; [exact Hk | lia])) as ->.
          assert (AT8 : loc_addr L2 (LMem (padd T0 8)) = zA T0 + 8) by (unfold loc_addr in AT |- *; destruct T0; cbn [padd] in *; lia).
          apply (leaf_cell tailF (mkCell (SLit 8) 8 (SVar 201)) (LMem (padd T0 8)) 8 (optr (Some pnew)) (pz));
            first [ exact (tailF_in T0 HT) | exact I | reflexivity
                  | solve [cbn; tauto]
                  | solve [exact sval_pnew0]
                  | solve [cbn [ob_base tailF c_off]; rewrite E186; rewrite soff_lit_small by lia; rewrite AT8; lia]
                  | solve [rewrite (rng_tailF T0 HT), AT8; cbn [fst snd]; lia]
                  | solve [cbn [c_val]; exact (evF_201 rhoF VF)]
                  | lia ].
      Qed.

      Theorem OLD : ltac2:(tb__ "0|2|
S93S8dS93R1S12S93S9aVt2;A1S137Vt2;A1A3A3S6S15fVL2;S10cR2A3A1S4S8dS93R3S12S93S9aVs;A1S137Vs;A1A3A3S4S3S0S97VL2;Sa0R3A1M0A2S97VL;G0A2A3S3S0S9eVL2;SbeR3A1M1A2S9eVL;G1A2A3A2A2F_;F_;Fc;").
      Proof using HAC2 HAMF HCTX2 HF HFP2 HFRESH HGRpage HI HIMG2 HLctx HLext HLold HMI HNOTX HPN HPZ HV183 HV184 HXr Hav Hev Hgd Hmnew HpzR STK VF.
        intros c Hc NM. pose proof Hctx' as HCX. pose proof HpzR as (P1 & P2 & P3 & P4).
        pose proof (cell_w_posI t2 c Hc) as WP.
        destruct (HIMG2 c Hc) as [Hcx|[[Hne ->]|[Hnew|(Hin & q & Eq)]]].
        - destruct (HCTX2 c Hcx) as [(o & w & val & -> & Wp & Ho)|[Hold Hna]].
          + exfalso. apply NM. exists 0%nat. split; [exact Wp|]. cbn [mc_loc loc_addr]. rewrite HLctx, HCX. unfold touched. left. lia.
          + assert (ST := AllocMetaGrow.cell_stable X R U s HI HXr L L2 c HLext ltac:(apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Hold)
                            ltac:(intros E; exfalso; exact (Hna E))).
            split; [apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Hold | exact ST].
        - exfalso. apply NM. pose proof (inv_areas HI) as (_ & _ & _ & Etail & _).
          destruct (st_area_tail s) as [T0|] eqn:HT.
          + pose proof (tail_facts T0 HT) as (HinT & ET & _ & T1 & T2 & _).
            exists 0%nat. split; [cbn; lia|]. unfold C_tn. cbn [mc_loc mc_w]. rewrite <- ET.
            unfold touched, tailword. rewrite HT. right; right.
            pose proof (HLold T0 (area_below X R U s HI T0 HinT)) as E. unfold zA, addr_of, loc_addr in *. destruct T0; cbn [padd prid poff] in *. lia.
          + exfalso. rewrite ?HT in Etail. destruct (st_areas s); [exact (Hne eq_refl) | discriminate].
        - exfalso. apply NM. destruct (In_area_cells _ _ _ _ Hnew) as (d & Ed & Hd & Hw). exists 0%nat. split; [lia|].
          rewrite Ed, addr_pnew. unfold touched. right; left. apply HGRpage. unfold PGSZ in *. lia.
        - assert (ST := AllocMetaGrow.cell_stable X R U s HI HXr L L2 c HLext Hin ltac:(intros E; rewrite Eq in E; discriminate)).
          split; [exact Hin | exact ST].
      Qed.

      Theorem minvI2 : ltac2:(tb__ "0|0|
S146Sc2SbS64Vmnew;VX;A3VR;VU;Sf4Vt2;VL2;A2SefS51S10bA2Sf0S51S10bA2Vvm2;A8").
      Proof using Erd Ewok GRdec HAC2 HAMF HB2 HCTX2 HCW2 HF HFP2 HFPW HFRESH HGRfp HGRimg HGRpage HI HI2 HIMG2 HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom HsmF Htp MF STK VF ZF bv0 rv0.
        unfold MInvI. pose proof Hctx' as HCX. pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges.
        refine (GapGrow.minv_postGX C_U (Inv X R U) (Inv (mnew :: X) R U) s t2 L L2 (Glue.rd_of segsU mW) (Glue.rd_of segsU mF) (Glue.wok_of segsU mW) (Glue.wok_of segsU mF) vm vm2
                  HMI0 HI2 HB2 HL2 HLctx HUB2 HV2 HLG2 HRES2
                  touched touched_dec [(LMem pnew, PGSZ)] _ _ _ _ V1 VIN VM OLD _ _ _ statics_in_image_U _ _ _ HMW2).
        - intros e He. apply HFP2 in He as [He| ->]; [left; exact He | right; left; reflexivity].
        - intros e He _. exact (HLfp e He).
        - intros b Hb. exact (HLub b Hb).
        - intros e x [<-|[]] Hx. cbn [fst snd] in Hx. rewrite HPZ in Hx. unfold touched. right; left. apply HGRpage. unfold PGSZ in *. lia.
        - intros c Hc. exact (cell_spanI (mnew :: X) R U t2 L2 HI2 HX2 HL2 c Hc).
        - intros x Hx. exact (owned_spanI t2 L2 HL2 x Hx).
        - intros c Hc. exact (cell_w_posI t2 c Hc).
        - intros x T Himg. unfold touched, tailword in T. destruct T as [T|[T|T]].
          + destruct T as [T|T]; [right; unfold mc_errno; cbn [mc_tp C_U]; lia | left; cbn [mc_ctx C_U]; unfold CTX_SIZE; lia].
          + exfalso. exact (HGRimg x T Himg).
          + exfalso. destruct (st_area_tail s) as [T0|] eqn:HT; [|destruct T]. pose proof (tail_facts T0 HT) as (HinT & _).
            assert (RX : loc_addr L (fst (LMem T0, PGSZ)) <= x < loc_addr L (fst (LMem T0, PGSZ)) + snd (LMem T0, PGSZ)) by (cbn [fst snd]; unfold zA, addr_of, PGSZ in *; lia).
            destruct (HFPW (LMem T0, PGSZ) x (e_area_In s T0 HinT) RX) as [[E _]|(pp & _ & _ & NI)]; [discriminate|]. exact (NI Himg).
        - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
          unfold CTX_SIZE in Hx. clear - Hx. lia.
        - intros Hf. exfalso. pose proof HF as (_ & F5 & _). rewrite F5 in Hf. discriminate.
      Qed.

      Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
SdS8aQ40A1L_;S1aS60Z64M0S2Vj;A1M1A2S61G1Z84A2A2S24VrhoF;S28Se8Se4A1S5cG1G0A2A2A2S26Vrho;Vj;A2Xdx2").
      Definition rho' : valuation := ltac2:(tb__ "0|0|
S3fS10eS35VrhoF;A1S10bA3").
      Lemma rw'_low j : ltac2:(tb__ "0|0|
S12fVj;P64A2S3S8aQ40A1S10eVj;A1S26Vrho;Vj;A2A3F_;").
      Proof using HV184 Hav Hev Hgd pz. intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity. Qed.
      Lemma rwF_low j : ltac2:(tb__ "0|0|
S12fVj;PaaA2S3S8aQ40A1S26VrhoF;Vj;A2S26Vrho;Vj;A2A3F_;").
      Proof using VF. intros Hj. exact (proj1 VF j Hj). Qed.
      Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S12dS52Vrho;S10dA3").
      Proof using HV184 Hav Hev Hgd VF.
        split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
        intros l. cbn [rl rho']. pose proof VF as (_ & _ & _ & _ & _ & _ & _ & F7). rewrite (F7 l). reflexivity.
      Qed.
      Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S56Z1Vz;A2S56Vz;Z1fA2A2S3SdS53S59Vz;A1M0A1S13A3S5S1S1S4S3S23S54G0A1S22R1A1A3S12fR1P64A2A2Lvv;A2F_;F_;").
      Proof using HV184 Hav Hev Hgd pz.
        intros Hr Hcs.
        pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
        cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
        destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
      Qed.
      Lemma reg_sv_ok z : ltac2:(tb__ "0|1|
S4S56Z1Vz;A2S56Vz;Z1fA2A2S3S23S28S138SfcA1Vz;A2SdS23L_;S53S59Vz;A1M0A1S54G0A1S22S130P64S133G0A1A2A1Xdx2A3F_;").
      Proof using HV184 Hav Hev Hgd pz.
        intros Hz.
        pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_ok IEC_U) z)
                       (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
        apply sv_eqb_sound in H. exact H.
      Qed.
      Lemma freg_sv_ok z : ltac2:(tb__ "0|2|
S4S56Z0M0Vz;A2S56Vz;Z1fA2A2S5S1S1S4S3S23S3dS138SfcA1Vz;A2S22R1A1M1A3S4S3S23S122S23S59Vz;A1S55S1fG0A1A4G1A3S4S131P3cR1A2S12fR1P64A2A2A2A2Lvv;A2F_;").
      Proof using HV184 Hav Hev Hgd pz.
        intros Hz.
        pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                      ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
        unfold freg_sv. change (ss_fregs (L_am_ok IEC_U)) with pre_fregs.
        destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
        apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
      Qed.
      Lemma E110 : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S10eP6eA1S8bG0S57Vpz;Z18A2A2A3").
      Proof using HV184 Hav Hev Hgd HpzR VF.
        unfold rw'. change ((100 <=? Z.pos 110) && (Z.pos 110 <? 132))%bool with true. change (Z.pos 110 - 100) with 10.
        destruct (LF_misc bT) as (_ & _ & _ & _ & _ & Ma0). rewrite Ma0. apply (evF_201o rhoF 24 VF). lia.
      Qed.
      Lemma U110 : ltac2:(tb__ "0|0|
S3S0S8cQ40S10eP6eA1A2S57Vpz;Z18A2A3").
      Proof using HV184 Hav Hev Hgd HpzR VF. pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges. rewrite E110. apply u64. unfold PGSZ in *. lia. Qed.
      Lemma EBs : ltac2:(tb__ "0|1|
S3S8aQ40A1S24S10dS22PaA1M0A2S24VrhoF;G0A2A3").
      Proof using HV184 Hav Hev Hgd VF. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
      Lemma ELs : ltac2:(tb__ "0|0|
S3S0S31S10dS22S158A1A2S31VrhoF;S22PfA1A2A3").
      Proof using HV184 Hav Hev Hgd VF. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
      Lemma EQbs : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S24S10dS22S15dA1A2S8bG0S57Vpz;Z18A2A2A3").
      Proof using HV184 Hav Hev Hgd HpzR VF. unfold V_RES. cbn [eval rho' rw]. exact E110. Qed.
      Lemma RSF : ltac2:(tb__ "0|1|
S3S10S0S0A2S25VrhoF;Sd6SdaA1A2ScS0S0S57S119Vrho;A1M0S118Vrho;A1A2G0A4A3").
      Proof using Hav Hev Hgd VF.
        rewrite <- (rng_stk frame_cells). unfold obj_range, obj_lo_of, obj_hi_of, O_stk. cbn [ob_base ob_lo ob_hi].
        rewrite (evF_low rhoF (SVar 10) VF eq_refl). unfold soff. rewrite (evF_low rhoF (SVar 15) VF eq_refl). reflexivity.
      Qed.
      Lemma RS' : ltac2:(tb__ "0|1|
S3S10S0S0A2S25S10dS15bS13dA1A2ScS0S0S57S119Vrho;A1M0S118Vrho;A1A2G0A4A3").
      Proof using HV184 Hav Hev Hgd VF. rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity. Qed.
      Lemma RQ' : ltac2:(tb__ "0|0|
S3S10S0S0A2S25S10dS13fA2ScS0S0S57Vpz;Z18A2S57Vpz;Z40A2A4A3").
      Proof using HV184 Hav Hev Hgd HpzR VF.
        pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges.
        unfold obj_range, obj_lo_of, obj_hi_of, meta_obj0. cbn [ob_base ob_lo ob_hi]. rewrite EQbs. unfold META_SIZE. rewrite !soff_lit_small by lia.
        rewrite u64 by lia. f_equal; lia.
      Qed.

      Theorem smatch_ok : ltac2:(tb__ "0|0|
S2aS51S10dS138SfcA1ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd2;A2A4A4").
      Proof using HAMF HF HFpre HNOTX HV183 HV184 Hav Hev Hgd HpzR HsmF STK VF.
        pose proof HpzR as (P1 & P2 & P3 & P4). top_ranges. pose proof Hpz8 as P8.
        pose proof STK as (S1 & S2 & S3 & S4). top_ranges.
        unfold smatch. cbn [fst snd cfg_ms cfg_model].
        split; [vm_compute; reflexivity|].
        split; [exact F_pc|].
        split; [exact F_pend|]. split; [exact F_halt|]. split; [exact HromF|]. split; [exact HroF|].
        split.
        {   intros r Hr0. rewrite (F_regs r Hr0).
          assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
          rewrite reg_sv_ok by lia.
          destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
          - destruct (pre_reg_cs (bv_unsigned r) ltac:(lia) CS) as (vv & E & Hv100).
            rewrite (LF_cs bT (bv_unsigned r) ltac:(lia) CS), E.
            cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. first [apply rwF_low | symmetry; apply rwF_low]; lia.
          - cbn [eval rho' rw]. unfold rw'.
            replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
              by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
            replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by lia.
            reflexivity. }
        split.
        {   intros r. rewrite (F_fregs r).
          assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
          destruct (freg_sv_ok (bv_unsigned r) ltac:(lia)) as (vv & E1 & E2 & Hvv). rewrite E1.
          unfold freg_sv. destruct (LF_misc bT) as (_ & _ & Mfr & _). rewrite Mfr, E2.
          cbn [eval rho' rw]. rewrite rw'_low by lia. first [apply rwF_low | symmetry; apply rwF_low]; lia. }
        split; [exact F_fcsr|].
        split; [exact F_resv|].
        split.
        {
          assert (HOS : obj_holds segsU rhoF msF (O_stk frame_cells)) by (apply (proj1 (Forall_forall _ _) HOF); left; reflexivity).
          assert (HOQ : obj_holds segsU rhoF msF pageF) by (apply (proj1 (Forall_forall _ _) HOF); apply OBJF_perm; right; apply in_app_iff; right; exact pageF_in).
          split; [|split].
          - constructor; [|constructor; [|constructor]].
            + apply obj_holds_drop_cells in HOS.
              destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
              cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
              rewrite EBs, ELs. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
              intros z Hz Hnc. apply B4; [exact Hz|]. intros C. inversion C.
            +
              assert (SPL : SymObj.obj_split pageF (SLit 24) = Some (pageF_lo, pageF_hi)) by (vm_compute; reflexivity).
              pose proof (SymObj.obj_split_holds segsU rhoF msF pageF (SLit 24) pageF_lo pageF_hi AM_NEXT SPL ltac:(vm_compute; reflexivity) HOQ
                            ltac:(unfold obj_lo_of, obj_hi_of; cbn [ob_lo ob_hi pageF]; rewrite !soff_lit_small by lia; lia)) as [_ HOQ2].
              assert (EB2 : bv_unsigned (eval rhoF (ob_base pageF_hi)) + 24 = bv_unsigned (eval rho' (ob_base meta_obj0))).
              { cbn [ob_base pageF_hi meta_obj0]. rewrite B_pageF, EQbs. rewrite u64 by lia. reflexivity. }
              apply (obj_holds_transfer segsU rhoF rho' msF pageF_hi meta_obj0 AM_NEXT HromF); [vm_compute; reflexivity | | | reflexivity | | left; split; reflexivity | exact HOQ2].
              * unfold obj_lo_of. rewrite <- EB2. cbn [ob_lo pageF_hi meta_obj0]. rewrite !soff_lit_small by lia. lia.
              * unfold obj_hi_of. rewrite <- EB2. cbn [ob_hi pageF_hi meta_obj0]. unfold META_SIZE. rewrite !soff_lit_small by lia. lia.
              * intros c2 Hc2. unfold cell_abs. rewrite <- EB2.
                unfold meta_obj0, meta_cells0 in Hc2. cbn [ob_cells] in Hc2.
                destruct Hc2 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
                  [ exists (mkCell (SLit 24) 8 (SLit 0)) | exists (mkCell (SLit 32) 8 (SLit 0)) | exists (mkCell (SLit 40) 8 (SLit 0))
                  | exists (mkCell (SLit 48) 4 (SLit 0)) | exists (mkCell (SLit 52) 4 (SLit 0)) | exists (mkCell (SLit 56) 8 (SLit 0)) ];
                  (split; [cbn; tauto|]); cbn [c_off c_val c_width eval]; rewrite !soff_lit_small by lia;
                  match goal with |- (?a, _, _) = (?b, _, _) => replace b with a by lia; reflexivity end.
          - cbn [pairwise_disjoint]. split; [constructor; [|constructor]|split; [constructor|exact I]].
            rewrite RS', RQ'. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
          - intros a Ha. cbn [rm rho'].
            destruct (in_ranges_dec rhoF (UNCHF ++ CHGF bT) a) as [IN|OUT].
            + unfold mF. rewrite (ReabKit.kit_in _ _ _ _ _ IN). reflexivity.
            + unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply HfrF.
              apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS. rewrite RS' in HaS.
              constructor; [cbn zeta; rewrite RSF; exact HaS|].
              apply Forall_forall. intros o Ho. cbn zeta. intros RR. apply OUT. exists o. split; [|exact RR].
              exact (OBJF_tail bT o Ho). }

        unfold L_am_ok. cbn [ss_facts].
        assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
        { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
        pose proof HFpre as HF0. cbn [ss_facts ContractAM.Pre_am] in HF0.
        unfold F_meta_facts. cbn [app].
        pose proof U110 as U110.
        assert (AR : 0 <= 3 /\ (pz + 24 =? 0) = false /\ 4096 <= pz + 24 /\ (pz + 24 + 40) mod 2 ^ 64 <= 0x7fffff800000 /\ (pz + 24) mod 8 = 0
                     /\ 0 <= 0 < 2 ^ 64 /\ 0 <= 4096 < 2 ^ 64 /\ 0 <= 40 < 2 ^ 64 /\ 0 <= 0x7fffff800000 < 2 ^ 64).
        { clear - P1 P2 P3 P4 P8. top_ranges. rewrite Z.eqb_neq. rewrite Z.mod_small by lia. unfold PGSZ in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|lia].
          Z.to_euclidean_division_equations; lia. }
        destruct AR as (AR0 & ARnz & AR1 & AR2 & AR8 & ARz & AR4k & AR40 & ARc).
        constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. split; [exact AR0|]. rewrite U110. change (2 ^ 3) with 8. exact AR8. }
        constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold branch_taken, bv_eqb. rewrite U110. rewrite (u64 _ ARz).
                       rewrite ARnz. intros X0; discriminate. }
        constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. rewrite U110. rewrite (u64 _ AR4k). exact AR1. }
        constructor. { cbn [SymState.holds eval rho' rw]. unfold V_RES. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
                       rewrite U110. top_ranges. unfold META_SIZE. rewrite (u64 _ AR40), (u64 _ ARc). exact AR2. }
        repeat (constructor; [apply AGR; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0); cbn; tauto|]). constructor.
      Qed.

      Theorem kept2 : ltac2:(tb__ "0|0|
S159S51Sc2Sf4Vs;VL;A2Sf4Vt2;VL2;A2S27Vrho;A1S10bA6").
      Proof using EmW HAMF HBW HF HFPW HGRblock HGRceil HGRimg HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 HXr Hav Hev Hgd HpzR Htp MF STK VF.
        intros x Hx CA _ NE NS. pose proof Hctx' as HCX. rewrite <- EmW. pose proof HpzR as (P1 & P2 & P3 & P4).
        assert (NCTX : ~ (369616 <= x < 369616 + CTX_SIZE)).
        { intros Hc. destruct CA as [H|[(b & n & Hin & Hr)|(_ & H & _)]].
          - top_ranges. unfold CTX_SIZE in Hc. lia.
          - destruct (HBW b n x Hin Hr) as (e & pp & He & Ep & Rx).
            destruct (HFPW e x He Rx) as [[E1 _]|(p' & _ & _ & NI)]; [rewrite Ep in E1; discriminate|]. apply NI. cbn [mc_img_lo mc_img_hi C_U]. unfold CTX_SIZE in Hc. lia.
          - apply H. cbn [mc_ctx C_U]. exact Hc. }
        assert (NG : ~ GR x).
        { intros G. destruct CA as [H|[(b & n & Hin & Hr)|(W & _)]].
          + pose proof (HGRceil x G) as CE. clear - H CE. cbn [ma_L] in H. top_ranges. lia.
          + exact (HGRblock b n x Hin Hr G).
          + apply (HGRimg x G). pose proof (ClientLaws.wseg_in_image_U (Z_to_bv 64 x) W) as WI. rewrite u64 in WI by lia. exact WI. }
        assert (NT : ~ tailword x).
        { unfold tailword. destruct (st_area_tail s) as [T0|] eqn:HT; [|tauto]. intros RX8.
          pose proof (tail_facts T0 HT) as (HinT & _ & _ & T1 & T2 & _).
          assert (RX : loc_addr L (fst (LMem T0, PGSZ)) <= x < loc_addr L (fst (LMem T0, PGSZ)) + snd (LMem T0, PGSZ)) by (cbn [fst snd]; unfold zA, addr_of, PGSZ in *; lia).
          destruct CA as [H|[(b & n & Hin & Hr)|(W & _)]].
          + pose proof (area_R T0 HinT) as (_ & RT2 & _). clear - H RT2 RX8. cbn [ma_L] in H. top_ranges. unfold zA, addr_of, PGSZ in *. lia.
          + unfold blocks in Hin. apply in_map_iff in Hin as [[p0 n'] [E0 Hin]]. cbn [fst snd] in E0. injection E0 as Eb En. subst b n'.
            pose proof (Zones2.image_cell_owned X R U s L HI HXr HL _ (tail_cell_image T0 HT) (Z.to_nat (x - (zA T0 + 8))) ltac:(cbn [mc_w]; lia)) as [_ Hnu].
            cbn [mc_loc] in Hnu. replace (loc_addr L (LMem (padd T0 8)) + Z.of_nat (Z.to_nat (x - (zA T0 + 8)))) with x in Hnu
              by (unfold zA, addr_of, loc_addr in *; destruct T0; cbn [padd] in *; lia).
            apply Hnu. exists (p0, n). split; [exact Hin|]. cbn [fst snd]. exact Hr.
          + pose proof (ClientLaws.wseg_in_image_U (Z_to_bv 64 x) W) as WI. rewrite u64 in WI by lia.
            destruct (HFPW (LMem T0, PGSZ) x (e_area_In s T0 HinT) RX) as [[E1 _]|(p' & _ & _ & NI)]; [discriminate|]. exact (NI WI). }
        destruct (in_ranges_dec rhoF (UNCHF ++ CHGF bT) (Z_to_bv 64 x)) as [IN|OUT].
        - exfalso. destruct IN as (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho].
          + pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite UNCH_rangesF in RNG.
            unfold alloc_static, errno_range, mc_errno in NS, NE. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in NS, NE.
            unfold CTX_SIZE in NCTX. clear - RNG RR NS NE NCTX.
            repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; lia|]). destruct RNG.
          + pose proof (CHG_touched o x Ho RR) as T. unfold touched in T. unfold CTX_SIZE in NCTX. unfold errno_range, mc_errno in NE. cbn [mc_tp C_U] in NE.
            destruct T as [T|[T|T]]; [clear - T NCTX NE; lia | exact (NG T) | exact (NT T)].
        - unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply MF. rewrite u64 by lia. exact NG.
      Qed.

      Theorem maps_kept2 : ltac2:(tb__ "0|0|
SfeSf4Vs;VL;A2S27Vrho;A1S10bA3").
      Proof using EmW HAMF HF HGRmaps HGRpage HI HIMG2 HMI HNOTX HPN HV183 HV184 Hav Hev Hgd HpzR Htp MF STK VF.
        intros k rg Hk Hkd Hl x Hx. cbn [ma_s ma_L] in *. rewrite <- EmW.
        destruct (map_region_where k rg x Hk Hkd Hl Hx) as (R64 & NI & NA & NK). cbn [mc_img_lo mc_img_hi C_U] in NI.
        destruct (in_ranges_dec rhoF (UNCHF ++ CHGF bT) (Z_to_bv 64 x)) as [INR|OUT].
        - exfalso. destruct INR as (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho].
          + pose proof (in_map (obj_range rhoF) _ _ Ho) as RNG. rewrite UNCH_rangesF in RNG.
            clear - RNG RR NI. cbn in RNG. repeat (destruct RNG as [E|RNG]; [rewrite <- E in RR; cbn [fst snd] in RR; lia|]). destruct RNG.
          + destruct (CHG_in o Ho) as [->|[->|[->|[->|[->|[-> [T0 HT]]]]]]].
            * rewrite rng_errF in RR. cbn [fst snd] in RR. clear - RR NI. lia.
            * rewrite rng_secF in RR. cbn [fst snd] in RR. clear - RR NI. lia.
            * rewrite rng_ctxF in RR. cbn [fst snd] in RR. clear - RR NI. lia.
            * rewrite rng_brkF in RR. cbn [fst snd] in RR. clear - RR NI. lia.
            * rewrite rng_pageF in RR. cbn [fst snd] in RR. exact (HGRmaps k rg x Hk Hl Hkd Hx (HGRpage x ltac:(lia))).
            * rewrite (rng_tailF T0 HT) in RR. cbn [fst snd] in RR. pose proof (tail_facts T0 HT) as (HinT & _).
              apply (NA T0 HinT). unfold PGSZ. lia.
        - unfold mF. rewrite (ReabKit.kit_out _ _ _ _ _ OUT). apply MF. rewrite u64 by lia. intros G. exact (HGRmaps k rg x Hk Hl Hkd Hx G).
      Qed.

      Theorem canary_kept2 : ltac2:(tb__ "0|0|
SfdS51Sc2S27Vrho;A1S10bA4").
      Proof using EmW Erd Ewok HAMF HF HMI HNOTX HV183 HV184 Hav Hav_rd Hev Hgd Hgd_rd HpzR Hrom HsmF STK VF.
        intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
        pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCHF] in R0, R1.
        destruct Hx as [Hx|Hx].
        - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
        - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
      Qed.

      Theorem post_ok2 : ltac2:(tb__ "0|0|
S12bS51S52Vrho;S139S51Sc2SfcVX;VR;VU;Sf4Vs;VL;A2VKc;A8ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd2;A2A4A5").
      Proof using EmW Erd Evm2 Ewok GRdec HAC2 HAMF HB2 HBW HCTX2 HCW2 HF HFP2 HFPW HFRESH HFpre HGRblock HGRceil HGRfp HGRimg HGRmaps HGRpage HI HI2 HIMG2 HKEYS HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr HY Haddr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom HsmF Htp K2 MF STK VF ZF bv0 bv1 rv0 rv1.
        exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'.
        split; [right; left; reflexivity|]. split; [exact agree_vals_rho'|]. split; [exact smatch_ok|].
        cbn [w_tr w_cfg fst snd cfg_model].
        exists (mkMA t2 L2), mnew. cbn [ma_s ma_L].
        pose proof HAMF as (AF & US & UB). pose proof HNOTX as (M1 & M2).
        pose proof HF as (F2 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        split; [cbn [rw rho']; unfold V_RES; rewrite U110, Haddr; unfold AREA_HDR; lia|].
        split; [unfold MInvIR; cbn [rm rho']; rewrite rdG, wokG, Evm2; exact minvI2|].
        split.
        { split; [exact HX2|]. split; [exact F5|]. split; [exact AF|]. split; [repeat split; assumption|].
          split; [exact US|]. split; [exact UB|]. cbn [ma_s ma_L]. split; [exact HKEYS | exact HLext]. }
        split; [exact M1|]. split; [exact M2|]. split; [exact kept2|]. split; [exact maps_kept2|]. split; [exact canary_kept2|].
        split; [exists ktr; exact HY | exact K2].
      Qed.

      Theorem post_ok2_only : ltac2:(tb__ "0|1|
S12bS51S52Vrho;SbS10S2bS12cA2M0ScS2bS12cS138SfcA1S13bS51Sc2VX;VR;VU;Sf4Vs;VL;A2VKc;A7A4S11G0A1A3ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd2;A2A4A5").
      Proof using EmW Erd Evm2 Ewok GRdec HAC2 HAMF HB2 HBW HCTX2 HCW2 HF HFP2 HFPW HFRESH HFpre HGRblock HGRceil HGRfp HGRimg HGRmaps HGRpage HI HI2 HIMG2 HKEYS HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr HY Haddr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom HsmF Htp K2 MF STK VF ZF bv0 bv1 rv0 rv1.
        exists (L_am_ok IEC_U), (JL_am_ok segsU C_U X R U (mkMA s L) Kc), rho'.
        split; [left; reflexivity|]. split; [exact agree_vals_rho'|]. split; [exact smatch_ok|].
        cbn [w_tr w_cfg fst snd cfg_model].
        exists (mkMA t2 L2), mnew. cbn [ma_s ma_L].
        pose proof HAMF as (AF & US & UB). pose proof HNOTX as (M1 & M2).
        pose proof HF as (F2 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
        split; [cbn [rw rho']; unfold V_RES; rewrite U110, Haddr; unfold AREA_HDR; lia|].
        split; [unfold MInvIR; cbn [rm rho']; rewrite rdG, wokG, Evm2; exact minvI2|].
        split.
        { split; [exact HX2|]. split; [exact F5|]. split; [exact AF|]. split; [repeat split; assumption|].
          split; [exact US|]. split; [exact UB|]. cbn [ma_s ma_L]. split; [exact HKEYS | exact HLext]. }
        split; [exact M1|]. split; [exact M2|]. split; [exact kept2|]. split; [exact maps_kept2|]. split; [exact canary_kept2|].
        split; [exists ktr; exact HY | exact K2].
      Qed.
    End FinalLeaf.

  Theorem c2e_sound : ltac2:(tb__ "0|7|
S16S148S2eS115S51Vok;R3S112S12bS51S52Vrho;S139S51Sc2SfcVX;VR;VU;Sf4Vs;VL;A2VKc;A8R1A5Lw';A4Se7R2A1S8aQ40M0A1M1S6VGR;S8cG0R1A2M2A1A1S3SfS8aQ8M3A1M4A1M5S27R5R2A2VmW;R2A1A3F_;Fx;G1S4S56Vpz;G2A2S58G2S57Vpz;Z1000A2A2A2S3G5S27R6R2A2S14G4S8bG3Z0A2A2A3F_;Fx;S2aS51R5Sd2S51ScfSecSe4A1A3ScSeSf6A1M6Sf1Vtr;Sf2R6Vmd2;A2A4A4S113S51Vok;R8ScG6Sf1Vtr;Sf2R7Vmd2;A2A4A4F_;F_;F_;F_;F_;FrhoE;Fms1;Fn;").
  Proof using EmW Erd Evm2 Ewok GRdec HAC2 HAMF HB2 HBW HCTX2 HCW2 HF HFP2 HFPW HFRESH HFpre HGRblock HGRceil HGRfp HGRimg HGRmaps HGRpage HI HI2 HIMG2 HKEYS HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HOK HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr HY Haddr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom Htp K2 STK.
    intros n ms1 rhoE HQ VE ME ZE HE.
    pose proof (alloc_meta_run_P (segF bT) ok (Kexact tr md2) rhoE (ok_frame_exact ok Kc tr md2 HOK K2)) as RUN.
    refine (RUN n _ (tr, mkCfg ms1 md2) (conj HE (conj eq_refl eq_refl))).
    intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape (segF bT)) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LF bT) by (rewrite <- LF_eq; unfold LF0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    rewrite NXF in Hag3.
    apply HQ. apply (post_ok2 ms3 rhoF).
    - exact (valF_ext _ _ VE Hag3).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ME x Hx).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ZE x Hx).
    - exact Hsm3.
  Qed.

  Theorem c2e_soundK : ltac2:(tb__ "0|8|
S16S148S2eS112S12bS51S52Vrho;SbS10S2bS12cA2M0ScS2bS12cS138SfcA1S13bS51Sc2VX;VR;VU;Sf4Vs;VL;A2VKc;A7A4S11G0A1A3R1A5S3Sf8Sf3S116R2A1A1Vmd2;A3S113S51Vok;R6R3A4F_;F_;Fw';Se7R2A1S8aQ40M1A1M2S6VGR;S8cG1R1A2M3A1A1S3SfS8aQ8M4A1M5A1M6S27R5R2A2VmW;R2A1A3F_;Fx;G2S4S56Vpz;G3A2S58G3S57Vpz;Z1000A2A2A2S3G6S27R6R2A2S14G5S8bG4Z0A2A2A3F_;Fx;S2aS51R5Sd2S51ScfSecSe4A1A3ScSeSf6A1M7Sf1Vtr;Sf2R6Vmd2;A2A4A4S113S51Vok;R8ScG7Sf1Vtr;Sf2R7Vmd2;A2A4A4F_;F_;F_;F_;F_;FrhoE;Fms1;Fn;").
  Proof using EmW Erd Evm2 Ewok GRdec HAC2 HAMF HB2 HBW HCTX2 HCW2 HF HFP2 HFPW HFRESH HFpre HGRblock HGRceil HGRfp HGRimg HGRmaps HGRpage HI HI2 HIMG2 HKEYS HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HOK HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr HY Haddr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom Htp K2 STK.
    intros n ms1 rhoE HQ VE ME ZE HE.
    pose proof (alloc_meta_run_P (segF bT) ok (Kexact tr md2) rhoE (ok_frame_exact ok Kc tr md2 HOK K2)) as RUN.
    refine (RUN n _ (tr, mkCfg ms1 md2) (conj HE (conj eq_refl eq_refl))).
    intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape (segF bT)) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LF bT) by (rewrite <- LF_eq; unfold LF0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    rewrite NXF in Hag3.
    apply (HQ (tr, mkCfg ms3 md2)); [|reflexivity]. apply (post_ok2_only ms3 rhoF).
    - exact (valF_ext _ _ VE Hag3).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ME x Hx).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ZE x Hx).
    - exact Hsm3.
  Qed.

  Theorem c2e_ex : ltac2:(tb__ "0|8|
S148S2eSe7R1A1S8aQ40M0A1M1S6VGR;S8cG0R1A2M2A1A1S3SfS8aQ8M3A1M4A1M5S27R4R2A2VmW;R2A1A3F_;Fx;G1S4S56Vpz;G2A2S58G2S57Vpz;Z1000A2A2A2S3G5S27R5R2A2S14G4S8bG3Z0A2A2A3F_;Fx;S2aS51R4Sd2S51ScfSecSe4A1A3ScSeSf6A1M6Sf1Vtr;Sf2R5Vmd2;A2A4A4S114S51S112S3S112R1ScG6Sf1Vtr;Sf2R7Vmd2;A2A4A3Lw;S112S4S12bS51S52Vrho;SbS10S2bS12cA2M7ScS2bS12cS138SfcA1S13bS51Sc2VX;VR;VU;Sf4Vs;VL;A2VKc;A7A4S11G7A1A3R1A5S3Sf8Sf3S116R1A1A1Vmd2;A3A2Lw';A3F_;F_;F_;F_;FrhoE;Fms1;").
  Proof using EmW Erd Evm2 Ewok GRdec HAC2 HAMF HB2 HBW HCTX2 HCW2 HF HFP2 HFPW HFRESH HFpre HGRblock HGRceil HGRfp HGRimg HGRmaps HGRpage HI HI2 HIMG2 HKEYS HL2 HLG2 HLctx HLext HLfp HLold HLsec HLub HMI HMW2 HNOTX HPN HPZ HRES2 HUB2 HV183 HV184 HV2 HX2 HXr HY Haddr Hav Hav_rd Hbrk2 Hev Hgd Hgd_rd Hmnew HpzR Hrom Htp K2 STK.
    intros ms1 rhoE VE ME ZE HE w ->.
    destruct (alloc_meta_run_ex_P (segF bT) (Kexact tr md2) rhoE (tr, mkCfg ms1 md2) (conj HE (conj eq_refl eq_refl)))
      as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
    destruct (Posts_am_P_shape (segF bT)) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
    assert (ELF3 : lf_state L3 = LF bT) by (rewrite <- LF_eq; unfold LF0; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
    rewrite NXF in Hag3.
    exists (tr, mkCfg ms3 md2). split; [exact ST3|]. split; [|reflexivity].
    apply (post_ok2_only ms3 rhoF).
    - exact (valF_ext _ _ VE Hag3).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ME x Hx).
    - intros x Hx. destruct Hag3 as (_ & _ & M). rewrite <- (M x). exact (ZE x Hx).
    - exact Hsm3.
  Qed.
End C2E.

End InstX.

End Mal_ameta_C2E.

Module Mal_ameta_R78.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReabKit OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G1.Mal_ameta_I.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapEx.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac cells_inside_tac := unfold cells_inside; repeat constructor; cbn; lia.
Ltac zlit := repeat (rewrite (Z.mod_small _ (2 ^ 64)) by lia).

Section InstX.

Variables (s : astate) (L : layout) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variable rho : valuation.
Hypothesis HI : ltac2:(tb__ "0|0|
Sa5VX;VR;VU;Vs;A4").
Hypothesis HXr : xraw X s.
Variables (rd0 : word -> option byte) (wok0 : word -> bool) (vm : VmMaps).
Hypothesis HMI : ltac2:(tb__ "0|0|
S146Sc2VX;VR;VU;Sf4Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Local Notation "§4§ h__" := (h__ s L X R U rd0 wok0 vm HMI) (at level 10, h__ global).
Local Abbreviation HL := (§4§ U.Mal_ameta__G1.Mal_ameta_I.HL).
Local Abbreviation HV := (§4§ U.Mal_ameta__G1.Mal_ameta_I.HV).
Local Abbreviation HLG := (§4§ U.Mal_ameta__G1.Mal_ameta_I.HLG).
Local Abbreviation Hctx := (§4§ U.Mal_ameta__G1.Mal_ameta_I.Hctx).
Local Abbreviation HB := (§4§ U.Mal_ameta__G1.Mal_ameta_I.HB).
Variables (gd : Z) (evb avb : list byte).
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis Hev : length evb = 4%nat.
Hypothesis Hav : length avb = 8%nat.
Local Abbreviation zA := (@U.Mal_ameta__G1.Mal_ameta_I.zA L).
Local Abbreviation initZ := (@U.Mal_ameta__G1.Mal_ameta_I.initZ s).
Local Abbreviation brkZ := (@U.Mal_ameta__G1.Mal_ameta_I.brkZ s L).
Local Notation "§5§ h__" := (h__ s L rho gd evb avb) (at level 10, h__ global).
Local Abbreviation rho1 := (§5§ U.Mal_ameta__G1.Mal_ameta_I.rho1).
Local Notation "§6§ h__" := (h__ s L rho gd evb avb Hgd Hev Hav) (at level 10, h__ global).
Local Abbreviation rw1_low := (§6§ U.Mal_ameta__G1.Mal_ameta_I.rw1_low).
Local Abbreviation ev1 := (§5§ U.Mal_ameta__G1.Mal_ameta_I.ev1).
Local Abbreviation ze_v := (§5§ U.Mal_ameta__G1.Mal_ameta_I.ze_v).
Local Abbreviation ev173 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev173).
Local Abbreviation ev176 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev176).
Local Abbreviation ev177 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev177).
Local Abbreviation ev184 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev184).
Local Abbreviation ev185 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev185).
Local Abbreviation ev186 := (§6§ U.Mal_ameta__G1.Mal_ameta_I.ev186).
Variable mW : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S3S8aQ40A1SfS8aQ8A1A1F_;Vrd0;SefS51VmW;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S3S8aQ40A1SdF_;Vwok0;Sf0S51VmW;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hgd_rd : ltac2:(tb__ "0|0|
Sc9Sc3Vrd0;S8aQ40A1S13L_;A2ScbSc2A1U8Vgd;A4").
Hypothesis Hev_rd : ltac2:(tb__ "0|2|
S16S135R1U4A2S3SfS8aQ8M0A1M1A1SefS51VmW;S8bQ40S57SccSc2A1S5bR2A1A2A2A3S14G1S122G1R2Vevb;S8bG0Z0A2A4A2A3F_;Fj;").
Hypothesis Hav_rd : ltac2:(tb__ "0|2|
S16S135R1U8A2S3SfS8aQ8M0A1M1A1SefS51VmW;S8bQ40S57ScaSc2A1S5bR2A1A2A2A3S14G1S122G1R2Vavb;S8bG0Z0A2A4A2A3F_;Fj;").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51VmW;A2Sf0S51VmW;A2A2").
Local Abbreviation HMI0 := (@U.Mal_ameta__G1.Mal_ameta_I.HMI0 s L X R U rd0 wok0 vm HMI mW Erd Ewok).
Local Notation "§7§ h__" := (h__ s L X R U rho rd0 wok0 vm HMI gd evb avb Hgd Hev Hav mW Erd Ewok ms Hrom) (at level 10, h__ global).
Local Abbreviation hold_got := (§7§ U.Mal_ameta__G1.Mal_ameta_I.hold_got).
Local Abbreviation hold_guard := (@U.Mal_ameta__G1.Mal_ameta_I.hold_guard s L rho rd0 gd evb avb Hgd Hev Hav mW Erd ms Hrom Hgd_rd).
Local Abbreviation hold_pgsz := (§7§ U.Mal_ameta__G1.Mal_ameta_I.hold_pgsz).
Local Abbreviation hold_auxvp := (@U.Mal_ameta__G1.Mal_ameta_I.hold_auxvp s L rho gd evb avb Hgd Hev Hav mW ms Hrom Hav_rd).
Hypothesis Htp : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S26Vrho;P18A2S8bG0ScdSc2A1A2A3").
Local Abbreviation ev_tp := (@U.Mal_ameta__G1.Mal_ameta_I.ev_tp s L rho gd evb avb Hgd Hev Hav Htp).
Local Abbreviation hold_sec := (§7§ U.Mal_ameta__G1.Mal_ameta_I.hold_sec).
Local Abbreviation hold_brkE := (§7§ U.Mal_ameta__G1.Mal_ameta_I.hold_brkE).
Local Abbreviation hold_ctxB := (§7§ U.Mal_ameta__G1.Mal_ameta_I.hold_ctxB).
Local Abbreviation area_R := (@U.Mal_ameta__G1.Mal_ameta_I.area_R s L X R U rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).
Local Abbreviation sp0 := (@U.Mal_ameta__G1.Mal_ameta_I.sp0 rho).
Local Abbreviation D0 := (@U.Mal_ameta__G1.Mal_ameta_I.D0 rho).
Local Abbreviation rng_stk := (@U.Mal_ameta__G1.Mal_ameta_I.rng_stk s L rho gd evb avb Hgd Hev Hav mW).
Variables (tr : list event) (md : Model).
Hypothesis EmW : ltac2:(tb__ "0|0|
S3S8aQ40A1SfS8aQ8A1A1F_;VmW;S27Vrho;A1A3").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S2aS51Vrho;S13cSfcA1ScSeSf6A1Sf1Vtr;Sf2Vms;Vmd;A2A4A4").

Hypothesis Htop : ltac2:(tb__ "0|0|
S15cSf4Vs;VL;A2Vrho;A2").
Local Abbreviation agree1 := (@U.Mal_ameta__G1.Mal_ameta_I.agree1 s L rho gd evb avb Hgd Hev Hav mW EmW).
Local Abbreviation zr1_var := (§5§ U.Mal_ameta__G1.Mal_ameta_I.zr1_var).
Local Abbreviation map_region_where := (@U.Mal_ameta__G1.Mal_ameta_I.map_region_where s L X R U HI rd0 wok0 vm HMI gd evb avb Hgd Hev Hav).

Section Cut78r.
  Hypothesis Hhd : ltac2:(tb__ "0|0|
S3SfS64A1S6eVs;A1S17S64A1A3").
  Hypothesis Hcnt : st_avail_meta_count s = 0.
  Hypothesis Hac : st_avail_meta_area_count s = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S3S68S6dVs;A1S80A3").
  Hypothesis Hinit : st_init_done s = true.

  Variable msC : machine_state.
  Hypothesis HsmC : ltac2:(tb__ "0|0|
S2aS51S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7Sd2S51ScfSd8A3ScSeSf6A1Sf1Vtr;Sf2VmsC;Vmd;A2A4A4").
  Variable Kc : ltac2:(tb__ "0|0|
SeSf6A1Sf8OF_;F_;").
  Hypothesis HKc : Kc tr md.
  Hypothesis Evm : ltac2:(tb__ "0|0|
S3SfaVvm;Sf7Vmd;A1A3").
  Variable ok : world -> Prop.
  Hypothesis HOK : ltac2:(tb__ "0|0|
S15aS51Vok;VKc;A3").

  Definition img_reservedX (vmz : VmMaps) : Prop := ltac2:(tb__ "0|4|
S0S4S56Sc6Sc2A1R1A2S58R1Sc5Sc2A1A2A2S5S10S8aQ40M0A1M1G1A2M2G2S4S8dG2R1Sf9Vvmz;A1A3S4S56S8cG0S15G1G1R1A3A2M3R3A2S58R3S57G3S8cG0S18G1G1R1A3A2A2A2A2A2Le;A2F_;Fx;").
  Hypothesis HIR : img_reservedX (m_vmmaps md).

  Hypothesis STK : ltac2:(tb__ "0|3|
S4S56Z0S57S119Vrho;A1M0S118Vrho;A1M1A2M2A2S4S56Sc4VL;A1G2A2S4S56G0S5aZ2Z40A2A2S56G1S62SddA1A2A2A2A2").

  Definition L78 : sstate := ltac2:(tb__ "0|0|
S14eS8fS14dS14fSd2S51ScfSd8A3S14cA2SdcSd8A1A3A1").
  Definition LRF : sstate := ltac2:(tb__ "0|0|
S14eS8fS14dS14fSd2S51ScfSdbA3S14cA2SdcSdbA1A3A1").
  Lemma Pre_fail_eq : ltac2:(tb__ "0|0|
S3S2bSd2S51ScfSdbA3S156S100S157A2A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma L78_misc : ltac2:(tb__ "0|1|
S4S3S0S37S100A1Z21ea0A3S4S3S23S28S100Z11A2S1fZdeA1A3S4S3S23S28S100ZaA2S1fZ0A1M0A3S4S3S23S28S100ZbA2Sd9A3S4S3S23S28S100ZcA2G0A3S4S3S23S28S100ZdA2S1fZ22A1A3S4S3S23S28S100ZeA2S1fSd7A1A3S4S3S23S28S100ZfA2G0A3S3S1S36S100A1Sd1A3A2A2A2A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma L78_ecall : ltac2:(tb__ "0|0|
S3SfS129A1S150S51S37S100A1A2S14S129S12aA2A3").
  Proof using . vm_cast_no_check (@eq_refl (option instr) (Some Ecall)). Qed.

  Definition OKP : assn := ltac2:(tb__ "0|3|
S112S5S8aQ40M0A1M1G1S5S2eS2eS4S2dSd1S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R1A3S4S141S8bG0Z0A2Vmd;S24R1Sd9A2M2R2A4S145S51S144S11aVtr;SfbS142Sf7Vmd;A1G2R2A3Vmd;A2A2A1S154S100A1S155R1Sd1R2R2S140G2A1A5R3A5A2A2LrhoL;A2La;A2Lw;").

  Definition O_ctx78 : sobj := ltac2:(tb__ "0|1|
Se2ScfS1fZ0A1M0Sd0Pb0A1G0G0Sd0Pb8A1Sd0Pb9A1Sd0PbaA1Sd0Pb1A1A9").
  Definition O_brkD : sobj := ltac2:(tb__ "0|0|
Sd3ScfS1fSd7A1A2").
  Definition O_errF : sobj := ltac2:(tb__ "0|1|
S30S22P18A1S1fNa4A1M0S1fNa0A1SbS20S21G0Z4S1fZcA1A3S11S20A1A3S2fA5").
  Definition UNCH_R : list sobj := ltac2:(tb__ "0|0|
SbS1eSdfScfA1SbS1eSe0SbS1eSdeScfA1SbS1eSe1ScfA1SbS1eSd5ScfSd0PafA1Z1A3SbS1eS109SbS1eS108S11S1eA1A3A3A3A3A3A3A3").
  Definition CHG_R : list sobj := [O_errF].
  Definition stkR_cells : list cell := ltac2:(tb__ "0|2|
SbS20S21S1fN90A1Z8M0S1fZ1000A1M1A3SbS20S21S1fN88A1G0S1fZ21ec4A1A3SbS20S21S1fN78A1G0S22P29A1A3SbS20S21S1fN70A1G0S1fSd7A1A3SbS20S21S1fN68A1G0S1fZ5a3c8A1A3SbS20S21S1fN60A1G0Sd0PadA1A3SbS20S21S1fN58A1G0S29S128S1fZ2A1Sd0Pb8A1A3A3SbS20S21S1fN50A1G0G1A3SbS20S21S1fN48A1G0S1fZ20e08A1A3SbS20S21S1fN8A1G0S22PbA1A3SbS20S21S1fN10A1G0S22P1cA1A3SbS20S21S1fN18A1G0S22P1dA1A3SbS20S21S1fN20A1G0S22P26A1A3SbS20S21S1fN28A1G0S22P27A1A3SbS20S21S1fN30A1G0S22P28A1A3SbS20S21S1fN38A1G0Sd0PaeA1A3S11S20A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Definition OBJ_R : list sobj := ltac2:(tb__ "0|1|
SbS1eSd6S107A1S12S1eS124S1eU4M0SffA3S12S1eS103S125S1eG0SffA3A3A3A3").
  Lemma LRF_objs : ltac2:(tb__ "0|0|
S3SeS1eA1S32S102A1S105A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma LRF_misc : ltac2:(tb__ "0|0|
S4S3S0S37S102A1Z20ec8A3S4S3S1S36S102A1Sd1A3S4S3SeS23A1S48S102A1S55A3S4S3S46S47S102A1S33A3S4S3SfS23A1S49S102A1S17S23A1A3S3S23S28S102ZaA2S1fZ0A1A3A2A2A2A2A2").
  Proof using . vm_compute. repeat split; reflexivity. Qed.
  Lemma LRF_cs : ltac2:(tb__ "0|0|
S0S4S56Z1R1A2S56R1Z1fA2A2S3SdS53S59R2A1A1S13A3S3S23S28S102R3A2S54S59R3A1A1A3F_;F_;Fz;").
  Proof using Hav Hev Hgd.
    intros z Hz Hcs.
    pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || sv_eqb (reg_sv LRF z) (pre_reg (Z.to_nat z)))%bool 1 31
                  ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
    cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX. apply sv_eqb_sound in XX. exact XX.
  Qed.

  Lemma Pre78r_objs : ltac2:(tb__ "0|1|
S3SeS1eA1S32Sd2S51ScfSd8A3A1SbS1eSd6SdaA1S12S1eS124S1eU4M0SffA3S12S1eSbS1eSd4S11S1eA1A3S125S1eG0SffA3A3A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.

  Lemma block_vs_ctxR b n a : ltac2:(tb__ "0|1|
S8dS10S0S0A2ScS0S0Vb;Vn;A4Sc8VL;Vs;A2A3S4S56Vb;Va;A2S58Va;S57Vb;Vn;A2A2A2S6S4S56Sa3VL;A1M0Va;A2S58Va;S57G0Sa9A2A2A2A1F_;F_;").
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
S2dSd1S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoF;A3").
    Hypothesis HsmF : ltac2:(tb__ "0|0|
S2aS51VrhoF;S102ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd;A2A4A4").

    Lemma HromF : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.
    Lemma HroF : ro_clear segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmF)))))). Qed.
    Lemma HOF : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3S105A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). cbn [fst snd cfg_ms] in Hall. rewrite LRF_objs in Hall. exact Hall. Qed.
    Lemma HfrF : ltac2:(tb__ "0|0|
S8aQ40A1S43VrhoF;S105R1A3S3SfS8aQ8A1A1S149VmsF;R2A2S27VrhoF;R2A2A3F_;Fa;").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms] in Hfr. rewrite LRF_objs in Hfr. exact Hfr. Qed.
    Lemma rmF a : ltac2:(tb__ "0|0|
S3SfS8aQ8A1A1S27VrhoF;Va;A2VmW;Va;A1A3"). Proof using HagF. destruct HagF as (_ & _ & M). rewrite <- M. reflexivity. Qed.
    Lemma F_pc : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S14aVmsF;A1S8bG0Z20ec8A2A3").
    Proof using HsmF. pose proof HsmF as (_ & Hpc & _). destruct LRF_misc as (Mpc & _). rewrite Mpc in Hpc. exact Hpc. Qed.
    Lemma F_pend : ltac2:(tb__ "0|1|
S3SfS8aQ40A1M0A1S14bVmsF;A1S17G0A1A3"). Proof using HsmF. exact (proj1 (proj2 (proj2 HsmF))). Qed.
    Lemma F_halt : model_idle md. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 HsmF)))). Qed.
    Lemma F_regs : ltac2:(tb__ "0|0|
S44VrhoF;S102VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & Hr & _). exact Hr. Qed.
    Lemma F_fregs : ltac2:(tb__ "0|0|
S3eVrhoF;S102VmsF;A3"). Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & Hf & _). exact Hf. Qed.
    Lemma F_fcsr : ltac2:(tb__ "0|0|
S3cVrhoF;S33VmsF;A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & Hc & _). destruct LRF_misc as (_ & _ & _ & Mfc & _). rewrite Mfc in Hc. exact Hc. Qed.
    Lemma F_resv : ltac2:(tb__ "0|0|
S45VrhoF;S17S23A1VmsF;A3").
    Proof using HsmF. pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). destruct LRF_misc as (_ & _ & _ & _ & Mrs & _). rewrite Mrs in Hv. exact Hv. Qed.

    Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S161VrhoF;VmsF;SffS103A4").

    Lemma evM64 m : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S24S117Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7S1fSd7A1A2S8bG0S11cVs;VL;A2A2A3").
    Proof using Hbrk. unfold brkZ. rewrite Hbrk. apply bv_eq. reflexivity. Qed.
    Lemma KU_entry : ltac2:(tb__ "0|0|
S121S1eS2cS51S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7S151Vms;VmW;A2A3SffA3").
    Proof using Erd Ewok HMI Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom.
      unfold UNCH_R. pose proof (hold_sec) as HS. unfold initZ in HS. rewrite Hinit in HS.
      constructor; [apply hold_got|]. constructor; [apply hold_guard|]. constructor; [apply hold_auxvp|]. constructor; [apply hold_pgsz|].
      constructor; [exact HS|].
      constructor; [apply hold_ctxB; [rewrite Hhd; reflexivity | apply ev176 | rewrite Hcnt; reflexivity | rewrite Hac; reflexivity | apply ev184 | apply ev185 | apply ev186 | apply ev177]|].
      constructor; [apply hold_brkE; apply evM64|]. constructor.
    Qed.
    Lemma KU_leaf : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3SffA3").
    Proof using HsmF.
      pose proof HOF as H. unfold OBJ_R in H. apply Forall_inv_tail in H.
      apply Forall_app in H as [H1 H]. apply Forall_app in H as [_ H2]. unfold UNCH_R. cbn [firstn skipn UNCH_R] in H1, H2.
      repeat (apply Forall_cons_iff in H1 as [? H1]). repeat (apply Forall_cons_iff in H2 as [? H2]). repeat (constructor; [assumption|]). constructor.
    Qed.
    Lemma KC_leaf : ltac2:(tb__ "0|0|
S121S1eS2cS51VrhoF;VmsF;A3S103A3").
    Proof using HsmF. pose proof HOF as H. unfold OBJ_R in H. apply Forall_inv_tail in H. apply Forall_app in H as [_ H]. apply Forall_app in H as [H _]. exact H. Qed.
    Lemma Kvars : ltac2:(tb__ "0|0|
S3SdS8eS1eS42Sd1A1S12S1eSffS103A3A3S13A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kcov : ltac2:(tb__ "0|0|
S3SdS8eS1eS160SffA3S13A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Klits : ltac2:(tb__ "0|0|
S3SdS8eS1eS162S12S1eSffS103A3A3S13A3"). Proof using . vm_compute. reflexivity. Qed.
    Lemma Kdunk : ltac2:(tb__ "0|1|
S3SdS8eS1eS1eS34SdLx;S41R1A1S13S19S19S1S19Ll;M0G0S0S23SeS10S0S0A2A1SeS4aA1S19Ltmpl;Lflds;Lcnt;Lesz;X34x6Lo;S12S1eSffS103A3A3S13A3"). Proof using . reflexivity. Qed.

    Lemma KIT_unch : ltac2:(tb__ "0|2|
S1eS0S8dS1eR2SffA3S4S56S15S0S0S25VrhoF;R3A2M0A3R2A2S58R2S18S0S0G0A3A2A2S4S3SfS8aQ8A1A1SefS51S11dS8bQ40R3A2M1A3SefS51VmW;G1A3A3S3SdSf0S51S11dG1A3Sf0S51VmW;G1A3A3A2F_;F_;Fx;Fo;").
    Proof using Erd Ewok HMI Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF. exact (ReabKit.unch_same segsU (rho1 mW) rhoF ms msF mW Hrom HromF UNCH_R CHG_R KU_entry KU_leaf AM_NEXT HagF Kvars Kcov Klits Kdunk). Qed.
    Lemma KIT_chgb : ltac2:(tb__ "0|3|
S1eS0S8dS1eR2S103A3S4S56S15S0S0S25VrhoF;R3A2M0A3R2A2S58R2S18S0S0G0A3A2A2S4S3SdSf0S51S11dS8bQ40M1R3A2A3S13A3S5S8aQ8A1M2G2S3SfG2A1SefS51S11dS8bG1R4A2A3S14G2R1A2A3Lb;A2A2F_;F_;Fx;Fo;").
    Proof using HsmF. exact (ReabKit.chg_byte segsU rhoF msF HromF UNCH_R CHG_R KC_leaf Kdunk). Qed.

    Definition touched (x : Z) : Prop := 237612 <= x < 237616.
    Lemma touched_dec x : ltac2:(tb__ "0|1|
S147S11eVx;A1M0S6G0A1A2"). Proof using . unfold touched. apply range_dec. Qed.
    Lemma evF_lit z : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S24VrhoF;S1fVz;A1A2S8bG0Vz;A2A3"). Proof using . reflexivity. Qed.
    Lemma CHG_ranges : ltac2:(tb__ "0|1|
S3SeS10S0S0A2M0A1S123S1eG0S25VrhoF;A1S103A4SbG0ScS0S0Z3a02cZ3a030A4S11G0A1A3A3").
    Proof using HagF Hav Hev Hgd Htp.
      cbn [map CHG_R]. unfold O_errF. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
      rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (SVar 24) HagF eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.
    Lemma UNCH_rangesF : ltac2:(tb__ "0|1|
S3SeS10S0S0A2M0A1S123S1eG0S25VrhoF;A1SffA4SbG0ScS0S0Z28d50Z28d58A4SbG0ScS0S0Z5a338Z5a340A4SbG0ScS0S0Z5a360Z5a368A4SbG0ScS0S0Z5a388Z5a390A4SbG0ScS0S0Z5a3d0Z5a3dcA4SbG0ScS0S0Z5a3e0Z5a420A4SbG0ScS0S0Z5a768Z5a770A4S11G0A1A3A3A3A3A3A3A3A3").
    Proof using HagF Hav Hev Hgd.
      cbn [map UNCH_R]. unfold O_got, O_guard, O_auxvp, O_pgsz, O_sec, O_ctx78, O_ctxB, O_brkD, O_brk. cbn [am_got am_libc am_ctx AM_P].
      unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !evF_lit, !soff_lit_small by lia. rewrite !u64 by lia.
      rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoF (v 173) HagF eq_refl), ev173. rewrite !u64 by (cbn; lia). reflexivity.
    Qed.
    Lemma in_ranges_cases x : ltac2:(tb__ "0|1|
S4S56Z0Vx;A2S58Vx;S5aZ2Z40A2A2A2S153VrhoF;S12S1eSffS103A3S8bQ40Vx;A2A3S7S5S1eS1eS4S8dS1eR1SffA3S4S56S15S0S0S25VrhoF;R1A2M0A3Vx;A2S58Vx;S18S0S0G0A3A2A2A2Lo;A2S11eVx;A1A2F_;F_;").
    Proof using HagF Hav Hev Hgd Htp.
      intros Hx (o & Ho & RR). rewrite u64 in RR by lia. apply in_app_iff in Ho as [Ho|Ho]; [left; exists o; auto|right].
      pose proof (in_map (obj_range rhoF) _ _ Ho) as M. rewrite CHG_ranges in M. unfold touched.
      destruct M as [E|[]]; rewrite <- E in RR; cbn [fst snd] in RR; lia.
    Qed.
    Lemma touched_in x : ltac2:(tb__ "0|1|
S11eVx;A1S5S1eS1eS4S8dS1eR1S103A3S4S56S15S0S0S25VrhoF;R1A2M0A3Vx;A2S58Vx;S18S0S0G0A3A2A2A2Lo;A2F_;").
    Proof using HagF Hav Hev Hgd Htp.
      intros T. unfold touched in T. exists O_errF. split; [left; reflexivity|].
      pose proof (f_equal (fun l => nth 0 l (0, 0)) CHG_ranges) as CR. cbn [nth map CHG_R] in CR. rewrite CR. cbn [fst snd]. lia.
    Qed.

    Let bv1 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51S11dA2Sf0S51S11dA2A2").
    Let rv1 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51S11dA2S8aQ40A1S13L_;A2").
    Let rv0 : byteview := ltac2:(tb__ "0|0|
Sc3SefS51VmW;A2S8aQ40A1S13L_;A2").

    Theorem V1 : ltac2:(tb__ "0|1|
S0S4S56Z0R1A2S58R1S5aZ2Z40A2A2A2S6S11eR2A1A1S4S3SfS0A1M0Vbv1;R3A1Vbv0;R3A1A3S3G0Vrv1;R3A1Vrv0;R3A1A3A2F_;F_;Fx;").
    Proof using Erd Ewok HMI Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp.
      intros x Hx NT.
      assert (EQ : Glue.rd_of segsU mF (Z_to_bv 64 x) = Glue.rd_of segsU mW (Z_to_bv 64 x) /\ Glue.wok_of segsU mF (Z_to_bv 64 x) = Glue.wok_of segsU mW (Z_to_bv 64 x)).
      { destruct (in_ranges_dec rhoF (UNCH_R ++ CHG_R) (Z_to_bv 64 x)) as [IN|OUT].
        - destruct (in_ranges_cases x Hx IN) as [(o & Ho & RR)|T]; [exact (KIT_unch o x Ho RR) | exfalso; exact (NT T)].
        - unfold mF. unfold Glue.rd_of, Glue.wok_of. rewrite (ReabKit.kit_out rhoF msF UNCH_R CHG_R _ OUT), rmF. auto. }
      destruct EQ as [E1 E2]. unfold bv1, bv0, rv1, rv0, byteview_of. rewrite E1, E2. auto.
    Qed.
    Theorem VM : ltac2:(tb__ "0|0|
S0S4S56Z0R1A2S58R1S5aZ2Z40A2A2A2S11eR2A1SacVL;Vs;R3A3S6S3SfS0A1Vbv1;R4A1S17S0A1A3A1F_;F_;F_;Fx;").
    Proof using HagF Hav Hev Hgd HsmF Htp.
      intros x Hx T _. destruct (touched_in x T) as (o & Ho & RR). destruct (KIT_chgb o x Ho RR) as [W [b Hb]].
      unfold bv1, byteview_of. replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      cbn [andb]. rewrite W, Hb. discriminate.
    Qed.

    Lemma Hctx' : ly_ctx L = 369616. Proof using HMI. exact Hctx. Qed.
    Theorem VIN : ltac2:(tb__ "0|0|
S93S8dS93R1S12S93S9aVs;A1S137Vs;A1A3A3S164VL;S11eR2A3Sa2VL;Vbv1;R3A3F_;F_;Fc;").
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
S146Sc2VX;VR;VU;Sf4Vs;VL;A2SefS51S11dA2Sf0S51S11dA2Vvm;A8").
    Proof using Erd Ewok HI HMI HXr Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF Htp bv0 rv0.
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
SdS8aQ40A1L_;S1aS60Z64M0S2Vj;A1M1A2S61G1Z84A2A2S24VrhoF;S28S102S5cG1G0A2A2A2S26Vrho;Vj;A2Xdx2").
    Definition rho' : valuation := ltac2:(tb__ "0|0|
S3fS120S35VrhoF;A1S11dA3").
    Lemma rw'_low j : ltac2:(tb__ "0|0|
S12fVj;P64A2S3S8aQ40A1S120Vj;A1S26Vrho;Vj;A2A3F_;").
    Proof using Hav Hev Hgd. intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia). reflexivity. Qed.
    Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S12dS52Vrho;S11fA3").
    Proof using HagF Hav Hev Hgd.
      split; [intros j Hj; cbn [rw rho']; symmetry; apply rw'_low; exact Hj|].
      intros l. cbn [rl rho']. destruct HagF as (_ & HL2 & _). rewrite <- (HL2 l). reflexivity.
    Qed.
    Lemma rwF_low j : ltac2:(tb__ "0|0|
S12fVj;PaaA2S3S8aQ40A1S26VrhoF;Vj;A2S26Vrho;Vj;A2A3F_;").
    Proof using HagF Hav Hev Hgd. intros Hj. destruct HagF as (A & _ & _). rewrite <- (A j) by (unfold AM_NEXT; lia). cbn [rho1 rw]. apply rw1_low. exact Hj. Qed.
    Lemma pre_reg_cs z : ltac2:(tb__ "0|1|
S4S56Z1Vz;A2S56Vz;Z1fA2A2S3SdS53S59Vz;A1M0A1S13A3S5S1S1S4S3S23S54G0A1S22R1A1A3S12fR1P64A2A2Lvv;A2F_;F_;").
    Proof using Hav Hev Hgd.
      intros Hr Hcs.
      pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX.
      cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
      destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate. apply Pos.ltb_lt in XX. exists vv. auto.
    Qed.
    Lemma reg_sv_null z : ltac2:(tb__ "0|2|
S4S56Z1Vz;A2S56Vz;Z1fA2A2S3S23S28S13aSfcA1Vz;A2SdS23L_;M0S5fVz;ZaA2S1fZ0A1G0S53S59Vz;A1M1A1S54G1A1S22S130P64S133G1A1A2A1Xdx2Xdx2A3F_;").
    Proof using Hav Hev Hgd.
      intros Hz.
      pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_am_null IEC_U) z)
                     (if (z =? 10) then SLit 0 else if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
      apply sv_eqb_sound in H. exact H.
    Qed.
    Lemma freg_sv_null z : ltac2:(tb__ "0|2|
S4S56Z0M0Vz;A2S56Vz;Z1fA2A2S5S1S1S4S3S23S3dS13aSfcA1Vz;A2S22R1A1M1A3S4S3S23S122S23S59Vz;A1S55S1fG0A1A4G1A3S4S131P3cR1A2S12fR1P64A2A2A2A2Lvv;A2F_;").
    Proof using Hav Hev Hgd.
      intros Hz.
      pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with SVar vv => (60 <=? vv)%positive && (vv <? 100)%positive | _ => false end) 0 32
                    ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
      unfold freg_sv. change (ss_fregs (L_am_null IEC_U)) with pre_fregs.
      destruct (nth (Z.to_nat z) pre_fregs (SLit 0)); try discriminate. apply andb_prop in XX as [X1 X2].
      apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. eexists. split; [reflexivity|]. split; [reflexivity|]. lia.
    Qed.
    Lemma EBs : ltac2:(tb__ "0|1|
S3S8aQ40A1S24S11fS22PaA1M0A2S24VrhoF;G0A2A3").
    Proof using HagF Hav Hev Hgd. cbn [eval rho' rw]. rewrite rw'_low by lia. symmetry. apply rwF_low. lia. Qed.
    Lemma ELs : ltac2:(tb__ "0|0|
S3S0S31S11fS22S158A1A2S31VrhoF;S22PfA1A2A3").
    Proof using HagF Hav Hev Hgd. unfold soff, V_DEPTH. cbn [eval rho' rw]. rewrite rw'_low by lia. rewrite (rwF_low 15) by lia. reflexivity. Qed.
    Lemma RSF : ltac2:(tb__ "0|1|
S3S10S0S0A2S25VrhoF;Sd6S107A1A2ScS0S0S57S119Vrho;A1M0S118Vrho;A1A2G0A4A3").
    Proof using HagF Hav Hev Hgd.
      rewrite (ReabKit.range_ag (rho1 mW) rhoF [O_stk stkR_cells] [] AM_NEXT HagF ltac:(vm_compute; reflexivity) (O_stk stkR_cells) ltac:(left; reflexivity)).
      apply rng_stk.
    Qed.
    Lemma RS' : ltac2:(tb__ "0|1|
S3S10S0S0A2S25S11fS15bS13dA1A2ScS0S0S57S119Vrho;A1M0S118Vrho;A1A2G0A4A3").
    Proof using HagF Hav Hev Hgd. rewrite <- RSF. unfold obj_range, obj_lo_of, obj_hi_of, stack_win, O_stk. cbn [ob_base ob_lo ob_hi]. rewrite EBs, ELs. reflexivity. Qed.

    Theorem smatch_null : ltac2:(tb__ "0|0|
S2aS51S11fS13aSfcA1ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd;A2A4A4").
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
S159S51Sc2Sf4Vs;VL;A2M0G0S27Vrho;A1S11dA6").
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
SfeSf4Vs;VL;A2S27Vrho;A1S11dA3").
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
SfdS51Sc2S27Vrho;A1S11dA4").
    Proof using EmW Erd Ewok HMI Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmF.
      intros x Hx. rewrite <- EmW, !rdG. cbn [mc_chk_guard_got mc_chk_guard C_U] in Hx.
      pose proof (f_equal (fun l => nth 0 l (0, 0)) UNCH_rangesF) as R0. pose proof (f_equal (fun l => nth 1 l (0, 0)) UNCH_rangesF) as R1. cbn [nth map UNCH_R] in R0, R1.
      destruct Hx as [Hx|Hx].
      - refine (proj1 (KIT_unch (O_got AM_P) x _ _)); [left; reflexivity | rewrite R0; cbn [fst snd]; lia].
      - refine (proj1 (KIT_unch O_guard x _ _)); [right; left; reflexivity | rewrite R1; cbn [fst snd]; lia].
    Qed.

    Theorem post_null : ltac2:(tb__ "0|0|
S12bS51S52Vrho;S139S51Sc2SfcVX;VR;VU;Sf4Vs;VL;A2VKc;A8ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd;A2A4A5").
    Proof using EmW Erd Evm Ewok HI HKc HMI HXr Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC HsmF Htp STK bv0 bv1 rv0 rv1.
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
      exists (tr_RES (s0 s) 0 0). pose proof (yields_NB s Hhd Hcnt Hac Hbrk 0 0) as Y.
      unfold r_RES in Y. cbn [Z.eqb] in Y. rewrite (AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) in Y at 2 || rewrite (AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) in Y. exact Y.
    Qed.

    Theorem post_null_only : ltac2:(tb__ "0|1|
S12bS51S52Vrho;SbS10S2bS12cA2M0ScS2bS12cS13aSfcA1S13eS51Sc2VX;VR;VU;Sf4Vs;VL;A2VKc;A7A4S11G0A1A3ScSeSf6A1Sf1Vtr;Sf2VmsF;Vmd;A2A4A5").
    Proof using EmW Erd Evm Ewok HI HKc HMI HXr Hac HagF Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC HsmF Htp STK bv0 bv1 rv0 rv1.
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
      exists (tr_RES (s0 s) 0 0). pose proof (yields_NB s Hhd Hcnt Hac Hbrk 0 0) as Y.
      unfold r_RES in Y. cbn [Z.eqb] in Y. rewrite (AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) in Y at 2 || rewrite (AllocMetaGrow.s0_t X R U s L HI HXr Hhd Hcnt Hac Hbrk Hinit HL) in Y. exact Y.
    Qed.
  End FailLeaf.

  Lemma ok_pframe_exact : ltac2:(tb__ "0|0|
S152S51Vok;S144S11aVtr;Vmd;A2A1A3").
  Proof using HKc HOK.
    destruct HOK as (_ & HP & _). intros rhoX trX msX mdX x8 [-> ->] Hp Ho. exact (HP tr msX md x8 HKc Hp Ho).
  Qed.

  Definition lenZ : Z := ltac2:(tb__ "0|0|
S5dS63Z2S6fVs;A1A2Z1000A2").
  Lemma lenZ_range : ltac2:(tb__ "0|0|
S4S4S56Z2000S101A2S56S101S5aZ2Z30A2A2A2S3S0S5eS101Z1000A2Z0A3A2").
  Proof using HMI Hav Hev Hgd.
    pose proof HB as (_ & SH & _). unfold lenZ. rewrite Z.shiftl_mul_pow2 by lia.
    assert (1 <= 2 ^ st_meta_alloc_shift s <= 2 ^ 34) by (split; [apply Z.pow_le_mono_r with (b := 0) | apply Z.pow_le_mono_r]; lia).
    split; [lia|]. replace (2 * 2 ^ st_meta_alloc_shift s * 4096) with ((2 * 2 ^ st_meta_alloc_shift s) * 4096) by lia. apply Z.mod_mul. lia.
  Qed.
  Lemma LENX_val m : ltac2:(tb__ "0|1|
S3S8aQ40M0A1S24S117Vs;VL;Vrho;Vgd;Vevb;Vavb;Vm;A7Sd9A2S8bG0S101A2A3").
  Proof using HMI Hav Hev Hgd.
    pose proof HB as (_ & SH & _). pose proof lenZ_range as [LR _].
    rewrite (ev1 m LENX) by reflexivity. f_equal. unfold LENX. cbn [zeval zalu]. rewrite ze_v.
    rewrite (zr1_var 184 _ eq_refl).
    assert (P27 : 1 <= 2 ^ st_meta_alloc_shift s <= 2 ^ 34) by (split; [apply Z.pow_le_mono_r with (b := 0) | apply Z.pow_le_mono_r]; lia).
    rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia. rewrite (Z.mod_small (st_meta_alloc_shift s) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (st_meta_alloc_shift s) 64) by lia.
    change (2 mod 2 ^ 64) with 2. change (4096 mod 2 ^ 64) with 4096.
    rewrite !Z.shiftl_mul_pow2 by lia. unfold lenZ. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (2 * _)) by lia. rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Lemma lenZ_u64 : 0 <= lenZ < 2 ^ 64.
  Proof using HMI Hav Hev Hgd. pose proof lenZ_range as [LR _]. lia. Qed.
  Lemma mmap_nZ_lenZ : ltac2:(tb__ "0|0|
S3S0S143S8bQ40S101A2A1S101A3").
  Proof using HMI Hav Hev Hgd.
    pose proof lenZ_range as [LR LA]. unfold mmap_nZ, page_round_up_Z, page_size. rewrite (u64 lenZ lenZ_u64).
    Z.to_euclidean_division_equations; nia.
  Qed.
  Lemma mmap_n_lenZ : ltac2:(tb__ "0|1|
S3S0S8cQ40M0S140S8bG0S101A2A1A2S101A3").
  Proof using HMI Hav Hev Hgd. unfold mmap_n. rewrite mmap_nZ_lenZ. apply u64. exact lenZ_u64. Qed.
  Lemma lenZ_ne0 : Z_to_bv 64 lenZ <> Z_to_bv 64 0.
  Proof using HMI Hav Hev Hgd. intros E. apply (f_equal bv_unsigned) in E. rewrite (u64 lenZ lenZ_u64) in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. pose proof lenZ_range. lia. Qed.

  Lemma grant_misses_image (a lenw : word) : ltac2:(tb__ "0|2|
S141S8bQ40M0Z0A2Vmd;Vlenw;Va;A4S0S4S56Sc6Sc2A1R1A2S58R1Sc5Sc2A1A2A2S6S4S56S8cG0Va;A2M1R2A2S58R2S57G1S8cG0S140Vlenw;A1A2A2A2A2A1F_;Fx;F_;").
  Proof using HIR Hav Hev Hgd.
    intros (_ & _ & _ & Hfree) x Hx Hin. destruct (HIR x Hx) as (e & He & Hex).
    destruct e as [ea esz].
    pose proof (region_free_In _ _ _ _ _ Hfree ltac:(apply in_app_iff; left; exact He)) as OV.
    unfold iv_overlap in OV. cbn [fst snd] in Hex. apply Bool.andb_false_iff in OV.
    destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
  Qed.

  Definition stk78_cells : list cell := ltac2:(tb__ "0|1|
SbS20S21S1fN78A1Z8M0S22P29A1A3SbS20S21S1fN70A1G0S1fSd7A1A3SbS20S21S1fN68A1G0S1fZ5a3c8A1A3SbS20S21S1fN60A1G0Sd0PadA1A3SbS20S21S1fN58A1G0S29S128S1fZ2A1Sd0Pb8A1A3A3SbS20S21S1fN50A1G0S1fZ1000A1A3SbS20S21S1fN48A1G0S1fZ20e08A1A3SbS20S21S1fN8A1G0S22PbA1A3SbS20S21S1fN10A1G0S22P1cA1A3SbS20S21S1fN18A1G0S22P1dA1A3SbS20S21S1fN20A1G0S22P26A1A3SbS20S21S1fN28A1G0S22P27A1A3SbS20S21S1fN30A1G0S22P28A1A3SbS20S21S1fN38A1G0Sd0PaeA1A3S11S20A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
  Lemma L78_objs : ltac2:(tb__ "0|1|
S3SeS1eA1S32S100A1SbS1eSd6S10aA1S12S1eS124S1eU4M0SffA3S12S1eSbS1eSd4S11S1eA1A3S125S1eG0SffA3A3A3A3A3").
  Proof using . vm_compute. reflexivity. Qed.
  Lemma L78_ranges (rhoL : valuation) : ltac2:(tb__ "0|2|
S2dSd1S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoL;A3S3SeS10S0S0A2M0A1S123S1eG0S25VrhoL;A1S32S100A1A4SbG0ScS0S0S57S119Vrho;A1M1S118Vrho;A1A2G1A4SbG0ScS0S0Z28d50Z28d58A4SbG0ScS0S0Z5a338Z5a340A4SbG0ScS0S0Z5a360Z5a368A4SbG0ScS0S0Z5a388Z5a390A4SbG0ScS0S0Z3a02cZ3a030A4SbG0ScS0S0Z5a3d0Z5a3dcA4SbG0ScS0S0Z5a3e0Z5a420A4SbG0ScS0S0Z5a768Z5a770A4S11G0A1A3A3A3A3A3A3A3A3A3A3F_;").
  Proof using Hav Hev Hgd Htp.
    intros HagL. rewrite L78_objs. cbn [map firstn skipn app UNCH_R].
    rewrite (ReabKit.range_ag (rho1 mW) rhoL [O_stk stk78_cells] [] AM_NEXT HagL ltac:(vm_compute; reflexivity) (O_stk stk78_cells) ltac:(left; reflexivity)).
    rewrite rng_stk.
    unfold O_got, O_guard, O_auxvp, O_pgsz, O_errno, O_sec, O_ctx78, O_ctxB, O_brkD, O_brk. cbn [am_got am_libc am_ctx AM_P].
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    assert (EL0 : forall z, eval rhoL (SLit z) = Z_to_bv 64 z) by reflexivity. rewrite !EL0, !soff_lit_small by lia. rewrite !u64 by lia.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoL (v 173) HagL eq_refl), ev173.
    rewrite <- (eval_agree AM_NEXT (rho1 mW) rhoL (SVar 24) HagL eq_refl), ev_tp. rewrite !u64 by (cbn; lia). reflexivity.
  Qed.

  Theorem cut78r_sound : ltac2:(tb__ "0|0|
S16S115S51Vok;R1S112S7S12bS51S52Vrho;S139S51Sc2SfcVX;VR;VU;Sf4Vs;VL;A2VKc;A8R1A5S104R1A1A2Lw;A4S113S51Vok;R2ScSeSf6A1Sf1Vtr;Sf2VmsC;Vmd;A2A4A4F_;Fn;").
  Proof using EmW Erd Evm Ewok HI HIR HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC Htp STK.
    intros n HQ.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof lenZ_range as [LR LA].
    pose proof (alloc_meta_run_P A78_res ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1]] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_res) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    destruct n as [|m]; [exact I|].
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx).
    assert (EL : eval rhoL LENX = Z_to_bv 64 lenZ).
    { rewrite <- (LENX_val mW). symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. }
    refine (triple1_mmap_noneJ segsU ok (liftK (Kexact tr md)) (liftK (Kexact tr md))
              (fun a => fun _ tr' md' => tr' = tr /\ md' = with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) a) md
                                         /\ mmap_place_ok_none (Z_to_bv 64 0) md (eval rhoL LENX) a)
              L78 rhoL (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) ok_pframe_exact L78_ecall M17 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10 in G0. rewrite M11, EL in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5.
      split; [rewrite G1; exact lenZ_ne0|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G3; vm_compute; reflexivity|].
      split; [split; reflexivity|].
      intros a Hpl. split.
      +
        rewrite G0, G1 in Hpl. pose proof Hpl as (Hal & Hpos & Hceil & _). rewrite <- Evm, <- (vm_ok_top L s vm HV) in Hceil.
        pose proof (grant_misses_image a (Z_to_bv 64 lenZ) Hpl) as MISS. rewrite mmap_n_lenZ in MISS. cbn [mc_img_lo mc_img_hi C_U] in MISS.
        rewrite mmap_nZ_lenZ in Hceil. rewrite G1, mmap_nZ_lenZ.
        intros o Ho. pose proof (in_map (obj_range rhoL) _ _ Ho) as RO. rewrite (L78_ranges rhoL HagL) in RO.
        clear - RO MISS Hceil S2 Hpos LR. top_ranges.
        assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (bv_unsigned a, bv_unsigned a + lenZ)).
        { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
          destruct (Z_le_dec hi (bv_unsigned a)); [lia|]. destruct (Z_le_dec (bv_unsigned a + lenZ) lo); [lia|]. exfalso.
          destruct (Z_le_dec (bv_unsigned a) lo); [apply (MISS lo); lia | apply (MISS (bv_unsigned a)); lia]. }
        destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
        repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
      + split; [reflexivity|]. split; [rewrite G1, EL; reflexivity | rewrite EL, <- G0, <- G1; exact Hpl].
    -
      intros w2 [HF2 | (a & HO2)].
      +
        change (SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2) in HF2. rewrite <- Pre_fail_eq in HF2.
        pose proof (alloc_meta_run_P A78_res_fail ok (Kexact tr md) rhoL (ok_frame_exact ok Kc tr md HOK HKc)) as RUN2.
        refine (RUN2 m _ w2 HF2).
        intros [tr3 [ms3 md3]] (Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
        destruct (Posts_am_P_shape A78_res_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
        assert (ELF3 : lf_state L3 = LRF) by (unfold LRF; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
        apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HQ. left.
        exact (post_null ms3 rhoF (agree_below_trans AM_NEXT _ _ _ HagL Hag3) Hsm3).
      +
        apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HQ. right.
        destruct HO2 as [Hsm2 (Etr & Emd & Hpl2)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm2, Etr, Emd, Hpl2.
        exists a, rhoL. split; [exact HagL|]. split; [exact Hpl2|].
        rewrite M11, Mnx in Hsm2. split; [exact Hsm2|]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model]. split; [exact Etr | exact Emd].
  Qed.

  Definition OKPX (Xb : Z) : assn := ltac2:(tb__ "0|4|
S112S5S8aQ40M0A1M1G1S5S2eS2eS4S2dSd1S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7R1A3S4S141S8bG0Z0A2Vmd;S24R1Sd9A2M2R2A4S4S145S51S144S11aVtr;SfbS142Sf7Vmd;A1G2R2A3Vmd;A2M3A2A1S154S100A1S155R1Sd1R2R2S140G2A1A5R3A5S15eG3VXb;A2A2A2A2LrhoL;A2La;A2Lw;").

  Lemma OKPX_OKP Xb w : ltac2:(tb__ "0|0|
S106VXb;Vw;A2S104Vw;A1F_;").
  Proof using . intros (a & rhoL & A1 & A2 & A3 & _). exists a, rhoL. split; [exact A1|]. split; [exact A2 | exact A3]. Qed.

  Lemma L78_miss (rhoL : valuation) (a : word) : ltac2:(tb__ "0|2|
S2dSd1S117Vs;VL;Vrho;Vgd;Vevb;Vavb;VmW;A7VrhoL;A3S141S8bQ40M0Z0A2Vmd;S8bG0S101A2Va;A4S1eS8dS1eR1S32S100A1A3S4dS25VrhoL;R2A2ScS0S0S8cG0Va;A2M1S57G1S101A2A4A2F_;Fo;F_;F_;").
  Proof using Evm HIR HMI Hav Hev Hgd Htp STK.
    intros HagL Hpl. pose proof STK as (S1 & S2 & S3 & S4). pose proof lenZ_range as [LR LA].
    pose proof Hpl as (Hal & Hpos & Hceil & _). rewrite <- Evm, <- (vm_ok_top L s vm HV) in Hceil.
    pose proof (grant_misses_image a (Z_to_bv 64 lenZ) Hpl) as MISS. rewrite mmap_n_lenZ in MISS. cbn [mc_img_lo mc_img_hi C_U] in MISS.
    rewrite mmap_nZ_lenZ in Hceil.
    intros o Ho. pose proof (in_map (obj_range rhoL) _ _ Ho) as RO. rewrite (L78_ranges rhoL HagL) in RO.
    clear - RO MISS Hceil S2 Hpos LR. top_ranges.
    assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (bv_unsigned a, bv_unsigned a + lenZ)).
    { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
      destruct (Z_le_dec hi (bv_unsigned a)); [lia|]. destruct (Z_le_dec (bv_unsigned a + lenZ) lo); [lia|]. exfalso.
      destruct (Z_le_dec (bv_unsigned a) lo); [apply (MISS lo); lia | apply (MISS (bv_unsigned a)); lia]. }
    destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
    repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
  Qed.

  Theorem cut78r_ok_ex : ltac2:(tb__ "0|0|
S0S56Z0R1A2S56S101S5aZ2Z20A2A2S15eVmd;S57R3S101A2A2S114S51S112S3S112R1ScSeSf6A1Sf1Vtr;Sf2VmsC;Vmd;A2A4A3Lw;S106R4A1A3F_;F_;F_;FXb;").
  Proof using Evm HIR HMI Hav Hev Hgd HsmC Htp STK.
    intros Xb HXb H32 HR w ->. pose proof lenZ_range as [LR LA].
    destruct (alloc_meta_run_ex_P A78_res (Kexact tr md) (rho1 mW) (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl)))
      as ([tr1 [ms1 md1]] & ST1 & Lf & rhoL & HinL & HagL & HsmL & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_res) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx).
    assert (EL : eval rhoL LENX = Z_to_bv 64 lenZ).
    { rewrite <- (LENX_val mW). symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. }
    set (Jo := fun a : word => fun (_ : valuation) (tr' : list event) (md' : Model) =>
                 tr' = tr /\ md' = with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) a) md
                 /\ mmap_place_ok_none (Z_to_bv 64 0) md (eval rhoL LENX) a
                 /\ vm_room (with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) a) md) Xb).
    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) L78 rhoL)
                    (fun w => exists a, SPJ segsU (Jo a) (S_ret_fresh L78) (rho_after_unmap rhoL (ss_next L78) a a (mmap_n (eval rhoL (reg_sv L78 11)))) w)).
    { apply (HeapEx.etriple_mmap_none_okJ segsU (liftK (Kexact tr md)) Jo L78 rhoL L78_ecall M17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10 in G0. rewrite M11, EL in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5.
      split; [rewrite G1; exact lenZ_ne0|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G3; vm_compute; reflexivity|].

      assert (Hpos : 0 < bv_unsigned (Z_to_bv 64 lenZ)) by (rewrite (u64 lenZ lenZ_u64); clear - LR; lia).
      assert (HXl : mmap_nZ (Z_to_bv 64 lenZ) <= Xb + lenZ) by (rewrite mmap_nZ_lenZ; clear - HXb; lia).
      destruct (vm_room_grant md (Xb + lenZ) (Z_to_bv 64 lenZ) HR Hpos ltac:(rewrite mmap_nZ_lenZ; exact H32) HXl)
        as (a & _ & _ & _ & _ & _ & _ & _ & _ & Hpln & _ & HRn).
      exists a. rewrite G0, G1. split; [exact (Hpln (Z_to_bv 64 0))|].
      split; [rewrite mmap_nZ_lenZ; exact (L78_miss rhoL a HagL (Hpln (Z_to_bv 64 0)))|].
      unfold Jo. rewrite EL. split; [reflexivity|]. split; [reflexivity|]. split; [exact (Hpln (Z_to_bv 64 0))|].
      rewrite mmap_nZ_lenZ in HRn. replace (Xb + lenZ - lenZ) with Xb in HRn by (clear; lia). exact HRn. }
    destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as (w2 & ST2' & a & HO2).
    exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2']|].
    destruct HO2 as [Hsm2 (Etr & Emd & Hpl2 & HR2)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm2, Etr, Emd, Hpl2, HR2.
    exists a, rhoL. split; [exact HagL|]. split; [exact Hpl2|]. split; [|exact HR2].
    rewrite M11, Mnx in Hsm2. split; [exact Hsm2|]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model]. split; [exact Etr | exact Emd].
  Qed.

  Theorem cut78r_anyex : ltac2:(tb__ "0|0|
S114S51S112S3S112R1ScSeSf6A1Sf1Vtr;Sf2VmsC;Vmd;A2A4A3Lw;S112S7S12bS51S52Vrho;S139S51Sc2SfcVX;VR;VU;Sf4Vs;VL;A2VKc;A8R1A5S104R1A1A2Lw;A3").
  Proof using EmW Erd Evm Ewok HI HIR HKc HMI HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC Htp STK bv0.
    intros w ->. pose proof lenZ_range as [LR LA].
    destruct (alloc_meta_run_ex_P A78_res (Kexact tr md) (rho1 mW) (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl)))
      as ([tr1 [ms1 md1]] & ST1 & Lf & rhoL & HinL & HagL & HsmL & HK1).
    cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_res) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx).
    assert (EL : eval rhoL LENX = Z_to_bv 64 lenZ).
    { rewrite <- (LENX_val mW). symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. }
    set (Jo := fun a : word => fun (_ : valuation) (tr' : list event) (md' : Model) =>
                 tr' = tr /\ md' = with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) a) md
                 /\ mmap_place_ok_none (Z_to_bv 64 0) md (eval rhoL LENX) a).
    assert (ST2 : etriple segsU (SPJ segsU (liftK (Kexact tr md)) L78 rhoL)
                    (fun w2 => SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2
                               \/ exists a, SPJ segsU (Jo a) (S_ret_fresh L78) (rho_after_unmap rhoL (ss_next L78) a a (mmap_n (eval rhoL (reg_sv L78 11)))) w2)).
    { apply (HeapEx.etriple_mmap_none_anyJ segsU (liftK (Kexact tr md)) (liftK (Kexact tr md)) Jo L78 rhoL L78_ecall M17).
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10 in G0. rewrite M11, EL in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5.
      split; [rewrite G1; exact lenZ_ne0|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G3; vm_compute; reflexivity|].
      split; [intros _; split; reflexivity|].
      intros a Hpl. rewrite G0, G1 in Hpl. rewrite G1. split.
      + rewrite mmap_nZ_lenZ. exact (L78_miss rhoL a HagL Hpl).
      + unfold Jo. rewrite EL. split; [reflexivity|]. split; [reflexivity | exact Hpl]. }
    destruct (ST2 (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))) as (w2 & ST2' & [HF2 | (a & HO2)]).
    -
      change (SPJ segsU (liftK (Kexact tr md)) (S_ret_lit L78 enomem_ret) rhoL w2) in HF2. rewrite <- Pre_fail_eq in HF2.
      destruct (alloc_meta_run_ex_P A78_res_fail (Kexact tr md) rhoL w2 HF2) as ([tr3 [ms3 md3]] & ST3 & Lf3 & rhoF & Hin3 & Hag3 & Hsm3 & HK3).
      cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK3. destruct HK3 as [-> ->].
      destruct (Posts_am_P_shape A78_res_fail) as (L3 & EP3 & _). rewrite EP3 in Hin3. destruct Hin3 as [<-|[]].
      assert (ELF3 : lf_state L3 = LRF) by (unfold LRF; rewrite EP3; reflexivity). rewrite ELF3 in Hsm3. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm3.
      exists (tr, mkCfg ms3 md). split; [eapply wsteps_trans; [exact ST1 | eapply wsteps_trans; [exact ST2' | exact ST3]]|].
      left. exact (post_null ms3 rhoF (agree_below_trans AM_NEXT _ _ _ HagL Hag3) Hsm3).
    -
      exists w2. split; [eapply wsteps_trans; [exact ST1 | exact ST2']|]. right.
      destruct HO2 as [Hsm2 (Etr & Emd & Hpl2)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm2, Etr, Emd, Hpl2.
      exists a, rhoL. split; [exact HagL|]. split; [exact Hpl2|].
      rewrite M11, Mnx in Hsm2. split; [exact Hsm2|]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model]. split; [exact Etr | exact Emd].
  Qed.

  Theorem cut78r_S : ltac2:(tb__ "0|0|
S16S3SdS163Vmd;S101A2S19A3S115S51Vok;R2S104A4S113S51Vok;R3ScSeSf6A1Sf1Vtr;Sf2VmsC;Vmd;A2A4A4F_;F_;Fn;").
  Proof using EmW Erd Evm Ewok HI HIR HKc HMI HOK HXr Hac Hav Hav_rd Hbrk Hcnt Hev Hgd Hgd_rd Hhd Hinit Hrom HsmC Htp STK.
    intros n HNR HQ.
    pose proof STK as (S1 & S2 & S3 & S4). pose proof lenZ_range as [LR LA].
    pose proof (alloc_meta_run_P A78_res ok (Kexact tr md) (rho1 mW) (ok_frame_exact ok Kc tr md HOK HKc)) as RUN1.
    refine (RUN1 n _ (tr, mkCfg msC md) (conj HsmC (conj eq_refl eq_refl))).
    intros [tr1 [ms1 md1]] (Lf & rhoL & HinL & HagL & HsmL & HK1). cbn [liftK Kexact w_tr w_cfg fst snd cfg_model cfg_ms] in HK1. destruct HK1 as [-> ->].
    destruct (Posts_am_P_shape A78_res) as (L0 & EP & _). rewrite EP in HinL. destruct HinL as [<-|[]].
    assert (ELF : lf_state L0 = L78) by (unfold L78; rewrite EP; reflexivity). rewrite ELF in HsmL. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in HsmL.
    destruct n as [|m]; [exact I|].
    pose proof L78_misc as (Mpc & M17 & M10 & M11 & M12 & M13 & M14 & M15 & Mnx).
    assert (EL : eval rhoL LENX = Z_to_bv 64 lenZ).
    { rewrite <- (LENX_val mW). symmetry. apply (eval_agree AM_NEXT); [exact HagL | reflexivity]. }
    refine (triple1_mmap_noneJ_forced segsU ok (liftK (Kexact tr md)) (fun _ _ _ => False)
              (fun a => fun _ tr' md' => tr' = tr /\ md' = with_vmmaps (mmap_none_vm (m_vmmaps md) (eval rhoL LENX) a) md
                                         /\ mmap_place_ok_none (Z_to_bv 64 0) md (eval rhoL LENX) a)
              L78 rhoL (ok_frame_liftK segsU ok _ (ok_frame_exact ok Kc tr md HOK HKc)) ok_pframe_exact L78_ecall M17 _ m _
              (tr, mkCfg ms1 md) (conj HsmL (conj eq_refl eq_refl))).
    -
      intros tr0 ms0 md0 Hsp [-> ->].
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 0 Hsp ltac:(repeat constructor)) as G0.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 1 Hsp ltac:(repeat constructor)) as G1.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 2 Hsp ltac:(repeat constructor)) as G2.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 3 Hsp ltac:(repeat constructor)) as G3.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 4 Hsp ltac:(repeat constructor)) as G4.
      pose proof (smatch_pending_gpr segsU rhoL L78 tr ms0 md 5 Hsp ltac:(repeat constructor)) as G5.
      change (10 + Z.of_nat 0) with 10 in G0. change (10 + Z.of_nat 1) with 11 in G1. change (10 + Z.of_nat 2) with 12 in G2.
      change (10 + Z.of_nat 3) with 13 in G3. change (10 + Z.of_nat 4) with 14 in G4. change (10 + Z.of_nat 5) with 15 in G5.
      rewrite M10 in G0. rewrite M11, EL in G1. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5.
      split; [rewrite G1; exact lenZ_ne0|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G2, G3, G5; vm_compute; reflexivity|].
      split; [rewrite G3; vm_compute; reflexivity|].
      split; [rewrite G1, mmap_nZ_lenZ; intros Hrf; rewrite HNR in Hrf; discriminate Hrf|].
      intros a Hpl. split.
      +
        rewrite G0, G1 in Hpl. pose proof Hpl as (Hal & Hpos & Hceil & _). rewrite <- Evm, <- (vm_ok_top L s vm HV) in Hceil.
        pose proof (grant_misses_image a (Z_to_bv 64 lenZ) Hpl) as MISS. rewrite mmap_n_lenZ in MISS. cbn [mc_img_lo mc_img_hi C_U] in MISS.
        rewrite mmap_nZ_lenZ in Hceil. rewrite G1, mmap_nZ_lenZ.
        intros o Ho. pose proof (in_map (obj_range rhoL) _ _ Ho) as RO. rewrite (L78_ranges rhoL HagL) in RO.
        clear - RO MISS Hceil S2 Hpos LR. top_ranges.
        assert (IMG : forall lo hi, 65536 <= lo -> hi <= 372736 -> lo < hi -> SymState.ranges_disjoint (lo, hi) (bv_unsigned a, bv_unsigned a + lenZ)).
        { intros lo hi H1 H2 H3. unfold SymState.ranges_disjoint. cbn [fst snd].
          destruct (Z_le_dec hi (bv_unsigned a)); [lia|]. destruct (Z_le_dec (bv_unsigned a + lenZ) lo); [lia|]. exfalso.
          destruct (Z_le_dec (bv_unsigned a) lo); [apply (MISS lo); lia | apply (MISS (bv_unsigned a)); lia]. }
        destruct RO as [E|RO]; [rewrite <- E; unfold SymState.ranges_disjoint; cbn [fst snd]; lia|].
        repeat (destruct RO as [E|RO]; [rewrite <- E; apply IMG; lia|]). destruct RO.
      + split; [reflexivity|]. split; [rewrite G1, EL; reflexivity | rewrite EL, <- G0, <- G1; exact Hpl].
    -
      intros w2 [HF2 | (a & HO2)].
      + destruct HF2 as [_ F]. exact (False_ind _ F).
      +
        apply (@Safety.safe_mono segsU ok (S m) m); [apply Nat.le_succ_diag_r|]. apply HQ.
        destruct HO2 as [Hsm2 (Etr & Emd & Hpl2)]. cbn [w_tr w_cfg fst snd cfg_model cfg_ms] in Hsm2, Etr, Emd, Hpl2.
        exists a, rhoL. split; [exact HagL|]. split; [exact Hpl2|].
        rewrite M11, Mnx in Hsm2. split; [exact Hsm2|]. cbn [liftK Kexact w_tr w_cfg fst snd cfg_model]. split; [exact Etr | exact Emd].
  Qed.
End Cut78r.

End InstX.

End Mal_ameta_R78.
