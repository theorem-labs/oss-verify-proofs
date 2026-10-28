(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "proj2"; "not"; "or"; "ex"; "proj1"; "iff"; "False"; "True"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SAlu"; "SVar"; "sobj"; "sprop"; "cell"; "SMd"; "mkCell"; "SPUle"; "eval"; "rw"; "swf"; "ss_objs"; "DUnknown"; "sstate"; "sprop_eqb"; "ob_base"; "ob_dflt"; "odefault"; "ob_cells"; "rl"; "smatch"; "obj_hi_of"; "obj_holds"; "obj_lo_of"; "obj_range"; "ranges_disjoint"; "rm"; "valuation"; "SAluW"; "mkObj"; "rd"; "ss_next"; "SExt"; "mkSS"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "mkVal"; "ob_hi"; "ob_lo"; "DZero"; "agree_below"; "c_off"; "c_val"; "c_width"; "enc_bytes"; "soff"; "sv_eqb"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "bool"; "true"; "list"; "prod"; "option"; "Some"; "nil"; "length"; "nat"; "app"; "None"; "andb"; "false"; "snd"; "S"; "fst"; "negb"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "M_MUL"; "ALU_AND"; "ALU_SRL"; "ALU_OR"; "ALU_XOR"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "modulo"; "of_nat"; "mul"; "div"; "sub"; "min"; "eqb"; "opp"; "land"; "leb"; "lor"; "to_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "od2"; "obj_of2"; "zl2"; "zr2"; "rho2"; "D_got"; "D_guard"; "ia_sc"; "icnt0"; "D_errno"; "zA"; "ia_U"; "ia_X"; "ia_m"; "iaidx"; "icnt"; "isize"; "live"; "od2_entry"; "ctr"; "ia_R"; "ia_erv"; "ij"; "lv_MI"; "usg"; "D_act0"; "D_ctr"; "D_m"; "D_usg"; "ia_L"; "iszc"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "MFree"; "astate"; "region"; "PGSZ"; "st_free_meta_head"; "UNIT"; "ameta"; "st_regions"; "class_size"; "initial_cnt"; "st_brk"; "IB"; "alloc_group"; "halve_while_even"; "kreq"; "ones"; "padd"; "MRaw"; "RkMap"; "brkst"; "mkRegion"; "prid"; "small_cnt"; "sptr_eqb"; "st_areas"; "st_init_done"; "MUsed"; "am_last"; "am_maplen"; "am_sc"; "page_round"; "poff"; "st_active"; "st_usage"; "stride_of"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_TP.TP.LeafT"; "dsF"; "objsD"; "mA"; "omapF"; "stkF"; "Lf1"; "stkc"; "mF"; "rhoA"; "CHK'"; "touched"; "rhoX"; "HagA"; "HdsF_T"; "touchedD"; "NEW"; "gmeets"; "restF"; "EmA"; "HSF_objs"; "HdsC_sub"; "HsmA"; "rhoR"; "rhoS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "byteview_of"; "addr_of"; "mc_errno"; "holds"; "topL"; "wz"; "mc_ctx"; "vm_ok"; "blocks"; "img_reserved"; "ledger_ok"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctz_tab"; "mc_img_hi"; "mc_img_lo"; "mc_libc"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "RsSymJump"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_TP.TP"; "post"; "L'"; "dsC_T"; "omap_T"; "amL";
"drop_last"; "LWc"; "e_sll"; "sTx"; "aidx"; "e_av"; "e_bits"; "e_ctr"; "e_fr"; "e_sc6"; "e_usg"; "leafT_chk"; "D_mT"; "c_ab"; "c_mp"; "e_ab"; "sT_a"; "sT_b"; "sT_c"; "sT_d"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_FX.FX"; "s'"; "zm"; "HAND"; "zfm"; "zhp"; "t1"; "mF"; "Lfr"; "bv1"; "touched"; "locsF"; "gmeets"; "rhoA"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "MT"; "loc"; "loc_addr"; "keys"; "mc_loc"; "footprint"; "Inv"; "LMem"; "image"; "mc_w"; "cell_holds"; "user_blocks"; "CTX_SIZE"; "MCell"; "le_byte"; "ly_ctx"; "region_of"; "yields"; "VZ"; "group_cells"; "mc_val"; "sval_num"; "usedX"; "CTX_free_meta_head"; "LCtx"; "VP"; "active_hd"; "alloc_owned"; "memb"; "optr"; "sval"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3"; "SN3s"; "factsN3"; "nvars"; "NXN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K"; "dsM23"; "EK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN"; "iaN"; "mWN"; "bzN"; "nokR"; "nstrd"; "zp"; "nidx"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "m1_hi"; "m1_lo"; "stk_only"; "ods_eqb"; "stk_shape"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R"; "dlo2"; "dhi2"; "dcond2b"; "od2_semb"; "changed2"; "oStkF"; "DS2"; "drom2"; "rhoR"; "rngD"; "dcells2"; "fill2"; "od2_eqb"; "Hzl2"; "Hzr2"; "cellsD"; "cellsInD"; "dcond2"; "dunkD"; "range64D"; "semD"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "nth"; "Forall"; "seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "obj_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "IEC_U"; "L_as_ok"; "tier"; "L_as_fail"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "agrees"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "obj_matchb"; "objs_matchb"; "m'"; "touched"; "cell_from_od"; "m'_in"; "m'_out"; "touched_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs"; "leafN_ok"; "memZZ"; "nests"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "with_mem"; "diffs_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "VmMaps"; "vm_reserved"; "m_vmmaps"; "Model"; "vm_maps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "mkMA"; "layout_extends"; "MA"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_FX"; "O_fmpE"; "O_hpnE"; "O_fhE"; "RING"; "CANON"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "trailing_cell"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "state_has_rl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "wsub_id_below"; "wsub_get"; "wsub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "nr_id"; "fm_post"; "mm_aidx"; "mm_post"; "mm_pre"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_RES"; "alloc_static"; "client_addr"; "errno_range"; "mem_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG"; "QG"; "canary_bytes"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "m1v"; "LK"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv"; "prov"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow"; "memN"; "geN'"; "gg_amL"; "gg_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T"; "LW"; "Hi'"; "K1"; "SWx"; "live1"; "m1"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "group_post"; "heads_below"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes"; "release_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"; "cmeets"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "O_map"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs"; "SNok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC"; "contN_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NT2"; "dN_4_25_L"; "dN_4_25_Z"; "dN_5_10_L"; "dN_5_10_Z"; "dN_5_21_L"; "dN_5_21_Z"; "dN_5_5_L"; "dN_5_5_Z"; "dN_6_4_L"; "dN_6_4_Z"; "@Corelib.Init.Nat"; "add"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_fresh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow"; "Lext"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "not_used"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "fq_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow"; "gvm'"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP"; "nleaf_chk"; "resym"; "resym_chk"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK"; "lfs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN2"; "LN_4_25_L"; "LN_4_25_Z"; "LN_5_10_L"; "LN_5_10_Z"; "LN_5_21_L"; "LN_5_21_Z"; "LN_5_5_L"; "LN_5_5_Z"; "LN_6_4_L"; "LN_6_4_Z"; "SN_4_25_L"; "SN_4_25_Z"; "SN_5_10_L"; "SN_5_10_Z"; "SN_5_21_L"; "SN_5_21_Z"; "SN_5_5_L"; "SN_5_5_Z"; "SN_6_4_L"; "SN_6_4_Z";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.UsageBound.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_agrp_TP.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.UsageBound OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLawsI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma page_round_id z : ltac2:(tb__ "0|1|
S5dZ0M0Vz;A2S0S54S61Vz;Z1000A2G0A3S0S54SacVz;A1Vz;A3F_;F_;").
Proof. intros Hz Hm. unfold page_round, PGSZ. Z.to_euclidean_division_equations; nia. Qed.

Lemma layout_extends_trans_le L0 L1 L2 n0 n1 : ltac2:(tb__ "0|0|
S187VL0;VL1;Vn0;A3S187VL1;VL2;Vn1;A3S17cVn0;Vn1;A2S187VL0;VL2;Vn0;A3F_;F_;F_;").
Proof.
  intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5) Hle. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [|congruence].
  intros r Hr. rewrite (B4 r ltac:(lia)). exact (A4 r Hr).
Qed.

Section TP.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1b5SccVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variable za : Z.
Let ia' : instA := set_R ia za.
Let L : layout := ia_L ia. Let vm : VmMaps := ia_vm ia. Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let s1 : astate := ia_s ia. Let req : Z := ia_req ia.
Variables (cur : astate) (mWc : word -> option byte).
Hypothesis HLV : ltac2:(tb__ "0|0|
S7eVia;Vcur;VL;VmWc;Vvm;A5").
Hypothesis Hgr : grant_ok ia za.
Hypothesis HE : ltac2:(tb__ "0|0|
Sd5Sd2S112SccVmWc;A2SceQ40A1S43L_;A2Sd4Sd1A1U4S82Via;A1A4").
Let len : Z := ineeded ia.
Let mZ : word -> option byte := ltac2:(tb__ "0|0|
S1bbVia;Vza;VmWc;A3").
Let vmN : VmMaps := vm1 ia za.
Let KN : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S1b8VKc;Via;Vza;A3").
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S1abVia;VX;VU;VA;Vrho0;A5").
Hypothesis Ecur : ltac2:(tb__ "0|0|
S0S8fVcur;S19fVsc;Vs1;A2A3").
Hypothesis Harm : ltac2:(tb__ "0|0|
S5fS64S91Z2A2S5eS8bVia;A1S93A2A2").

Let Hi2 : instA_ok ia' := ltac2:(tb__ "0|0|
S1b7Via;VHi;Vza;A3").
Let HLV1 : live ia' cur L mZ vm := ltac2:(tb__ "0|0|
S1baVia;VHi;Vza;Vcur;VmWc;VHLV;VHgr;A7").

Definition aidx : Z := ltac2:(tb__ "0|0|
S19dS7dVia;A1S7cVia;A1A2").
Definition post : astate := ltac2:(tb__ "0|0|
S1b1Vcur;Vm;Vsc;S7cVia;A1Sf5Vlen;A6").
Definition L' : layout := ltac2:(tb__ "0|0|
S1d3VL;S19bVcur;A1Vza;A3").
Definition amL : ameta := ltac2:(tb__ "0|0|
S1b0Vm;S1aeVcur;A1Vsc;S7cVia;A1Sf5S64Vlen;Z1000A2A6").

Lemma AF : ltac2:(tb__ "0|4|
S1S5dZ1000M0Vza;A2S1S5dS5eVza;Vlen;A2Sd6VL;A1M1A2S1S0S54S61Vza;G0A2Z0M2A3S1S5dG1Z7fffff800000A2S1S1S5dG0Vlen;A2S5dVlen;S60Z2Z17A2A2A2S1S0S54S61Vlen;G0A2G2A3S1S0S54Sd0Q40M3Sd7Vza;A1A2Vza;A3S0S54Sd0G3S1d1Sd7Vlen;A1A1A2Vlen;A3A2A2A2A2A2A2A2").
Proof using Hgr Hi. exact (a_facts ia Hi za Hgr). Qed.

Lemma post_eq : ltac2:(tb__ "0|0|
S0S8fS19eVsc;Vreq;Vm;Vs1;A4SecA3").
Proof using Ecur Hgr Hi.
  pose proof AF as (_ & _ & _ & _ & A5 & A6 & _).
  unfold mm_post, post, gg_post, ig, grown. rewrite <- Ecur.
  change (snd (mmap_plan s1 sc req (initial_cnt sc (usage_of s1 sc)) (usage_of s1 sc))) with (ineeded ia).
  change (fst (mmap_plan s1 sc req (initial_cnt sc (usage_of s1 sc)) (usage_of s1 sc))) with (icnt ia).
  change (class_size sc) with (isize ia). fold len. rewrite (page_round_id len) by lia. reflexivity.
Qed.

Lemma pX : ltac2:(tb__ "0|0|
S0S44S8cA1S79Via;A1VX;A3"). Proof using PV. exact (pv_X ia X U A rho0 PV). Qed.
Lemma pU : ltac2:(tb__ "0|0|
S0S54S54F_;S78Via;A1VU;A3"). Proof using PV. exact (pv_U ia X U A rho0 PV). Qed.
Lemma pR : ia_R ia = None. Proof using PV. exact (pv_R ia X U A rho0 PV). Qed.
Lemma pSC : ltac2:(tb__ "0|0|
S0S54Vsc;Sd0Q40S15Vrho0;PcA2A2A3"). Proof using PV. exact (pv_sc ia X U A rho0 PV). Qed.
Lemma pREQ : ltac2:(tb__ "0|0|
S0S54Vreq;Sd0Q40S15Vrho0;PdA2A2A3"). Proof using PV. exact (pv_req ia X U A rho0 PV). Qed.

Lemma SCR : 0 <= sc < 48. Proof using Hi. exact (iok_sc ia Hi). Qed.
Lemma REQR : ltac2:(tb__ "0|0|
S1S5dZ0Vreq;A2S5dS5eVreq;S99A2S96Vsc;A1A2A2"). Proof using Hi. exact (iok_req ia Hi). Qed.

Lemma yields_T : ltac2:(tb__ "0|2|
S4aS17cS1b4Vsc;A1S50R1A1A2S5S44S45S9cS54A2A1M0G0S126S45S46S8cA1M1S8fA2S9aR3Vsc;Vreq;S185VA;A1A4R1S41G1S8fS47S8cVm;A2SecA4A4Lktr;A2F_;Ffuel;").
Proof using Ecur Harm Hgr Hi PV.
  intros fuel Hf. destruct (pv_am ia X U A rho0 PV) as [tr0 Hm]. pose proof AF as (A1 & _).
  destruct fuel as [|f]; [pose proof (need_ge2 sc); lia|].
  exists (tr0 ++ [(KMmapRW (snd (mmap_plan s1 sc req (initial_cnt sc (usage_of s1 sc)) (usage_of s1 sc))), za)]).
  rewrite <- post_eq. apply (ag_mmap_granted sc req f (ma_s A) m tr0 s1 Hm).
  - change (class_size sc * initial_cnt sc (usage_of s1 sc)) with (iszc ia). exact Harm.
  - lia.
  - exact (iok_hd ia Hi).
Qed.

Lemma GP : ltac2:(tb__ "0|0|
S1beVX;VU;S185VA;A1Vsc;Vreq;S41S46S8cA1S8fS47S8cVm;A2SecA4A6").
Proof using Ecur Harm Hgr Hi PV.
  destruct (yields_T (need sc) ltac:(lia)) as [ktr Hy]. pose proof SCR. pose proof REQR as [R1 R2].
  exact (alloc_group_post X U (ma_s A) sc req (need sc) ktr (Some m, post) (pv_I0 ia X U A rho0 PV) SCR R1 R2 ltac:(lia)
           (pv_hd0 ia X U A rho0 PV) Hy).
Qed.

Lemma post_I : ltac2:(tb__ "0|0|
S11bVX;S47S45S8cS54A2S41S8cS54Vm;Z0A4A2VU;SecA4").
Proof using Ecur Harm Hgr Hi PV. destruct GP as (_ & _ & am & HI & _). exact HI. Qed.
Lemma post_hb : ltac2:(tb__ "0|1|
S1S1bfS185VA;A1M0SecVsc;A3S1bcG0SecA2A2").
Proof using Ecur Harm Hgr Hi PV. destruct GP as (H1 & H2 & _). exact (conj H1 H2). Qed.

Let LMI : ltac2:(tb__ "0|0|
S1b3Sd1S40S8cS7aVia;A1S79Via;A1A3S81Via;A1S78Via;A1S186Vcur;VL;A2S112SccVmWc;A2S113SccVmWc;A2Vvm;A8") := ltac2:(tb__ "0|0|
S84Via;Vcur;VL;VmWc;Vvm;VHLV;A6").
Lemma LI : ltac2:(tb__ "0|0|
S11bS40S8cVm;VX;A3S4cS45S8cS54A2A1VU;Vcur;A4"). Proof using LMI PV. rewrite <- pX, <- pU, <- pR. exact (mig_I LMI). Qed.
Lemma LXr : ltac2:(tb__ "0|0|
S1c1S40S8cVm;VX;A3Vcur;A2"). Proof using HLV PV. rewrite <- pX. exact (lv_Xr ia cur L mWc vm HLV). Qed.
Lemma LL : layout_ok L cur. Proof using LMI. exact (mig_layout LMI). Qed.
Lemma LV : ltac2:(tb__ "0|0|
Sd9VL;Vcur;Vvm;A3"). Proof using LMI. exact (mig_vm LMI). Qed.
Lemma LLG : ledger_ok C_U vm. Proof using LMI. exact (mig_ledger LMI). Qed.
Lemma LIR : img_reserved C_U vm. Proof using LMI. exact (mig_img LMI). Qed.
Lemma LMW : maps_wf vm. Proof using LMI. exact (mig_maps LMI). Qed.
Lemma LB : bounded cur. Proof using LMI. exact (mig_bounded LMI). Qed.
Lemma Lctx : ltac2:(tb__ "0|0|
S0S54S124VL;A1Sd8Sd1A1A3"). Proof using LMI. exact (mig_ctx LMI). Qed.
Lemma Lkey : In m (keys cur). Proof using HLV. exact (lv_key ia cur L mWc vm HLV). Qed.
Lemma Lraw : ltac2:(tb__ "0|3|
S4S0S46S8dA1M0S115Vcur;Vm;A2M1S47S8dS9fA2A3S0G0G1S47S8dS8eS4cS8cA1M2G2A2A2A3A2"). Proof using HLV. exact (lv_raw ia cur L mWc vm HLV). Qed.
Lemma Lma : ltac2:(tb__ "0|0|
S0S54Sd3VL;Vm;A2S77Via;Vm;A2A3"). Proof using HLV. exact (lv_m_addr ia cur L mWc vm HLV). Qed.
Lemma ND : List.NoDup (keys cur). Proof using LMI PV m. exact (proj1 (inv_keys LI)). Qed.
Lemma Llen : ltac2:(tb__ "0|1|
S1S0S4aS49S46S8cA1SaeVcur;A1A2U30M0A3S0S4aS49S54SafVcur;A1A2G0A3A2").
Proof using LMI PV m. pose proof (inv_ctx LI) as (C1 & C2 & _). exact (conj C1 C2). Qed.
Lemma xold : ltac2:(tb__ "0|0|
S5S8dS8dS1S0S46S8dA1S115Vcur;Vm;A2S47S8dR1A2A3S1d4R1A1A2Lxo;A2").
Proof using HLV. destruct Lraw as [E|E]; eexists; (split; [exact E | exact I]). Qed.

Lemma Hfree : ltac2:(tb__ "0|4|
S45SceQ40M0A1M1G1A2M2Sb1G2R1S4bG2S181Vvm;A1S184Vvm;A1A3A3S54S1S5dSd0G0S51G1G1R3A3A2M3R1A2S5fR1S5eG3Sd0G0S4fG1G1R3A3A2A2A2A2S3S1S5dVza;R2A2S5fR2S5eVza;Vlen;A2A2A2A1F_;Fy;F_;Fe;").
Proof using Hgr. intros e He y Hy. exact (FREE ia za Hgr e y He Hy). Qed.
Lemma Hlen : ltac2:(tb__ "0|0|
S1S5dS91Vlen;A2S0S54S61Vlen;S91A2Z0A3A2"). Proof using Hgr Hi req sc. pose proof AF as (_ & _ & _ & _ & A5 & A6 & _). unfold PGSZ. lia. Qed.
Lemma Hzal : za mod PGSZ = 0. Proof using Hgr Hi len. pose proof AF as (_ & _ & A3 & _). exact A3. Qed.
Lemma Hzpos : 0 < za. Proof using Hgr Hi len req sc. pose proof AF as (A1 & _). lia. Qed.
Lemma Hzceil : ltac2:(tb__ "0|0|
S5dS5eVza;Vlen;A2Sd6VL;A1A2"). Proof using Hgr Hi. pose proof AF as (_ & A2 & _). exact A2. Qed.

Lemma post_regs : ltac2:(tb__ "0|0|
S0S44S90A1S95SecA1S4bS90S95Vcur;A1S40S90Sa2Sa0Vlen;S48S54A1S43A4S48S90A1A3A3A3"). Proof using . reflexivity. Qed.
Lemma post_areas : ltac2:(tb__ "0|0|
S0S44S8cA1Sa6SecA1Sa6Vcur;A1A3"). Proof using . reflexivity. Qed.
Lemma post_brk : ltac2:(tb__ "0|0|
S0Sa1S98SecA1S98Vcur;A1A3"). Proof using . reflexivity. Qed.
Lemma post_keys : ltac2:(tb__ "0|0|
S0S44S8cA1S118SecA1S118Vcur;A1A3").
Proof using HLV. destruct xold as (xo & E & NU). exact (gg_keys cur m sc (icnt ia) aidx len xo E). Qed.
Lemma post_MT q : ltac2:(tb__ "0|1|
S0S46S8dA1M0S115SecVq;A2S42G0L_;Sa5Vq;Vm;A2S47S8dSa8Sf0A1A2S115Vcur;Vq;A2X42x2A3").
Proof using . exact (gg_MT cur m sc (icnt ia) aidx len q). Qed.
Lemma post_ub : ltac2:(tb__ "0|0|
S0S44S45S8cS54A2A1S120SecA1S120Vcur;A1A3").
Proof using LMI PV. destruct xold as (xo & E & NU). exact (gg_user_blocks cur m sc (icnt ia) aidx len xo ND E NU). Qed.
Lemma post_fp : ltac2:(tb__ "0|1|
S0S44S45S116S54A2M0A1S11aSecA1S4bG0S11aVcur;A1S40G0S1afVcur;Vlen;A2S48G0A1A3A3A3").
Proof using . exact (gg_footprint cur m sc (icnt ia) aidx len). Qed.

Lemma vmN_eq : ltac2:(tb__ "0|0|
S0S180VvmN;S1d6Vvm;Vza;Vlen;A3A3").
Proof using Hgr Hi req sc.
  pose proof AF as (_ & _ & _ & _ & A5 & _ & Ua & Un). unfold vmN, vm1, mmap_rw_vm, gvm'. f_equal. f_equal.
  assert (E : mmap_n (wz (ineeded ia)) = wz (ineeded ia)); [|rewrite E; reflexivity].
  apply bv_eq. change (bv_unsigned (mmap_n (wz (ineeded ia)))) with (bv_unsigned (mmap_n (wz len))). rewrite Un. unfold wz, len. rewrite u64 by lia. reflexivity.
Qed.

Lemma post_L : layout_ok L' post.
Proof using Hgr Hi LMI PV.
  exact (g_layout_ok C_U (m :: X) None U cur post L vm za len LI LL Lctx statics_in_image_U LV (AllocMetaGrow.vm_ok_X L cur vm LV) LIR Hzal Hzpos Hlen Hzceil Hfree post_regs post_areas).
Qed.
Lemma post_V : ltac2:(tb__ "0|0|
Sd9SedSecVvmN;A3").
Proof using Hgr Hi LMI PV. rewrite vmN_eq. exact (g_vm_ok (m :: X) None U cur post L vm za len LI LV Hzal Hzpos Hlen Hzceil Hfree post_regs post_areas post_brk LMW). Qed.
Lemma post_LG : ltac2:(tb__ "0|1|
S1SdcSd1VvmN;A2S1SdbSd1VvmN;A2S0S44S45SceQ40A1M0G0A2A1S181VvmN;A1S181Vvm;A1A3A2A2").
Proof using Hgr Hi LMI len req sc. rewrite vmN_eq. exact (g_ledger C_U cur L vm za len statics_in_image_U LV LLG LIR Hzal Hzpos Hlen Hzceil Hfree). Qed.
Lemma post_MW : maps_wf vmN.
Proof using Hgr Hi LMI len req sc. rewrite vmN_eq. exact (g_maps_wf L vm za len Hzal Hzpos Hlen Hzceil Hfree LMW). Qed.
Lemma post_B : bounded post.
Proof using Ecur Harm Hgr Hi LMI PV vmN.
  apply (bounded_usage C_U X (Some (m, 0)) U cur post L' vmN LB post_I post_L post_V (proj1 post_LG)).
  - intros c. rewrite <- pU. exact (iok_U0 ia Hi c).
  - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - rewrite post_regs, length_app. cbn. lia.
Qed.

Lemma post_used : ltac2:(tb__ "0|0|
S1S12bVX;SecVm;Sf0A4S0S42S131Vm;VX;A2S4eA3A2").
Proof using Ecur Harm Hgr Hi PV.
  destruct GP as (_ & _ & am & _ & _ & Hu & _). unfold usedX, MTX in Hu |- *.
  destruct (memb m X); [discriminate|]. split; [|reflexivity]. rewrite post_MT. rewrite (proj2 (sptr_eqb_eq m m) eq_refl). reflexivity.
Qed.
Lemma post_am : ltac2:(tb__ "0|0|
S94S12bVX;SecVm;R1A4S0S94R2Sf0A3F_;Fam;").
Proof using .
  intros am Hu. unfold usedX, MTX in Hu. destruct (memb m X); [discriminate|]. rewrite post_MT, (proj2 (sptr_eqb_eq m m) eq_refl) in Hu. congruence.
Qed.
Lemma post_X : xraw X post.
Proof using Ecur HLV Harm Hgr Hi PV.
  intros q Hq. pose proof post_used as [_ NM]. rewrite post_MT.
  destruct (sptr_eqb q m) eqn:E.
  - exfalso. apply sptr_eqb_eq in E. subst q. unfold memb in NM.
    assert (C : existsb (sptr_eqb m) X = true) by (apply existsb_exists; exists m; split; [exact Hq | apply (proj2 (sptr_eqb_eq m m) eq_refl)]).
    rewrite C in NM. discriminate.
  - exact (LXr q (or_intror Hq)).
Qed.
Lemma post_group : ltac2:(tb__ "0|0|
S1S0S54SabSf0A1Vsc;A3S1S5dS5eVreq;S99A2Sb0Sf0A1A2S1S5dZ0Sa9Sf0A1A2S0S46S8cA1S12fSecVsc;A2S47S8cVm;A2A3A2A2A2").
Proof using Ecur Harm Hgr Hi PV.
  destruct GP as (_ & _ & am & _ & Hhd & Hu & Hsc & Hst & Hl). pose proof (post_am am Hu) as ->. auto.
Qed.

Definition e_sll (e : sv) : sv := SAluW ALU_SLL (SLit 2) e.
Definition e_av : sv := ltac2:(tb__ "0|1|
ScS56S2cS43Q20ScS56Sf3SdPa1A1A1SbN1A1M0A3A3G0A3").
Definition e_fr : sv := ltac2:(tb__ "0|1|
ScS56Sf3ScS56SdPb0A1SbN1A1M0A3A1ScS5cS2cS43Q20ScS56Sf3SdPa1A1A1G0A3A3SbZffffffffffffffffA1A3A3").

Definition e_sc6 (x : m1v) : sv := ltac2:(tb__ "0|1|
S1a9SaLx;Vx;ScS57SdPcA1SbZ6A1A3M0G0G0SbZbc0A1X1a9x4").
Definition e_bits (x : m1v) : sv := ltac2:(tb__ "0|0|
ScS56ScS5bScS5bSfaVx;A1ScS59ScS56SdPb0A1SbN1A1A3SbZ1fA1A3A3SdPb1A1A3SbZ20A1A3").
Definition e_usg : sv := SAlu ALU_ADD (SVar 192%positive) (SVar 176%positive).
Definition e_ctr : sv := ltac2:(tb__ "0|0|
ScS56S2cS43Q20SdPc5A1A3SbZ1A1A3").
Definition e_ab : sv := SAlu ALU_AND (SVar 161%positive) (SLit 31).
Definition D_mT (x : m1v) : od2 := ltac2:(tb__ "0|1|
S88SdPbeA1M0G0SdPbbA1Sf6Sf9Sf7Vx;A1A6").
Definition dsC_T (x : m1v) : list od2 := ltac2:(tb__ "0|0|
S40S6dSfdVx;A1S40S6dS86SdPbeA1A1S40S6dS89SfbA1S40S6dS87Sf8A1S48S6dA1A3A3A3A3").
Definition c_ab : cell := mkCell (SLit 8) 1 e_ab.
Definition c_mp : cell := mkCell (SLit 0) 8 (SVar 190%positive).
Definition omap_T : sobj := ltac2:(tb__ "0|0|
S29SdPbbA1SbZ0A1SdPb1A1S40S10SfeS40S10SffS48S10A1A3A3S38A5").

Definition leafT_chk (x : m1v) (Lf : sstate) : bool := ltac2:(tb__ "0|3|
S44SeA1M0S42Lx;S17VLf;A1S4eSeG0S49S6dS13aVx;A1M1A2S4aS15eSeR1R2A3G0S15fSeR2R3S1c3A4SeS153G1R2A2S44S6dA1S4dS4dS4dS4dS4dS4dS4dS4dS4dS4dS1efS49SeR5A2S50R4A1A2S147R6A1A2S16cR3S15dS6dSeS6eR1A4M2A2A2Sb2SeS164S169A1G2A3A2Sb2S6dS14bR1A3A2Sb2S6dS14aS144Vx;A1S143Vx;A1A2R1A3A2S146S14cG1R1A2SeeVx;A1A2A2S16bR2SefA2A2S16S145VLf;A1A1A2Sb3S6dS154S72A1R1A3A2Sb3S6dS154S73A1R1A3A2TdsF;TomapF;TobjsD;Tn;Lrest;Lstk;X44x2").

Lemma Lok_norl l : ltac2:(tb__ "0|0|
S0S42S195Vl;S166S165A1A2S4eA3"). Proof using . destruct l; reflexivity. Qed.

Section Arith.
Let c : Z := icnt ia. Let a : Z := iaidx ia. Let q : Z := iqdiv ia.
Lemma cR : 1 <= c <= 32. Proof using Hi. exact (proj1 (iplan_range ia Hi)). Qed.
Lemma aR : ltac2:(tb__ "0|0|
S1S1S5dZ0Va;A2S5dVa;S65Vc;Z1A2A2A2S5dVa;Z1fA2A2"). Proof using Hi. exact (iaidx_range ia Hi). Qed.
Lemma z161 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPa1A1A3Va;A3"). Proof using Hi2. exact (zs161 ia' Hi2). Qed.
Lemma z176 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPb0A1A3Vc;A3"). Proof using Hi2. exact (zs176 ia' Hi2). Qed.
Lemma z177 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPb1A1A3Vlen;A3"). Proof using Hi2. exact (zs177 ia' Hi2). Qed.
Lemma z12 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPcA1A3Vsc;A3"). Proof using Hi2. exact (zs12 ia' Hi2). Qed.
Lemma z190 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPbeA1A3S77Via;Vm;A2A3"). Proof using Hi2. exact (zs190 ia' Hi2). Qed.
Lemma z192 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPc0A1A3S85Via;A1A3"). Proof using Hi2. exact (zs192 ia' Hi2). Qed.
Lemma z197 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPc5A1A3S80Via;A1A3"). Proof using Hi2. exact (zs197 ia' Hi2). Qed.
Lemma z187 : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SdPbbA1A3Vza;A3").
Proof using Hgr Hi2 a c len q req sc. pose proof AF as (A1 & A2 & A3 & AC & A5 & _). rewrite (zs187 ia' Hi2). cbn [ia' set_R ia_Rz]. apply Z.mod_small. lia. Qed.

Definition F_av (a : Z) : Z := zeval (fun _ => a) (fun _ => []) e_av.
Definition F_fr (a c : Z) : Z := zeval (fun j => if Pos.eqb j 161 then a else c) (fun _ => []) e_fr.
Lemma F_av_ok : forall a0, 0 <= a0 < 0 + Z.of_nat 32 -> (F_av a0 mod 2 ^ 32 =? (ones a0 - 1) mod 2 ^ 32) = true.
Proof using . apply forall_range_dec. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma F_fr_ok : forall c0, 1 <= c0 < 1 + Z.of_nat 32 -> forallb (fun a0 => F_fr a0 c0 mod 2 ^ 32 =? (ones (c0 - 1) - ones a0) mod 2 ^ 32) (map (fun k => 0 + Z.of_nat k) (seq 0 (Z.to_nat c0))) = true.
Proof using . apply (forall_range_dec (fun c0 => forallb _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma zev_av : ltac2:(tb__ "0|1|
S0S54S61S134S70Via';A1S6fVia';A1Sf6A3S60Z2Z20A2M0A2S61S65S9dVa;A1Z1A2G0A2A3").
Proof using Hi2 c len q req sc.
  pose proof aR as AR. pose proof (F_av_ok a ltac:(lia)) as E. apply Z.eqb_eq in E. rewrite <- E. f_equal.
  unfold F_av. transitivity (zeval (fun _ => zr2 ia' 161%positive) (fun _ => @nil Z) e_av).
  - unfold e_av, e_sll. cbn [zeval]. reflexivity.
  - rewrite (zr2_161 ia' Hi2). reflexivity.
Qed.
Lemma zev_fr : ltac2:(tb__ "0|1|
S0S54S61S134S70Via';A1S6fVia';A1Sf9A3S60Z2Z20A2M0A2S61S65S9dS65Vc;Z1A2A1S9dVa;A1A2G0A2A3").
Proof using Hi2 len q req sc.
  pose proof aR as AR. pose proof cR as CR.
  pose proof (proj1 (forallb_forall _ _) (F_fr_ok c ltac:(lia)) a ltac:(apply in_map_iff; exists (Z.to_nat a); split; [lia | apply in_seq; lia])) as E.
  apply Z.eqb_eq in E. rewrite <- E. f_equal.
  unfold F_fr. transitivity (zeval (fun j => if Pos.eqb j 161 then zr2 ia' 161%positive else zr2 ia' 176%positive) (fun _ => @nil Z) e_fr).
  - unfold e_fr, e_sll. cbn [zeval Pos.eqb]. reflexivity.
  - rewrite (zr2_161 ia' Hi2), (zr2_176 ia' Hi2). reflexivity.
Qed.

Lemma lor_add_high u w k : ltac2:(tb__ "0|3|
S1S5dZ0M0Vu;A2S5fVu;S60Z2Vk;A2M1A2A2S5dG0Vw;A2S5dG0Vk;A2S0S54S6bVu;S63Vw;G1A2M2A2S5eVu;G2A2A3F_;F_;F_;").
Proof using a c len q req sc.
  intros Hu Hw Hk.
  assert (HL : Z.land u (w * 2 ^ k) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n k) as [LT|GE].
    - rewrite (Z.mul_pow2_bits_low w k n) by lia. apply Bool.andb_false_r.
    - destruct (Z.eq_dec u 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      assert (LG : Z.log2 u < n) by (pose proof (proj1 (Z.log2_lt_pow2 u k ltac:(lia)) ltac:(lia)); lia).
      rewrite (Z.bits_above_log2 u n ltac:(lia) LG). reflexivity. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.
Lemma zev_sc6 x0 : ltac2:(tb__ "0|0|
S1S5dS144Vx0;A1Vsc;A2S5dVsc;S143Vx0;A1A2A2S0S54S134S70Via';A1S6fVia';A1SfaVx0;A1A3S63Vsc;S60Z2Z6A2A2A3F_;").
Proof using Hi2 a c len q req.
  intros Hx0. pose proof SCR as SC. destruct x0; cbn [m1_lo m1_hi] in Hx0; cbn [e_sc6];
    [ | | | rewrite (ze_lit ia'); change (3008 mod 2 ^ 64) with (47 * 2 ^ 6); unfold sc in *; lia];
    rewrite (ze_alu ia'), z12, (ze_lit ia'); cbn [zalu]; change ((6 mod 2 ^ 64) mod 64) with 6; rewrite Z.shiftl_mul_pow2 by lia; apply Z.mod_small; lia.
Qed.
Lemma zev_bits x0 : ltac2:(tb__ "0|0|
S1S5dS144Vx0;A1Vsc;A2S5dVsc;S143Vx0;A1A2A2S0S54S134S70Via';A1S6fVia';A1Sf7Vx0;A1A3S5eS5eS5eS65Vc;Z1A2Z20A2S63Z40Vsc;A2A2Vlen;A2A3F_;").
Proof using Hgr Hi2 a q req.
  intros Hx0. pose proof cR as CR. pose proof SCR as SC. pose proof AF as (_ & _ & _ & _ & A5 & A6 & _).
  unfold e_bits. rewrite !(ze_alu ia'), (zev_sc6 x0 Hx0), z176, z177, !(ze_lit ia'). cbn [zalu].
  replace ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5) by reflexivity. change (32 mod 2 ^ 64) with 32.
  replace ((((c + -1 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64)) with (c - 1) by (Z.to_euclidean_division_equations; lia).
  rewrite Z.land_ones by lia. change (2 ^ 5) with 32. rewrite (Z.mod_small (c - 1) 32) by lia.
  rewrite !(Z.mod_small (sc * 2 ^ 6)) by lia. fold len. rewrite (Z.mod_small len) by lia. rewrite (Z.mod_small (c - 1)) by lia.
  assert (E1 : Z.lor (sc * 2 ^ 6) (c - 1) = (c - 1) + sc * 2 ^ 6).
  { rewrite Z.lor_comm. apply lor_add_high; lia. }
  rewrite E1. rewrite (Z.mod_small (c - 1 + sc * 2 ^ 6)) by lia.
  assert (E2 : Z.lor (c - 1 + sc * 2 ^ 6) len = (c - 1 + sc * 2 ^ 6) + (len / 4096) * 2 ^ 12).
  { replace len with ((len / 4096) * 2 ^ 12) at 1 by (Z.to_euclidean_division_equations; lia). apply lor_add_high; lia. }
  rewrite E2. rewrite Z.mod_small by (Z.to_euclidean_division_equations; lia). Z.to_euclidean_division_equations; lia.
Qed.
Lemma zev_usg : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1SfbA3S5eS85Via;A1Vc;A2A3").
Proof using Hi2.
  pose proof cR as CR. pose proof (usg_bounds ia Hi) as [UB _]. pose proof (ctx_ranges ia Hi) as (U0 & _).
  unfold e_usg. rewrite (ze_alu ia'), z192, z176. cbn [zalu]. apply Z.mod_small. lia.
Qed.
Lemma zev_ctr : ltac2:(tb__ "0|2|
S0S54S61S134S70Via';A1S6fVia';A1Sf8A3S60Z2Z20A2M0A2S69S5eS80Via;A1Z1M1A2S65G0G1A2A2A3").
Proof using Hi2.
  pose proof (ctx_ranges ia Hi) as (_ & _ & _ & _ & _ & CT).
  unfold e_ctr. rewrite (ze_alu ia'), (ze_ext ia'), z197, (ze_lit ia'). cbn [zalu]. change (Z.of_N 32) with 32.
  change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. change (1 mod 2 ^ 64) with 1.
  destruct (toS32_cases (ctr ia) ltac:(lia)) as [[LT E]|[GE E]]; rewrite E; Z.to_euclidean_division_equations; lia.
Qed.
Lemma zev_ab : ltac2:(tb__ "0|0|
S0S54S134S70Via';A1S6fVia';A1S100A3Va;A3").
Proof using Hi2 c len q req sc.
  pose proof aR as AR. pose proof cR as CR. unfold e_ab. rewrite (ze_alu ia'), z161, (ze_lit ia'). cbn [zalu]. rewrite (Z.mod_small a) by lia.
  replace ((31 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 5) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
End Arith.

Lemma firstn_nth_last {T} (l : list T) (n : nat) (d : T) : ltac2:(tb__ "0|0|
S0S4aS49VT;Vl;A2S50Vn;A1A3S0S44VT;A1Vl;S4bVT;S15eVT;Vn;Vl;A3S40VT;S15fVT;Vn;Vl;Vd;A4S48VT;A1A3A3A3F_;").
Proof using len req sc.
  revert n. induction l as [|y t IH]; intros [|n] H; cbn in *; try lia.
  - destruct t; [reflexivity | cbn in H; lia].
  - f_equal. apply IH. lia.
Qed.

Definition drop_last (x : m1v) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S2dS32VLf;A1S33VLf;A1S30VLf;A1S2fVLf;A1S34VLf;A1S15eSeS50S49S6dS13aVx;A1A2A1S17VLf;A1A3S2eVLf;A1S2bVLf;A1S31VLf;A1A9").

Section LeafT.
Variables (x : m1v) (Lf : sstate) (sT : wsub).
Hypothesis Hx : ltac2:(tb__ "0|0|
S1S5dS144Vx;A1Vsc;A2S5dVsc;S143Vx;A1A2A2").
Hypothesis CHK : ltac2:(tb__ "0|0|
S0S42SfcVx;VLf;A2S43A3").
Hypothesis CHK2 : ltac2:(tb__ "0|0|
S0S42S16Sf1Vx;VLf;A2A1S43A3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S42S196S145VLf;A1S166S165A1VsT;A3S43A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S42S198VsT;ScdA2S43A3").
Hypothesis SRES : ltac2:(tb__ "0|0|
S0SaS199VsT;S1a0A2SbZ0A1A3").
Variables (rho' : valuation) (tr : list event) (msF : machine_state) (md : Model).
Hypothesis Hag : ltac2:(tb__ "0|0|
S16aS71Via';VmZ;A2Vrho';A2").
Hypothesis HsmL : ltac2:(tb__ "0|0|
S20SccVrho';VLf;S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4").
Hypothesis HKc : Kc tr md.
Hypothesis Hmd : ltac2:(tb__ "0|0|
S0S180S182Vmd;A1VvmN;A3").

Definition stkF : sobj := hd O_map (ss_objs Lf).
Definition restF : list sobj := tl (ss_objs Lf).
Definition objsD : list sobj := ltac2:(tb__ "0|0|
S15eSeS49S6dS13aVx;A1A2Sc5A3").
Definition omapF : sobj := ltac2:(tb__ "0|0|
S15fSeS49S6dS13aVx;A1A2Sc5S1c3A4").
Definition dsF : list od2 := ltac2:(tb__ "0|0|
S153S13aVx;A1Sb5A2").
Definition stkc : list cell := ob_cells stkF.
Definition Lf1 : sstate := ltac2:(tb__ "0|0|
S2dS32VLf;A1S33VLf;A1S30VLf;A1S2fVLf;A1S34VLf;A1S40SeSb8Sb5A3S2eVLf;A1S2bVLf;A1S31VLf;A1A9").

Lemma CHK' : ltac2:(tb__ "0|2|
S1S0S44SeA1S17VLf;A1S40SeSb8S4bSeSb5S40SeSb7S48SeA1A3A3A3A3S1S0SeSb8S14dSbaA1A3S1S0S42S16cSb5S15dS6dSeS6eSb4A4M0A2S43A3S1S0S42Sb2SeS164S169A1G0A3S43A3S1S0S42Sb2S6dS14bSb4A3S43A3S1S0S42Sb2S6dS14aS144Vx;A1S143Vx;A1A2Sb4A3S43A3S1S0S44S6dA1S14cS13aVx;A1M1Sb4A2SeeVx;A1A3S1S0S42S16bSb7SefA2S43A3S1S0S42S16S145VLf;A1A1S43A3S1S0S19Sf1Vx;VLf;A2Sb9A3S1S0S4aS49SeSb5A2S49S6dG1A2A3S1Sb1S6dS72Sb4A3Sb1S6dS73Sb4A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof using CHK KN len md req sc tr.
  unfold leafT_chk in CHK. unfold Lf1, drop_last, stkc, dsF. unfold objsD, omapF. unfold stkF, restF.
  destruct (ss_objs Lf) as [|stk rest] eqn:EO; [discriminate|]. cbn [hd tl].
  apply andb_prop in CHK as [CHK C11]. apply andb_prop in CHK as [CHK C10].
  assert (IG : forall d l, existsb (od2_eqb d) l = true -> In d l).
  { intros d l H. apply existsb_exists in H as (d' & Hd' & E). apply od2_eqb_sound in E. subst d'. exact Hd'. }
  apply IG in C10. apply IG in C11.
  apply andb_prop in CHK as [CHK C9]. apply andb_prop in CHK as [CHK C8]. apply andb_prop in CHK as [CHK C7]. apply andb_prop in CHK as [CHK C6].
  apply andb_prop in CHK as [CHK C5]. apply andb_prop in CHK as [CHK C4]. apply andb_prop in CHK as [CHK C3]. apply andb_prop in CHK as [C1 C2].
  apply Nat.eqb_eq in C1. apply ods_eqb_sound in C7.
  split; [f_equal; exact (firstn_nth_last rest _ O_map C1)|]. split; [exact (stk_shape_sound stk C2)|].
  repeat (split; [assumption|]). cbn [firstn]. split; [reflexivity|]. split; [rewrite length_firstn; lia|]. split; assumption.
Qed.

Let EO := proj1 CHK'.
Let Estk := proj1 (proj2 CHK').
Let Cmatch := proj1 (proj2 (proj2 CHK')).
Let Cvars := proj1 (proj2 (proj2 (proj2 CHK'))).
Let Csem := proj1 (proj2 (proj2 (proj2 (proj2 CHK')))).
Let Ccond := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CHK'))))).
Let CdsC := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK')))))).
Let Comap := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK'))))))).
Let Cswf := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK')))))))).
Let ELf1 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK'))))))))).
Let Clen := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK')))))))))).
Let Cgot := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK'))))))))))).
Let Cguard := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CHK'))))))))))).
Lemma dsF_len : ltac2:(tb__ "0|0|
S0S4aS49S6dSb4A2S49S6dS13aVx;A1A2A3"). Proof using Clen. unfold dsF. apply fill2_length. exact Clen. Qed.

Lemma HromF : rom_ok segsU msF. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.
Lemma Erm : ltac2:(tb__ "0|0|
S0SceQ40A1S46SceQ8A1A1F_;S26Vrho';A1VmZ;A3"). Proof using Hag. exact (proj2 (proj2 Hag)). Qed.
Lemma E187 : ltac2:(tb__ "0|0|
S0SceQ40A1S14Vrho';SdPbbA1A2Sd7Vza;A1A3").
Proof using Clen Hag Hgr Hi.
  pose proof AF as (A1 & A2 & A3 & AC & A5 & _). cbn [eval]. rewrite (proj1 Hag 187%positive eq_refl). cbn [rho2 rw]. unfold rw2.
  cbn [rw2v Z.eqb Pos.eqb ia' set_R ia_Rz]. unfold wz. f_equal. apply Z.mod_small. lia.
Qed.
Lemma E177 : ltac2:(tb__ "0|0|
S0SceQ40A1S14Vrho';SdPb1A1A2Sd7Vlen;A1A3").
Proof using Hag. cbn [eval]. rewrite (proj1 Hag 177%positive eq_refl). reflexivity. Qed.
Lemma E190 : ltac2:(tb__ "0|1|
S0SceQ40M0A1S14Vrho';SdPbeA1A2ScfG0S77Via;Vm;A2A2A3").
Proof using Hag. cbn [eval]. rewrite (proj1 Hag 190%positive eq_refl). reflexivity. Qed.

Lemma RNG_T : ltac2:(tb__ "0|0|
S0S45S54S54A2S24Vrho';SefA2S41S54S54Vza;S5eVza;Vlen;A2A4A3").
Proof using Clen Hag Hgr Hi.
  pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & Ua & Un).
  unfold obj_range, obj_lo_of, obj_hi_of, omap_T. cbn [ob_base ob_lo ob_hi]. rewrite E187, Ua, soff_lit_small by lia.
  unfold soff. rewrite E177. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold wz. rewrite u64, toS_small by lia. f_equal; lia.
Qed.
Lemma RNG_F : ltac2:(tb__ "0|0|
S0S45S54S54A2S24Vrho';Sb7A2S41S54S54Vza;S5eVza;Vlen;A2A4A3").
Proof using Clen Comap Hag Hgr Hi. rewrite (obj_range_match rho' omapF omap_T Comap). exact RNG_T. Qed.

Definition mA : word -> option byte := ltac2:(tb__ "0|0|
S1c0Vrho';S40SeSb7S48SeA1A3VmsF;A3").
Definition rhoA : valuation := ltac2:(tb__ "0|0|
S35S15Vrho';A1S1fVrho';A1Sb6A3").
Lemma relA : ltac2:(tb__ "0|5|
S1S20SccSbcSb9S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4S1SceQ40A1M0S3S197Vrho';S40SeSb7S48SeA1A3M1R1A3M2A1S0S46SceQ8A1A1M3Sb6R2A1M4S26Vrho';R2A2A3F_;Fa;S1G0G2S0G3G4S192VmsF;R2A2A3F_;Fa;S160SeS22SccVrho';VmsF;A3G1A3A2A2A2").
Proof using CHK2 ELf1 EO HsmL.
  pose proof (smatch_release_suffix segsU rho' Lf tr msF md (stkF :: objsD) [omapF] (ss_next Lf) HsmL EO) as R. cbn zeta in R.
  apply R. change (swf Lf1 = true). rewrite <- ELf1. exact CHK2.
Qed.
Lemma in_omap a : ltac2:(tb__ "0|0|
S1S5dZ0Va;A2S5fVa;S60Z2Z40A2A2A2S7S197Vrho';S40SeSb7S48SeA1A3ScfQ40Va;A2A3S1S5dVza;Va;A2S5fVa;S5eVza;Vlen;A2A2A2A2F_;").
Proof using Clen Comap Hag Hgr Hi.
  intros Ha. unfold in_ranges. rewrite u64 by lia. split.
  - intros (o & [<-|[]] & R). rewrite RNG_F in R. cbn [fst snd] in R. exact R.
  - intros R. exists omapF. split; [left; reflexivity|]. rewrite RNG_F. cbn [fst snd]. exact R.
Qed.
Lemma mA_out a : ltac2:(tb__ "0|1|
S1S5dZ0Va;A2S5fVa;S60Z2Z40A2A2A2S3S1S5dVza;Va;A2S5fVa;S5eVza;Vlen;A2A2A2A1S0S46SceQ8A1A1Sb6ScfQ40Va;A2M0A1VmWc;G0A1A3F_;F_;").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi HsmL.
  intros Ha Hn. rewrite (proj1 (proj2 relA)); [|intros I; apply Hn; apply (in_omap a Ha); exact I].
  rewrite Erm. exact (m1_out ia Hi za mWc Hgr a Ha Hn).
Qed.
Lemma mA_in a : ltac2:(tb__ "0|1|
S1S5dZ0Va;A2S5fVa;S60Z2Z40A2A2A2S1S5dVza;Va;A2S5fVa;S5eVza;Vlen;A2A2A2S0S46SceQ8A1A1Sb6ScfQ40Va;A2M0A1S192VmsF;G0A2A3F_;F_;").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi HsmL. intros Ha R. apply (proj1 (proj2 (proj2 relA))). apply (in_omap a Ha). exact R. Qed.
Lemma HO_map : ltac2:(tb__ "0|0|
S22SccVrho';VmsF;SefA4").
Proof using CHK2 Comap ELf1 EO HsmL. apply (obj_holds_match segsU rho' msF omapF omap_T Comap). exact (Forall_inv (proj2 (proj2 (proj2 relA)))). Qed.

Lemma HLVA : ltac2:(tb__ "0|0|
S7eVia';Vcur;VL;Sb6Vvm;A5").
Proof using CHK2 Clen Comap ELf1 EO HLV Hag Hgr Hi HsmL. exact (liveX ia Hi za cur mWc HLV Hgr mA mA_out). Qed.
Lemma HagA : ltac2:(tb__ "0|0|
S16aS71Via';Sb6A2SbcA2").
Proof using Hag. destruct Hag as (AW & AL & AM). split; [exact AW|]. split; [exact AL|]. reflexivity. Qed.

Lemma HSF_objs : ltac2:(tb__ "0|0|
S0S44SeA1S17Sb9A1S40SeS14dSbaA1Sb5A3A3"). Proof using Estk. cbn [Lf1 ss_objs]. rewrite <- Estk. reflexivity. Qed.
Lemma HsmA : ltac2:(tb__ "0|0|
S20SccSbcSb9S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4"). Proof using CHK2 ELf1 EO HsmL. exact (proj1 relA). Qed.
Lemma Hcond : ltac2:(tb__ "0|0|
S6dSb1S6dR1Sb4A3S159S74Via';A1R2A2F_;Fd;").
Proof using Ccond Hx. intros d Hd. apply (dcond2b_sound (m1_lo x) (m1_hi x)); [exact Hx | exact (proj1 (forallb_forall _ _) Ccond d Hd)]. Qed.
Lemma HdsF_T : ltac2:(tb__ "0|0|
S6dSb1S6dR1Sb4A3S14eVia';R2A2F_;Fd;"). Proof using Ccond Csem Cvars Hx. exact (HdsF ia' dsF Cvars Csem Hcond). Qed.

Lemma CF : ctx_frame s1 cur. Proof using Ecur Hi. rewrite Ecur. exact (proj2 (mm_inv ia Hi)). Qed.
Lemma HEA : ltac2:(tb__ "0|0|
Sd5Sd2S112SccSb6A2SceQ40A1S43L_;A2Sd4Sd1A1U4S82Via;A1A4").
Proof using CHK2 Clen Comap ELf1 EO HE HLV Hag Hgr Hi HsmL.
  intros j Hj. pose proof (HE j Hj) as E. rewrite errno_U in *. unfold byteview_of in *.
  rewrite (rd_of_mem segsU mA mWc); [exact E|]. apply mA_out; [lia|]. apply (IMG ia za cur mWc HLV Hgr). cbn [mc_img_lo mc_img_hi C_U]. lia.
Qed.
Lemma Hent : ltac2:(tb__ "0|0|
S6dSb1S6dR1Sb4A3S4S7fVia';Vcur;Sb6R2A4Sb1S6dR2SeeVx;A1A3A2F_;Fd;").
Proof using CHK2 CdsC Clen Comap ELf1 EO Ecur HE HLV Hag Hgr Hi2 HsmL Hx.
  intros d Hd. rewrite <- CdsC. apply (ent_changed2 (od2_entry ia' cur mA) (dsM23 x) dsF).
  - exact dsF_len.
  - exact (dsP_entry ia' Hi2 x cur mA Hx CF HEA).
  - exact Hd.
Qed.

Lemma Hent_hold : ltac2:(tb__ "0|0|
S6dSb1S6dR1Sb4A3S7fVia';Vcur;Sb6R2A4S22SccS150Via';Sb6A2S177VmsF;Sb6A2S6eR3A1A4F_;F_;Fd;").
Proof using CHK2 Clen Comap ELf1 EO HLV Hag Hgr Hi2 HsmL. intros d _ Hok. exact (od2_hold ia' Hi2 cur L mA vm HLVA msF HromF d Hok). Qed.
Lemma HdsC_sub : ltac2:(tb__ "0|0|
S6dSb1S6dR1SeeVx;A1A3S1Sb1S6dR2Sb4A3S0S46S55A1S14fR2A1S4cS55A1A3A2F_;Fd;").
Proof using CdsC.
  intros d Hd. split; [rewrite <- CdsC in Hd; exact (changed2_sub _ _ d Hd)|].
  destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
Qed.
Lemma EmA : ltac2:(tb__ "0|0|
S0SceQ40A1S46SceQ8A1A1F_;S26S150Via';Sb6A2A1Sb6A3"). Proof using ia za. reflexivity. Qed.

Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S16dS6dS6eVmsF;SbcSb4A5").
Definition touchedD : Z -> Prop := ltac2:(tb__ "0|0|
S16eS6dS148Via';A1S149Via';A1SeeVx;A1A4").
Let bvA : byteview := ltac2:(tb__ "0|0|
Sd2S112SccSb6A2S113SccSb6A2A2").
Let rvA : byteview := ltac2:(tb__ "0|0|
Sd2S112SccSb6A2SceQ40A1S43L_;A2").
Let bv1 : byteview := ltac2:(tb__ "0|0|
Sd2S112SccSbbA2S113SccSbbA2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
Sd2S112SccSbbA2SceQ40A1S43L_;A2").

Lemma V1D : ltac2:(tb__ "0|1|
S54S1S5dZ0R1A2S5fR1S60Z2Z40A2A2A2S3Sc2R2A1A1S1S0S46S54A1M0Vbv1;R3A1VbvA;R3A1A3S0G0Vrv1;R3A1VrvA;R3A1A3A2F_;F_;Fy;").
Proof using CHK2 Ccond CdsC Clen Cmatch Comap Csem Cvars ELf1 EO Ecur Estk HE HLV Hag Hgr Hi2 HsmL Hx.
  exact (V1 segsU (rhoR ia' mA) (zr2 ia') (zl2 ia') (Hzr2 ia' mA) (Hzl2 ia' mA) od2 obj_of2 (dlo2 ia') (dhi2 ia') (dcells2 (ia_sc ia')) drom2 (DS2 ia') mA EmA
           (rngD ia' Hi2 mA) (range64D ia' Hi2) (cellsD ia' Hi2 mA) (cellsInD ia' Hi2) (semD ia' Hi2 mA) (coverD ia' Hi2) (dunkD ia') (romD ia' Hi2 cur L mA vm HLVA)
           msF HromF tr md msF rhoA HagA Lf1 (oStkF stkc) objsD dsF (dsC_T x) HSF_objs Cmatch HsmA HdsF_T (od2_entry ia' cur mA) Hent Hent_hold).
Qed.
Lemma VMD : ltac2:(tb__ "0|0|
S54S1S5dZ0R1A2S5fR1S60Z2Z40A2A2A2Sc2R2A1S3S0S46S54A1Vbv1;R3A1S4cS54A1A3A1F_;F_;Fy;").
Proof using CHK2 Ccond CdsC Cmatch Csem Cvars ELf1 EO Estk Hag Hi2 HsmL Hx.
  exact (VM segsU (rhoR ia' mA) od2 obj_of2 (dlo2 ia') (dhi2 ia') drom2 (DS2 ia') (rngD ia' Hi2 mA) (dunkD ia') tr md msF rhoA HagA Lf1 (oStkF stkc) objsD dsF (dsC_T x) HSF_objs Cmatch HsmA HdsF_T HdsC_sub).
Qed.
Definition cell_from_odD : ltac2:(tb__ "0|3|
S6dS54S4aSaS114S54Sb1S6dR6SeeVx;A1A3Sb1S45S45S54S4aA2M0SaA2S41G0SaS41S54S4aR6R5A4R4A4S152S74Via';A1R7A2A3S0S54S117SedS119R4A1A2S5eS148Via';R8A2R7A2A3S0S4aS11eR5A1R7A3S0S46S54A1S193SedR6A2S47S54R5A2A3S0S54S61R6S60Z2S63Z8S62R9A1A2A2M1A2S61S134S70Via';A1S6fVia';A1R8A3G1A2A3S11fSedSd2S112SccS16dS6dS6eVmsF;SbcSb4A5M2A2S113SccG2A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S16fSccS150Via';Sb6A2S70Via';A1S6fVia';A1S156Via';Sb6A2S155Via';Sb6A2S6dS6eS148Via';A1S149Via';A1S152S74Via';A1A1S14fS14eVia';A1S151Via';VHi2;Sb6A3S15bVia';VHi2;A2S157Via';VHi2;Sb6A3S158Via';VHi2;A2S15cVia';VHi2;Sb6A3S15aVia';A1Vtr;Vmd;VmsF;SbcSc0Sb9S14dSbaA1Sb5Sb4SeeVx;A1Sc7VCmatch;Sc9Sc1Sc8SedA23").
Definition m'_inD : ltac2:(tb__ "0|1|
S6dS54Sb1S6dR2Sb4A3S1S5dS148Via';R3A2R2A2S5fR2S149Via';R3A2A2A2S1S5dZ0R3A2S5fR3S60Z2Z40A2A2A2S0S46SceQ8A1A1S16dS6dS6eVmsF;SbcSb4ScfQ40R4A2M0A6S192VmsF;G0A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|0|
S170S150Via';Sb6A2S6dS6eS148Via';A1S149Via';A1S14eVia';A1S151Via';VHi2;Sb6A3VmsF;SbcSc0Sb4Sc1Ac").
Definition m'_outD : ltac2:(tb__ "0|1|
S54S1S5dZ0R1A2S5fR1S60Z2Z40A2A2A2S6dSb1S6dR1Sb4A3S3S1S5dS148Via';R2A2R4A2S5fR4S149Via';R2A2A2A2A1F_;Fd;S0S46SceQ8A1A1S16dS6dS6eVmsF;SbcSb4ScfQ40R3A2M0A6Sb6G0A1A3F_;F_;Fx;") := ltac2:(tb__ "0|0|
S171S150Via';Sb6A2S6dS6eS148Via';A1S149Via';A1S14eVia';A1Sb6Sc6S151Via';VHi2;Sb6A3VmsF;SbcSc0Sb4Sc1Ae").
Definition touchedD_dec : ltac2:(tb__ "0|1|
S54S1acS16eS6dS148Via';A1S149Via';A1SeeVx;A1R1A5M0S3G0A1A2Fx;") := ltac2:(tb__ "0|0|
S172S6dS148Via';A1S149Via';A1SeeVx;A1A4").

Definition touched (y : Z) : Prop := ltac2:(tb__ "0|0|
S4Sc2Vy;A1S1S5dVza;Vy;A2S5fVy;S5eVza;Vlen;A2A2A2A2").
Lemma touched_dec y : ltac2:(tb__ "0|1|
S1acSbeVy;A1M0S3G0A1A2").
Proof using Clen.
  unfold touched. destruct (touchedD_dec y) as [T|T]; [left; left; exact T|].
  destruct (Z_le_dec za y); [destruct (Z_lt_dec y (za + len)); [left; right; lia|]|]; right; intros [H|H]; try exact (T H); lia.
Qed.

Lemma od2_not_fresh d y : ltac2:(tb__ "0|0|
S14eVia';Vd;A2S1S5dS148Via';Vd;A2Vy;A2S5fVy;S149Via';Vd;A2A2A2S3S1S5dVza;Vy;A2S5fVy;S5eVza;Vlen;A2A2A2A1F_;F_;").
Proof using Clen Hgr Hi LMI m.
  intros Hd R. pose proof (m_R ia Hi) as MR. top_ranges. pose proof SCR as SC.
  unfold dlo2, dhi2, od2_range, od2_rangeP in R.
  destruct d; cbn [fst snd mc_tp C_U ia_sc ia_m ia' set_R] in R; try (apply (IMG ia za cur mWc HLV Hgr); cbn [mc_img_lo mc_img_hi C_U]; unfold sc in *; lia).

  apply (FP ia za cur mWc HLV Hgr).
  destruct (key_area (m :: ia_X ia) (ia_R ia) (ia_U ia) cur (mig_I LMI) m Lkey) as (ar & k & Har & Hk & Em).
  exists (e_area ar). split; [exact (e_area_In cur ar Har)|]. unfold e_area. cbn [fst snd].
  assert (R' : addr_of L m + 0 <= y < addr_of L m + 40) by (rewrite Lma; exact R). clear R. rewrite Em in R'.
  unfold addr_of, loc_addr in *. destruct ar; cbn [padd prid poff] in *.
  unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. unfold L in *. lia.
Qed.
Lemma mF_fresh y : ltac2:(tb__ "0|1|
S1S5dVza;Vy;A2S5fVy;S5eVza;Vlen;A2A2A2S0S46SceQ8A1A1SbbScfQ40Vy;A2M0A1S192VmsF;G0A2A3F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI m.
  intros R. pose proof AF as (A1 & A2 & A3 & AC & A5 & _). assert (Hy : 0 <= y < 2 ^ 64) by lia.
  unfold mF. rewrite (m'_outD y Hy); [exact (mA_in y Hy R)|]. intros d Hd Rd. exact (od2_not_fresh d y (HdsF_T d Hd) Rd R).
Qed.
Lemma fresh_views y : ltac2:(tb__ "0|1|
S1S5dVza;Vy;A2S5fVy;S5eVza;Vlen;A2A2A2S1S0S46SceQ8A1A1S112SccSbbScfQ40Vy;A2M0A3S2aVmsF;G0A2A3S0S42S113SccSbbG0A3S43A3A2F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI m.
  intros R. pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & Ua & _). pose proof (mF_fresh y R) as E.
  split; [exact (rd_of_at segsU mF msF _ HromF E)|]. apply (wok_of_at segsU mF msF _ E).
  pose proof HO_map as (_ & Hw & _). unfold obj_lo_of, obj_hi_of, omap_T in Hw. cbn [ob_base ob_lo ob_hi ob_dflt] in Hw.
  pose proof RNG_T as RG. unfold obj_range, obj_lo_of, obj_hi_of, omap_T in RG. cbn [ob_base ob_lo ob_hi] in RG.
  rewrite E187, Ua in Hw, RG. injection RG as RG1 RG2. replace y with (za + (y - za)) by lia.
  apply Hw; [lia | reflexivity].
Qed.

Lemma fresh_ptr j : ltac2:(tb__ "0|3|
S17bVj;U8M0A2S0S46SceQ8M1A1M2A1S2aVmsF;ScfQ40S5eVza;S62Vj;A1A2A2A2S47G2ScfG1S123S77Via;Vm;A2G0Vj;A3A2A2A3F_;").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi HsmL.
  intros Hj. pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & Ua & _).
  pose proof (cell_bytes_sym segsU rho' msF omap_T c_mp j HO_map ltac:(right; left; reflexivity) ltac:(cbn; lia)) as B.
  cbn [ob_base omap_T c_off c_val c_width c_mp] in B. rewrite E187, Ua, soff_lit_small, E190 in B by lia. rewrite Z.add_0_r in B.
  rewrite B. change (Z.to_nat 8) with 8%nat. rewrite nth_enc_bytes by lia. reflexivity.
Qed.
Lemma fresh_ab : ltac2:(tb__ "0|2|
S0S46SceQ8M0A1M1A1S2aVmsF;ScfQ40S5eVza;Z8A2A2A2S47G1ScfG0S7bVia;A1A2A2A3").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi2 HsmL.
  pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & Ua & _). pose proof aR as AR. pose proof cR as CR.
  pose proof (cell_bytes_sym segsU rho' msF omap_T c_ab 0 HO_map ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
  cbn [ob_base omap_T c_off c_val c_width c_ab] in B. rewrite E187, Ua, soff_lit_small in B by lia. rewrite Z.add_0_r in B.
  rewrite (EVw ia' mZ rho' e_ab Hag eq_refl eq_refl), zev_ab in B. rewrite B. change (Z.to_nat 1) with 1%nat. rewrite nth_enc_bytes by lia.
  f_equal. f_equal. unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_small; lia.
Qed.
Lemma fresh_zero y : ltac2:(tb__ "0|2|
S1S5dS5eVza;Z9A2Vy;A2S5fVy;S5eVza;Vlen;A2A2A2S0S46SceQ8M0A1M1A1S2aVmsF;ScfQ40Vy;A2A2S47G1ScfG0Z0A2A2A3F_;").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi HsmL.
  intros R. pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & Ua & _).
  pose proof HO_map as (_ & _ & _ & Hd & _). unfold obj_lo_of, obj_hi_of, omap_T in Hd. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Hd.
  pose proof RNG_T as RG. unfold obj_range, obj_lo_of, obj_hi_of, omap_T in RG. cbn [ob_base ob_lo ob_hi] in RG.
  rewrite E187, Ua in Hd, RG. injection RG as RG1 RG2.
  specialize (Hd (y - za) ltac:(lia)). replace (za + (y - za)) with y in Hd by lia. apply Hd.
  intros C. unfold covered in C. apply Exists_exists in C as (c & Hc & IC). unfold in_cell in IC.
  destruct Hc as [<-|[<-|[]]]; cbn [c_off c_width c_ab c_mp] in IC; rewrite soff_lit_small in IC by lia; lia.
Qed.

Lemma bv1_fresh_ptr j : ltac2:(tb__ "0|1|
S17bVj;U8M0A2S0S46S54A1Vbv1;S5eVza;S62Vj;A1A2A1S47S54S123S77Via;Vm;A2G0Vj;A3A2A3F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI.
  intros Hj. pose proof AF as (A1 & A2 & A3 & AC & A5 & _). destruct (fresh_views (za + Z.of_nat j) ltac:(lia)) as [E1 E2].
  unfold bv1, byteview_of. replace ((0 <=? za + Z.of_nat j) && (za + Z.of_nat j <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E2, E1, (fresh_ptr j Hj). cbn [andb]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. apply le_byte_range.
Qed.
Lemma bv1_fresh_ab : ltac2:(tb__ "0|0|
S0S46S54A1Vbv1;S5eVza;Z8A2A1S47S54S7bVia;A1A2A3").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI.
  pose proof AF as (A1 & A2 & A3 & AC & A5 & _). pose proof aR as AR. pose proof cR as CR. destruct (fresh_views (za + 8) ltac:(lia)) as [E1 E2].
  unfold bv1, byteview_of. replace ((0 <=? za + 8) && (za + 8 <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E2, E1, fresh_ab. cbn [andb]. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. lia.
Qed.
Lemma bv1_fresh_zero y : ltac2:(tb__ "0|0|
S1S5dS5eVza;Z9A2Vy;A2S5fVy;S5eVza;Vlen;A2A2A2S0S46S54A1Vbv1;Vy;A1S47S54Z0A2A3F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI m.
  intros R. pose proof AF as (A1 & A2 & A3 & AC & A5 & _). destruct (fresh_views y ltac:(lia)) as [E1 E2].
  unfold bv1, byteview_of. replace ((0 <=? y) && (y <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite E2, E1, (fresh_zero y R). reflexivity.
Qed.
Lemma bv1_fresh_some y : ltac2:(tb__ "0|0|
S1S5dVza;Vy;A2S5fVy;S5eVza;Vlen;A2A2A2S3S0S46S54A1Vbv1;Vy;A1S4cS54A1A3A1F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx LMI m.
  intros R. pose proof AF as (A1 & A2 & A3 & AC & A5 & _).
  destruct (Z_lt_dec y (za + 8)) as [LT|GE].
  - replace y with (za + Z.of_nat (Z.to_nat (y - za))) by lia. rewrite (bv1_fresh_ptr (Z.to_nat (y - za)) ltac:(lia)). discriminate.
  - destruct (Z.eq_dec y (za + 8)) as [->|NE]; [rewrite bv1_fresh_ab; discriminate|]. rewrite (bv1_fresh_zero y ltac:(lia)). discriminate.
Qed.

Lemma amL_maplen : ltac2:(tb__ "0|1|
S1S0S54SaaSf0A1S64Vlen;Z1000A2M0A3S5dZ1G0A2A2"). Proof using Clen Hgr Hi. pose proof AF as (_ & _ & _ & _ & A5 & A6 & _). split; [reflexivity|]. apply Z.div_le_lower_bound; lia. Qed.
Lemma amL_stride : 16 <= stride_of amL.
Proof using Clen Hgr Hi.
  pose proof (isize_range ia Hi) as IR. pose proof amL_maplen as [EM PM]. pose proof AF as (_ & _ & _ & _ & A5 & A6 & _).
  unfold stride_of. rewrite EM. change (am_sc amL) with sc. change (class_size sc) with (isize ia).
  destruct ((am_last amL =? 0) && negb (len / 4096 =? 0))%bool; [|lia]. unfold UNIT. Z.to_euclidean_division_equations; nia.
Qed.
Lemma new_cells c : ltac2:(tb__ "0|1|
S4Sb1S114Vc;S128Vm;Sf0A2A3Sb1S114Vc;S190Sf0A1A3A2S4S0S114Vc;S122S11cS1aeVcur;A1M0A1U8S12eVm;A1A3A3S4S0S114Vc;S122S11cS9eG0Z8A2A1U4S127S7bVia;A1A1A3A3S1S0S133S129Vc;A1S127Z0A1A3S5S8cS8cS1S0S116S119Vc;A1S11cR1A1A3S1S0S4aSa3R1A1S19bVcur;A1A3S5dZcSadR1A1A2A2A2Lp;A2A2A2A2F_;").
Proof using Clen Hgr Hi.
  pose proof amL_stride as ST. pose proof amL_maplen as [EM PM].
  intros [Hc|Hc].
  - rewrite (group_cells_eq m amL) in Hc. destruct Hc as [<-|[<-|Hc]]; [left; reflexivity | right; left |].
    + unfold ImageDelta.aidx_cell. rewrite EM. replace (len / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + right; right. apply in_flat_map in Hc as (i & Hi0 & Hc). apply In_zseq in Hi0.
      assert (SL : nth_slot amL i = slot_zero \/ nth_slot amL i = slot_junk).
      { unfold nth_slot, amL, gg_amL, ig_am. cbn [am_slots am_set_links].
        destruct (nth_in_or_default (Z.to_nat i) (repeat slot_zero (Z.to_nat (icnt ia))) slot_junk) as [H|H]; [left; apply repeat_spec in H; exact H | right; exact H]. }
      assert (Hsi : 0 <= stride_of amL * i) by nia.
      unfold slot_cells, slot_start in Hc. change (am_mem amL) with (memN cur) in Hc. unfold memN, UNIT in Hc. cbn [padd] in Hc.
      destruct SL as [SL|SL]; rewrite SL in Hc; cbn [ss_hdr ss_fr slot_zero slot_junk app] in Hc;
        [destruct Hc as [<-|[<-|[<-|[]]]] | destruct Hc as [<-|[]]];
        cbn [mc_val mc_loc]; (split; [reflexivity|]); eexists; (split; [reflexivity|]); cbn [prid poff]; (split; [reflexivity | lia]).
  - unfold amL in Hc. rewrite (gg_group_footer_cellsZ m (memN cur) sc (icnt ia) aidx (len / 4096)) in Hc. fold amL in Hc.
    destruct Hc as [<-|[]]. right; right. split; [reflexivity|]. unfold trailing_cell, trailing_loc. change (am_mem amL) with (memN cur). change (am_last amL) with (icnt ia - 1).
    unfold memN, UNIT, IB. cbn [mc_loc padd]. eexists. split; [reflexivity|]. cbn [prid poff]. pose proof (iplan_range ia Hi) as [CR _]. split; [reflexivity | nia].
Qed.

Lemma m_below : ltac2:(tb__ "0|0|
S17bSa3Vm;A1S19bVcur;A1A2"). Proof using LMI PV. exact (key_below (m :: X) None U cur LI m Lkey). Qed.
Lemma L'_m : ltac2:(tb__ "0|0|
S0S54Sd3SedVm;A2S77Via;Vm;A2A3").
Proof using LMI PV. pose proof (gL'_addr_of cur L za m m_below) as E. unfold gL', MapGrow.gr in E. unfold L', nr_id. rewrite E. exact Lma. Qed.
Lemma L'_ctx : ltac2:(tb__ "0|0|
S0S54S124SedA1S124VL;A1A3"). Proof using . reflexivity. Qed.
Lemma L'_memN : ltac2:(tb__ "0|0|
S0S54Sd3SedS1aeVcur;A1A2Vza;A3").
Proof using Clen. unfold L', memN, addr_of, loc_addr. cbn [prid poff]. rewrite Lext_reg. lia. Qed.

Let I' : astate -> Prop := ltac2:(tb__ "0|0|
S11bVX;S47S45S8cS54A2S41S8cS54Vm;Z0A4A2VU;A3").
Lemma HMI0 : ltac2:(tb__ "0|0|
S1b2Sd1S11bS40S8cVm;VX;A3S4cS45S8cS54A2A1VU;A3S186Vcur;VL;A2S112SccSb6A2S113SccSb6A2Vvm;A6").
Proof using CHK2 Clen Comap ELf1 EO HLV Hag Hgr Hi HsmL PV. pose proof (lv_MI ia' cur L mA vm HLVA) as H. unfold MInvI in H. cbn [ia' set_R ia_X ia_R ia_U] in H. rewrite pX, pU, pR in H. exact H. Qed.

Definition NEW : list (loc * Z) := ltac2:(tb__ "0|1|
S40S45S116S54A2M0S1afVcur;Vlen;A2S48G0A1A3").
Lemma Hfp e : ltac2:(tb__ "0|1|
Sb1S45S116S54A2M0Ve;S11aSecA1A3S4Sb1G0Ve;S11aVcur;A1A3Sb1G0Ve;Sc3A3A2F_;").
Proof using . rewrite post_fp. intros H. apply in_app_iff in H as [H|H]; [left; exact H | right; exact H]. Qed.
Lemma FPO e : ltac2:(tb__ "0|2|
Sb1S45S116S54A2M0Ve;S11aVcur;A1A3Sb1G0Ve;S11aSecA1A3S0S54S117SedS51S116S54Ve;A3M1A2S117VL;G1A2A3F_;F_;").
Proof using LMI PV. intros He _. exact (gL'_fp (m :: X) None U cur L za LI e He). Qed.
Lemma UBO b : ltac2:(tb__ "0|1|
Sb1S45S8cS54A2Vb;S120Vcur;A1A3S0S54S117SedS11cS51S8cS54Vb;A3A1M0A2S117VL;G0A2A3F_;").
Proof using LMI PV. intros Hb. exact (gL'_ub (m :: X) None U cur L za LI LXr b Hb). Qed.
Lemma NEWT e y : ltac2:(tb__ "0|1|
Sb1S45S116S54A2Ve;Sc3A3S1S5dS117SedS51S116S54Ve;A3A2M0Vy;A2S5fVy;S5eG0S4fS116S54Ve;A3A2A2A2SbeVy;A1F_;F_;").
Proof using Clen. intros [<-|[]] Hy. right. unfold geN' in Hy. cbn [fst snd] in Hy. change (loc_addr L' (LMem (SP (length (st_regions cur)) 0))) with (addr_of L' (memN cur)) in Hy. rewrite L'_memN in Hy. exact Hy. Qed.

Lemma V1 y : ltac2:(tb__ "0|2|
S1S5dZ0Vy;A2S5fVy;S60Z2Z40A2A2A2S3SbeVy;A1A1S1S0S46S54A1M0Vbv1;Vy;A1Sd2S112SccSb6A2M1S113SccSb6A2Vy;A3A3S0G0Vrv1;Vy;A1Sd2G1SceQ40A1S43L_;Vy;A3A3A2F_;F_;").
Proof using CHK2 Ccond CdsC Clen Cmatch Comap Csem Cvars ELf1 EO Ecur Estk HE HLV Hag Hgr Hi2 HsmL Hx. intros Hy NT. apply (V1D y Hy). intros T. apply NT. left. exact T. Qed.

Lemma VM y : ltac2:(tb__ "0|0|
S1S5dZ0Vy;A2S5fVy;S60Z2Z40A2A2A2SbeVy;A1S130SedSecVy;A3S3S0S46S54A1Vbv1;Vy;A1S4cS54A1A3A1F_;F_;F_;").
Proof using CHK2 Ccond CdsC Clen Cmatch Comap Csem Cvars ELf1 EO Estk Hag Hgr Hi2 HsmL Hx LMI. intros Hy [T|T] _; [exact (VMD y Hy T) | exact (bv1_fresh_some y T)]. Qed.

Lemma NOSTAT y : ltac2:(tb__ "0|2|
SbeVy;A1S1S5dSe1Sd1A1Vy;A2S5fVy;Se0Sd1A1A2A2S4S1S5dSd8Sd1A1M0Vy;A2S5fVy;S5eG0S121A2A2A2S1S5dSd4Sd1A1M1Vy;A2S5fVy;S5eG1Z4A2A2A2A2F_;F_;").
Proof using Clen HLV Hgr Hi I'.
  intros [T|T] Himg.
  - destruct T as (d & Hd & R). pose proof (m_R ia Hi) as MR. top_ranges. pose proof SCR as SC.
    unfold dlo2, dhi2, od2_range, od2_rangeP in R.
    destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd mc_tp C_U ia_sc ia_m ia' set_R D_mT] in R; cbn [mc_img_lo mc_img_hi mc_ctx C_U] in *; unfold mc_errno; cbn [mc_tp C_U]; unfold CTX_SIZE; unfold sc in *; try lia.
    exfalso. change (zA ia' (ia_m ia)) with (zA ia (ia_m ia)) in R. lia.
  - exfalso. exact (IMG ia za cur mWc HLV Hgr y Himg T).
Qed.
Lemma HSD y : ltac2:(tb__ "0|d|
S4S1S5dSd8Sd1A1M0Vy;A2S5fVy;S5eG0S121A2A2A2S1S5dSd4Sd1A1M1Vy;A2S5fVy;S5eG1Z4M2A2A2A2A2S1S3S1S5dSe2Sd1A1M3Vy;A2S5fVy;S5eG3Z38A2A2A2A1S1S3S1S5dSe5Sd1A1M4Vy;A2S5fVy;S5eG4G2A2A2A2A1S1S3S1S5dSe3Sd1A1M5Vy;A2S5fVy;S5eG5G2A2A2A2A1S1S3S1S5dSe6Sd1A1M6Vy;A2S5fVy;S5eG6Z60A2A2A2A1S1S3S1S5dSe7Sd1A1M7Vy;A2S5fVy;S5eG7Z1bA2A2A2A1S1S3S1S5dSe4Sd1A1M8Vy;A2S5fVy;S5eG8G2A2A2A2A1S1S3S1S5dSdfSd1A1M9Vy;A2S5fVy;S5eG9Z20A2A2A2A1S1S3S1S5dSdeSd1A1MaVy;A2S5fVy;S5eGaZ8MbA2A2A2A1S3S1S5dSddSd1A1McVy;A2S5fVy;S5eGcGbA2A2A2A1A2A2A2A2A2A2A2A2F_;").
Proof using Clen I' cur.
  intros Hy. unfold mc_errno in Hy. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
  unfold CTX_SIZE in Hy. lia.
Qed.

Definition gmeets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S5S4aS4aS1S17bR1S11eVc;A1A2SbeS5eS117SedS119Vc;A1A2S62R1A1A2A1A2Lk;A2").

Lemma region_post : ltac2:(tb__ "0|0|
S0S46S90A1S125SecS19bVcur;A1A2S47S90Sa2Sa0Vlen;S48S54A1S43A4A2A3").
Proof using Clen I'. unfold region_of. rewrite post_regs. unfold nr_id. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma new_cell_range c : ltac2:(tb__ "0|1|
S4Sb1S114Vc;S128Vm;Sf0A2A3Sb1S114Vc;S190Sf0A1A3A2S1S5dVza;S117SedS119Vc;A1A2M0A2S5dS5eG0S62S11eVc;A1A1A2S5eVza;Vlen;A2A2A2F_;").
Proof using Clen Ecur Harm Hgr Hi I' PV.
  intros Hc. destruct (group_cell_in X (Some (m, 0)) U post L' post_I m amL c (proj1 post_used) Hc) as (rg & Hr & _ & _ & _ & RI & _).
  change (am_mem amL) with (memN cur) in Hr, RI. unfold memN in Hr, RI. cbn [prid] in Hr, RI. rewrite region_post in Hr. injection Hr as <-.
  unfold range_incl, cell_range, crange, e_reg in RI. cbn [fst snd rg_len] in RI.
  change (loc_addr L' (LMem (SP (nr_id cur) 0))) with (addr_of L' (memN cur)) in RI. rewrite L'_memN in RI. lia.
Qed.

Lemma trailing_In : ltac2:(tb__ "0|0|
Sb1S114S191Sf0A1S190Sf0A1A3").
Proof using . unfold amL. rewrite (gg_group_footer_cellsZ m (memN cur) sc (icnt ia) aidx (len / 4096)). left. reflexivity. Qed.

Theorem OLD c : ltac2:(tb__ "0|2|
Sb1S114Vc;S4bS114S11dSecA1S18fSecA1A3A3S3Sc4Vc;A1A1S1Sb1S114Vc;S4bS114S11dVcur;A1S18fVcur;A1A3A3S1S0S54S117SedS119Vc;A1M0A2S117VL;G0A2A3S0S54S12aSedS129Vc;A1M1A2S12aVL;G1A2A3A2A2F_;F_;").
Proof using Clen Ecur Harm Hgr Hi I' LMI PV.
  intros Hc NM. destruct xold as (xo & Exo & NU). pose proof Llen as [LA LU]. pose proof SCR as SC.
  pose proof (mig_bounded LMI) as (_ & _ & _ & APTR). cbn [ma_s] in APTR.
  destruct (gg_image_In cur m sc (icnt ia) aidx len xo ND Exo SC LA LU c Hc) as [Hold|Hnew].
  - split; [exact Hold|]. exact (g_cell_stable (m :: X) None U cur L za len LI LXr APTR Hzpos c Hold).
  - exfalso. apply NM. exists 0%nat. pose proof (cell_w_posI post c Hc) as WP. split; [exact WP|]. rewrite Z.add_0_r.
    pose proof Lctx as HCX. cbn [mc_ctx C_U] in HCX. pose proof (m_R ia Hi) as MR.
    unfold gg_new in Hnew. destruct Hnew as [E|[E|[E|[(d & E & Hd & Hdw)|Hg]]]].
    + left. exists (D_ctr e_ctr). split; [right; right; right; left; reflexivity|]. rewrite E. cbn [loc_addr]. rewrite L'_ctx, HCX.
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd]. unfold CTX_mmap_counter. lia.
    + left. exists (D_usg e_usg). split; [right; right; left; reflexivity|]. rewrite E. cbn [loc_addr]. rewrite L'_ctx, HCX.
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd ia_sc ia' set_R]. unfold CTX_usage. fold sc. lia.
    + left. exists (D_act0 (SVar 190%positive)). split; [right; left; reflexivity|]. rewrite E. cbn [loc_addr]. rewrite L'_ctx, HCX.
      unfold dlo2, dhi2, od2_range, od2_rangeP. cbn [fst snd ia_sc ia' set_R]. unfold CTX_active. fold sc. lia.
    + left. exists (D_mT x). split; [left; reflexivity|]. rewrite E. change (loc_addr L' (LMem (padd m d))) with (loc_addr L' (LMem (padd m d))). rewrite loc_addr_padd, L'_m.
      unfold dlo2, dhi2, od2_range, od2_rangeP, D_mT. cbn [fst snd ia_m ia' set_R]. change (zA ia' (ia_m ia)) with (zA ia (ia_m ia)). change (zA ia m) with (zA ia (ia_m ia)). unfold META_SIZE in Hdw. lia.
    + right. assert (Hg' : In c (group_cells m amL) \/ In c (group_footer_cells amL)) by (destruct Hg as [Hg0|Hg0]; [left; exact Hg0 | right; rewrite Hg0; exact trailing_In]).
      pose proof (new_cell_range c Hg') as [R1 R2]. pose proof (cell_w_posI post c Hc). lia.
Qed.

Theorem VIN c : ltac2:(tb__ "0|0|
Sb1S114Vc;S4bS114S11dSecA1S18fSecA1A3A3Sc4Vc;A1S11fSedVbv1;Vc;A3F_;F_;").
Proof using CHK2 Ccond CdsC Clen Cmatch Comap Csem Cvars ELf1 EO Ecur Estk Hag Harm Hgr Hi2 HsmL Hx I' LMI PV.
  intros Hc (k & Hk & T). pose proof Lctx as HCX. cbn [mc_ctx C_U] in HCX. pose proof SCR as SC. pose proof (m_R ia Hi) as MR. top_ranges.
  pose proof aR as AR. pose proof cR as CR. pose proof AF as (A1 & A2 & A3 & AC & A5 & A6 & _).
  destruct T as [(d & Hd & R)|F].
  -
    unfold dlo2, dhi2, od2_range, od2_rangeP in R.
    destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd mc_tp C_U ia_sc ia_m ia' set_R D_mT] in R.
    +
      assert (EzA : zA ia' (ia_m ia) = zA ia m) by reflexivity. rewrite EzA in R.
      assert (CM : cmeets L' c (addr_of L' m) META_SIZE) by (exists k; split; [exact Hk|]; rewrite L'_m; unfold META_SIZE; lia).
      pose proof (meta_zone X (Some (m, 0)) U post L' post_I post_X post_L m c ltac:(rewrite post_keys; exact Lkey) Hc CM) as IN.
      rewrite post_MT, (proj2 (sptr_eqb_eq m m) eq_refl) in IN.
      cbn [meta_slot_cells amL gg_amL ig_am am_set_links am_prev am_next am_mem am_avail am_freed MallocInv.optr] in IN.
      assert (AGm : forall dd, loc_addr L' (LMem (padd m dd)) = dlo2 ia' (D_mT x) + dd).
      { intros dd. rewrite loc_addr_padd, L'_m. unfold dlo2, od2_range, od2_rangeP, D_mT. cbn [fst ia_m ia' set_R]. rewrite EzA. lia. }
      unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
      destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      * eapply (cell_from_odD (D_mT x) 0 8 (SVar 190%positive) _ (addr_of L' m)); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        rewrite L'_m, z190. reflexivity.
      * eapply (cell_from_odD (D_mT x) 8 8 (SVar 190%positive) _ (addr_of L' m)); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        rewrite L'_m, z190. reflexivity.
      * eapply (cell_from_odD (D_mT x) 16 8 (SVar 187%positive) _ (addr_of L' (memN cur))); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        rewrite L'_memN, z187. reflexivity.
      * eapply (cell_from_odD (D_mT x) 24 4 e_av _ (ones (iaidx ia) - 1)); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        change (8 * Z.of_nat 4) with 32. rewrite zev_av. reflexivity.
      * eapply (cell_from_odD (D_mT x) 28 4 e_fr _ (ones (icnt ia - 1) - ones (iaidx ia))); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        change (8 * Z.of_nat 4) with 32. rewrite zev_fr. reflexivity.
      * eapply (cell_from_odD (D_mT x) 32 8 (e_bits x) _ (meta_bits amL)); [left; reflexivity | cbn; tauto | apply AGm | reflexivity | reflexivity |].
        rewrite (zev_bits x Hx). unfold meta_bits. change (am_last amL) with (icnt ia - 1). change (am_sc amL) with sc. change (am_maplen amL) with (len / 4096).
        f_equal. Z.to_euclidean_division_equations; lia.
    +
      assert (CM : cmeets L' c (ly_ctx L' + (CTX_active + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite L'_ctx, HCX; unfold CTX_active; unfold sc in *; lia).
      pose proof (ctx_active_cell X (Some (m, 0)) U post L' post_I post_X post_L c sc SC Hc CM) as ->.
      rewrite (proj2 (proj2 (proj2 post_group))). cbn [MallocInv.optr].
      eapply (cell_from_odD (D_act0 (SVar 190%positive)) 0 8 (SVar 190%positive) _ (addr_of L' m)); [right; left; reflexivity | left; reflexivity | | reflexivity | reflexivity |].
      * cbn [mc_loc loc_addr]. rewrite L'_ctx, HCX. unfold dlo2, od2_range, od2_rangeP. cbn [fst ia_sc ia' set_R]. unfold CTX_active. fold sc. lia.
      * rewrite L'_m, z190. reflexivity.
    +
      assert (CM : cmeets L' c (ly_ctx L' + (CTX_usage + 8 * sc)) 8) by (exists k; split; [exact Hk|]; rewrite L'_ctx, HCX; unfold CTX_usage; unfold sc in *; lia).
      pose proof (ctx_usage_cell X (Some (m, 0)) U post L' post_I post_X post_L c sc SC Hc CM) as ->.
      eapply (cell_from_odD (D_usg e_usg) 0 8 e_usg _ (usage_of post sc)); [right; right; left; reflexivity | left; reflexivity | | reflexivity | unfold usage_of, znth; reflexivity |].
      * cbn [mc_loc loc_addr]. rewrite L'_ctx, HCX. unfold dlo2, od2_range, od2_rangeP. cbn [fst ia_sc ia' set_R]. unfold CTX_usage. fold sc. lia.
      * unfold post. rewrite (gg_usage_sc cur m sc (icnt ia) aidx len SC (proj1 Llen) (proj2 Llen)), zev_usg.
        pose proof CF as (_ & _ & _ & F4 & _). unfold usg, usage_of. rewrite F4. reflexivity.
    +
      assert (CM : cmeets L' c (ly_ctx L' + CTX_mmap_counter) 4) by (exists k; split; [exact Hk|]; rewrite L'_ctx, HCX; unfold CTX_mmap_counter; lia).
      pose proof (ctx_ctr_cell X (Some (m, 0)) U post L' post_I post_X post_L c Hc CM) as ->.
      eapply (cell_from_odD (D_ctr e_ctr) 0 4 e_ctr _ (st_mmap_counter post)); [right; right; right; left; reflexivity | left; reflexivity | | reflexivity | reflexivity |].
      * cbn [mc_loc loc_addr ctr_cell]. rewrite L'_ctx, HCX. unfold dlo2, od2_range, od2_rangeP. cbn [fst]. unfold CTX_mmap_counter. lia.
      * change (8 * Z.of_nat 4) with 32. rewrite zev_ctr. change (st_mmap_counter post) with (Z.land (st_mmap_counter cur + 1) (2 ^ 32 - 1)).
        pose proof CF as (_ & _ & _ & _ & F5 & _). rewrite F5. unfold ctr. change (2 ^ 32 - 1) with (Z.ones 32). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
  -
    assert (NEWc : In c (group_cells m amL) \/ In c (group_footer_cells amL)).
    { destruct (cell_cases X (Some (m, 0)) U post post_I post_X c Hc) as [Hcx | [(ar & next & Har & Hca) | (g & am & Hu & Hcg)]].
      - exfalso. pose proof (ctx_cell_in post L' c Hcx) as RI. unfold range_incl, cell_range, crange, e_ctx in RI. cbn [fst snd loc_addr] in RI.
        change (ly_ctx L') with (ly_ctx L) in RI. rewrite HCX in RI. apply (IMG ia za cur mWc HLV Hgr (loc_addr L' (mc_loc c) + Z.of_nat k)); [cbn [mc_img_lo mc_img_hi C_U]; unfold CTX_SIZE in RI; lia | exact F].
      - exfalso. pose proof (area_cell_in post L' ar next c Hca) as RI. unfold range_incl, cell_range, crange, e_area in RI. cbn [fst snd] in RI.
        rewrite post_areas in Har. pose proof (gL'_fp (m :: X) None U cur L za LI (e_area ar) (e_area_In cur ar Har)) as EA. unfold e_area in EA. cbn [fst] in EA. change (gL' cur L za) with L' in EA.
        apply (g_vs_footprint C_U cur L vm za len Lctx statics_in_image_U LV LIR Hzal Hzpos Hlen Hfree (e_area ar) (loc_addr L' (mc_loc c) + Z.of_nat k) (e_area_In cur ar Har)); [|exact F].
        unfold e_area. cbn [fst snd]. rewrite <- EA. lia.
      - destruct (sptr_eq_dec g m) as [->|NE]; [rewrite (post_am am Hu) in Hcg; exact Hcg|].
        exfalso. assert (Hu0 : usedX (m :: X) cur g am).
        { unfold usedX, MTX in Hu |- *. change (memb g (m :: X)) with (sptr_eqb g m || memb g X)%bool.
          replace (sptr_eqb g m) with false by (symmetry; apply sptr_eqb_neq; exact NE). cbn [orb].
          destruct (memb g X); [discriminate|]. rewrite post_MT in Hu. replace (sptr_eqb g m) with false in Hu by (symmetry; apply sptr_eqb_neq; exact NE). exact Hu. }
        destruct (group_cell_in (m :: X) None U cur L LI g am c Hu0 Hcg) as (rg & Hr & Hkd & Hl & ER & RI & d & Eloc & _).
        assert (EA : loc_addr L' (mc_loc c) = loc_addr L (mc_loc c)).
        { rewrite Eloc. rewrite !loc_addr_padd. pose proof (gL'_addr_of cur L za (am_mem am) (used_mem_below (m :: X) None U cur LI g am Hu0)) as EG.
          change (gL' cur L za) with L' in EG. rewrite EG. reflexivity. }
        unfold range_incl, cell_range, crange in RI. cbn [fst snd] in RI.
        apply (g_vs_footprint C_U cur L vm za len Lctx statics_in_image_U LV LIR Hzal Hzpos Hlen Hfree _ (loc_addr L' (mc_loc c) + Z.of_nat k) ER); [|exact F].
        unfold e_reg in RI |- *. cbn [fst snd] in RI |- *. rewrite EA. lia. }
    pose proof (new_cell_range c NEWc) as [R1 R2].
    destruct (new_cells c NEWc) as [-> | [-> | (Ev & p & Ep & Hpr & Hpo)]].
    +
      unfold cell_holds. cbn [mc_loc mc_val mc_w sval_num]. change (loc_addr L' (LMem (memN cur))) with (addr_of L' (memN cur)). change (loc_addr L' (LMem m)) with (addr_of L' m).
      rewrite L'_memN, L'_m. intros j Hj. exact (bv1_fresh_ptr j Hj).
    +
      unfold cell_holds. cbn [mc_loc mc_val mc_w sval_num]. rewrite loc_addr_padd, L'_memN. intros j Hj.
      destruct j as [|j]; [rewrite Z.add_0_r; rewrite bv1_fresh_ab; f_equal; unfold le_byte; change (8 * Z.of_nat 0) with 0; rewrite Z.shiftr_0_r; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); rewrite !Z.mod_small; lia|].
      rewrite (bv1_fresh_zero (za + 8 + Z.of_nat (S j))); [|cbn [mc_loc mc_w] in R2; rewrite loc_addr_padd, L'_memN in R2; lia]. f_equal. unfold le_byte.
      change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (iaidx ia)) by lia. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_small; [reflexivity|]. split; [lia|]. apply (Z.lt_le_trans _ (2 ^ 8)); [lia|]. apply Z.pow_le_mono_r; lia.
    +
      unfold cell_holds. rewrite Ev. cbn [sval_num]. intros j Hj. rewrite Ep in R1, R2 |- *.
      assert (EA : loc_addr L' (LMem p) = za + poff p).
      { destruct p as [r o]. cbn [prid poff] in Hpr, Hpo |- *. subst r. unfold loc_addr, L', Lext. cbn [ly_reg]. rewrite Nat.eqb_refl. lia. }
      rewrite EA in R2 |- *. rewrite (bv1_fresh_zero (za + poff p + Z.of_nat j)) by lia. rewrite le_byte_0. reflexivity.
Qed.

Theorem MI' : ltac2:(tb__ "0|0|
S1b2Sd1VI';S186SecSedA2S112SccSbbA2S113SccSbbA2VvmN;A6").
Proof using CHK2 Ccond CdsC Clen Cmatch Comap Csem Cvars ELf1 EO Ecur Estk HE Hag Harm Hgr Hi2 HsmL Hx LMI PV.
  pose proof post_LG as (LG1 & LG2 & LG3).
  refine (minv_postGX C_U (Inv (m :: X) None U) I' cur post L L' (Glue.rd_of segsU mA) (Glue.rd_of segsU mF) (Glue.wok_of segsU mA) (Glue.wok_of segsU mF) vm vmN
            HMI0 post_I post_B post_L L'_ctx post_ub post_V LG1 LG3 touched touched_dec NEW Hfp FPO UBO NEWT V1 VIN VM OLD _ _ _ statics_in_image_U NOSTAT HSD _ post_MW).
  - intros c Hc. exact (cell_spanI X (Some (m, 0)) U post L' post_I post_X post_L c Hc).
  - intros y Hy. exact (owned_spanI post L' post_L y Hy).
  - intros c Hc. exact (cell_w_posI post c Hc).
  - intros Hf. exfalso. change (st_init_done post) with (st_init_done cur) in Hf. rewrite (init_cur ia cur mWc HLV) in Hf. discriminate.
Qed.

Definition rhoR : valuation := set_rm rhoA mF.
Definition rhoS : valuation := rho_sub rhoR sT.
Definition rhoX : valuation := ltac2:(tb__ "0|4|
S194S194S194S194ScbP1M0S1fVrho0;G0A2A3P2M1S1fVrho0;G1A2A3P3M2S1fVrho0;G2A2A3P4M3S1fVrho0;G3A2A3").

Lemma smatch_R : ltac2:(tb__ "0|0|
S20SccScaS145VLf;A1S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4").
Proof using CHK2 Cmatch Cswf ELf1 EO Estk HsmL.
  pose proof (U.Mal_agrp__G4.Mal_agrp_R.smatch_released tr md msF rhoA Lf1 stkc objsD dsF HSF_objs Cmatch HsmA) as SM.
  assert (E : SFr Lf1 stkc = stk_only Lf) by (unfold SFr, stk_only, Lf1; cbn; rewrite EO, Estk; reflexivity).
  rewrite E in SM. exact (SM Cswf).
Qed.
Lemma smatch_X : ltac2:(tb__ "0|0|
S20SccSbfS166S165A1S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4").
Proof using CHK2 Cmatch Cswf ELf1 ENT EO Estk HsmL.
  unfold rhoX. do 4 (apply SymCall.smatch_set_rl; [apply Lok_norl|]). unfold rhoS. exact (entails_sound segsU (stk_only Lf) (L_as_ok IEC_U) sT rhoR _ ENT smatch_R).
Qed.
Lemma rmX : rm rhoX = mF. Proof using . reflexivity. Qed.
Lemma rwX i : ltac2:(tb__ "0|0|
S1f0Vi;ScdA2S0SceQ40A1S15SbfVi;A2S15Vrho0;Vi;A2A3F_;").
Proof using Clen Hag Hi2 I' PV SID cur.
  intros Hi0. pose proof (pv_frame ia X U A rho0 PV) as (F1 & _). cbn [rhoX rho_set_rl rw rhoS rho_sub]. rewrite (wsub_get_id sT NF i SID Hi0). cbn [eval rhoR set_rm rw rhoA].
  rewrite (proj1 Hag i ltac:(unfold below200; apply Pos.ltb_lt; unfold NF in Hi0; lia)). cbn [rho2 rw]. unfold NF in Hi0.
  destruct (Pos.eq_dec i 12) as [->|N12]; [change (rw2 ia' 12) with (Z_to_bv 64 (ia_sc ia)); change (ia_sc ia) with sc; rewrite pSC, Z_to_bv_bv_unsigned; reflexivity|].
  destruct (Pos.eq_dec i 13) as [->|N13]; [change (rw2 ia' 13) with (Z_to_bv 64 (ia_req ia)); change (ia_req ia) with req; rewrite pREQ, Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (rw2_low ia' Hi2 i ltac:(lia) N12 N13). cbn [ia' set_R ia_rho]. exact (F1 i ltac:(lia)).
Qed.
Lemma rlX l : ltac2:(tb__ "0|0|
S0S44SceQ8A1A1S1fSbfVl;A2S1fVrho0;Vl;A2A3").
Proof using Hag PV.
  pose proof (pv_frame ia X U A rho0 PV) as (_ & _ & F3 & _). cbn [rhoX rho_set_rl rl rhoS rho_sub rhoR set_rm rhoA].
  destruct (Pos.eqb_spec l 4) as [->|N4]; [reflexivity|]. destruct (Pos.eqb_spec l 3) as [->|N3]; [reflexivity|].
  destruct (Pos.eqb_spec l 2) as [->|N2]; [reflexivity|]. destruct (Pos.eqb_spec l 1) as [->|N1]; [reflexivity|].
  rewrite (proj1 (proj2 Hag) l). cbn [rho2 rl]. unfold rl2.
  replace (Pos.eqb l 1) with false by (symmetry; apply Pos.eqb_neq; exact N1). replace (Pos.eqb l 2) with false by (symmetry; apply Pos.eqb_neq; exact N2).
  replace (Pos.eqb l 3) with false by (symmetry; apply Pos.eqb_neq; exact N3). replace (Pos.eqb l 4) with false by (symmetry; apply Pos.eqb_neq; exact N4).
  cbn [ia' set_R ia_rho]. exact (F3 l N1).
Qed.
Lemma resX : ltac2:(tb__ "0|0|
S0S54Sd0Q40S15SbfS1a0A2A2Z0A3").
Proof using SRES. cbn [rhoX rho_set_rl rw rhoS rho_sub]. rewrite SRES. reflexivity. Qed.

Lemma blocks_post : ltac2:(tb__ "0|0|
S0S44S45S54S54A2A1SdaSedSecA2SdaVL;Vs1;A2A3").
Proof using CHK2 Clen Comap ELf1 EO Hag Hgr Hi HsmL LMI PV.
  pose proof (lv_blocks ia' cur L mA vm HLVA) as EB. cbn [ia' set_R ia_L ia_s] in EB. change (blocks L s1) with (blocks (ia_L ia) (ia_s ia)). rewrite <- EB.
  unfold blocks. rewrite post_ub. apply map_ext_in. intros [b n] Hb. cbn [fst snd]. f_equal. exact (UBO (b, n) Hb).
Qed.
Lemma kept_step a : ltac2:(tb__ "0|1|
S1S5dZ0Va;A2S5fVa;S60Z2Z40A2A2A2S1a2SccSd1S186Vcur;VL;A2Va;A4S3S1a3Sd1Va;A2A1S3S1a1Sd1Va;A2A1S0S46SceQ8A1A1SbbScfQ40Va;A2M0A1Sb6G0A1A3F_;F_;F_;F_;").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO HLV Hag Hgr Hi2 HsmL Hx I' PV.
  intros Ha Hc He Hst. pose proof (m_R ia Hi) as MR. top_ranges. pose proof SCR as SC. pose proof AF as (A1 & A2 & A3 & AC & A5 & _).
  destruct (in_ranges_decD od2 (dlo2 ia') (dhi2 ia') dsF a) as [(d & Hd & R)|N].
  2:{ unfold mF. apply (m'_outD a Ha). intros d Hd R. apply N. exists d. auto. }
  destruct (drom2 d) as [l|] eqn:Ed.
  - unfold mF. rewrite (m'_inD d a Hd R Ha). destruct (romD ia' Hi2 cur L mA vm HLVA d l a (HdsF_T d Hd) Ed R) as [Hro Hnone]. rewrite Hnone.
    apply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmA)))))). exact Hro.
  - exfalso. pose proof (client_not_ctx_U (m :: X) None U cur L _ _ vm HMI0 LXr a Hc) as NC.
    pose proof (fun q Hq => client_not_meta_U (m :: X) None U cur L _ _ vm HMI0 LXr a q Hc Hq) as NM.
    unfold dlo2, dhi2, od2_range, od2_rangeP in R. unfold alloc_static in Hst. unfold errno_range, mc_errno in He.
    cbn [mc_ctx mc_libc mc_chk_guard_got mc_chk_guard mc_replaced mc_tp C_U] in *. unfold CTX_SIZE, META_SIZE in *.
    destruct d; cbn [fst snd ia_sc ia_m ia' set_R] in R; try discriminate Ed; unfold sc in *; try lia.
    apply (NM m Lkey). rewrite Lma. change (zA ia' (ia_m ia)) with (zA ia (ia_m ia)) in R. change (zA ia m) with (zA ia (ia_m ia)). lia.
Qed.
Lemma keptX : ltac2:(tb__ "0|0|
S1a4SccSd1VA;S186SecSedA2S26Vrho0;A1SbbA6").
Proof using CHK2 Ccond Clen Comap Csem Cvars ELf1 EO Hag Hgr Hi2 HsmL Hx I' LMI PV.
  intros a Ha HcA HcA' He Hst.

  assert (Hc1 : client_addr segsU C_U (mkMA cur L) a) by (apply (client_addr_blocks post L' cur L a); [reflexivity | rewrite blocks_post; exact (lv_blocks ia' cur L mA vm HLVA) | exact HcA']).
  assert (Hs1 : client_addr segsU C_U (mkMA s1 L) a) by (apply (client_addr_blocks post L' s1 L a); [reflexivity | symmetry; exact blocks_post | exact HcA']).
  rewrite (kept_step a Ha Hc1 He Hst).
  rewrite (lv_kept ia' cur L mA vm HLVA a Ha Hs1 Hc1 He Hst). cbn [ia' set_R ia_mW].
  exact (pv_kept ia X U A rho0 PV a Ha HcA Hs1 He Hst).
Qed.

Lemma HOF_T d : ltac2:(tb__ "0|0|
Sb1S6dVd;Sb4A3S22SccSbcVmsF;S6eVd;A1A4F_;").
Proof using CHK2 Cmatch ELf1 EO Estk HsmL. exact (HOF_d segsU od2 obj_of2 tr md msF rhoA Lf1 (oStkF stkc) objsD dsF HSF_objs Cmatch HsmA d). Qed.
Lemma canaryX : ltac2:(tb__ "0|0|
S1a6SccSd1Sd0Q40S15Vrho0;PaeA2A2SbbA4").
Proof using CHK2 Ccond Cgot Cguard Clen Cmatch Csem Cvars ELf1 EO Estk Hag Hi2 HsmL Hx I' PV cur.
  pose proof (iok_gd ia Hi) as GR.
  assert (E173 : eval rhoA (v 173) = Z_to_bv 64 (mc_chk_guard C_U)) by (cbn [eval v rhoA rw]; rewrite (proj1 Hag 173%positive eq_refl); reflexivity).
  assert (E174 : eval rhoA (v 174) = Z_to_bv 64 (ia_gd ia)) by (cbn [eval v rhoA rw]; rewrite (proj1 Hag 174%positive eq_refl); reflexivity).
  assert (RGg : forall y, 0x28d50 <= y < 0x28d50 + 8 -> dlo2 ia' D_got <= y < dhi2 ia' D_got) by (intros y Hy; unfold dlo2, dhi2, od2_range, od2_rangeP; cbn [fst snd]; lia).
  assert (RGu : forall y, mc_chk_guard C_U <= y < mc_chk_guard C_U + 8 -> dlo2 ia' D_guard <= y < dhi2 ia' D_guard) by (intros y Hy; unfold dlo2, dhi2, od2_range, od2_rangeP; cbn [fst snd mc_chk_guard C_U] in *; lia).
  split; intros k Hk; cbn [mc_chk_guard_got C_U].
  - assert (Ha : 0 <= 0x28d50 + Z.of_nat k < 2 ^ 64) by lia.
    assert (Hy : 0x28d50 <= 0x28d50 + Z.of_nat k < 0x28d50 + 8) by lia.
    rewrite rd_of_CG, (rd_of_at segsU mF msF _ HromF (m'_inD D_got (0x28d50 + Z.of_nat k) Cgot (RGg _ Hy) Ha)).
    pose proof (cell_bytes_sym segsU rhoA msF (obj_of2 D_got) (mkCell (SLit 0) 8 (v 173)) k (HOF_T D_got Cgot) ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_got c_off c_val c_width eval] in B. rewrite soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E173. rewrite nth_enc_bytes by (cbn; lia). reflexivity.
  - assert (Ha : 0 <= mc_chk_guard C_U + Z.of_nat k < 2 ^ 64) by (cbn; lia).
    assert (Hy : mc_chk_guard C_U <= mc_chk_guard C_U + Z.of_nat k < mc_chk_guard C_U + 8) by lia.
    rewrite rd_of_CG, (rd_of_at segsU mF msF _ HromF (m'_inD D_guard (mc_chk_guard C_U + Z.of_nat k) Cguard (RGu _ Hy) Ha)).
    pose proof (cell_bytes_sym segsU rhoA msF (obj_of2 D_guard) (mkCell (SLit 0) 8 (v 174)) k (HOF_T D_guard Cguard) ltac:(left; reflexivity) ltac:(cbn; lia)) as B.
    cbn [ob_base obj_of2 O_guard c_off c_val c_width] in B. rewrite E173, soff_lit_small, !u64 in B by (cbn; lia).
    rewrite Z.add_0_r in B. rewrite B. change (Z.to_nat 8) with 8%nat. rewrite E174. rewrite nth_enc_bytes by lia. rewrite (pv_gd ia X U A rho0 PV). reflexivity.
Qed.

Theorem exit_post : ltac2:(tb__ "0|0|
S1a5SccSd1S165VNf;VOg;VX;VU;VA;VKc;Vrho0;S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4Ab").
Proof using CHK2 Ccond CdsC Cgot Cguard Clen Cmatch Comap Csem Cswf Cvars ELf1 ENT EO Ecur Estk HE HKc HOg Hag Harm Hgr Hi2 Hmd HsmL Hx I' LMI PV SID SRES bv1 bvA rv1 rvA.
  exists (L_as_ok IEC_U), (JLg_okG segsU C_U Og X U A Kc), rhoX.
  split; [right; left; reflexivity|].
  split; [split; [intros i Hi0; symmetry; exact (rwX i Hi0) | intros l; symmetry; exact (rlX l)]|].
  split; [exact smatch_X|].
  cbn [w_tr w_cfg cfg_model]. unfold JLg_okG. split; [exact HOg|]. unfold JLg_ok. cbn zeta. rewrite <- !pSC, <- !pREQ.
  split; [exact resX|].
  exists (mkMA post L'), m, amL. pose proof post_group as (G1 & G2 & G3 & G4). pose proof post_hb as [HB UB]. pose proof CF as (_ & _ & F3 & _).
  split. { unfold MInvIR, MInvI. change (m_vmmaps (cfg_model (w_cfg (tr, mkCfg msF md)))) with (m_vmmaps md). rewrite rmX. rewrite Hmd. rewrite rd_of_CG, wok_of_CG. exact MI'. }
  split; [exact post_X|].
  split; [cbn [ma_L]; apply (layout_extends_trans_le (ma_L A) L L' _ (nr_id cur) (pv_ext ia X U A rho0 PV) (Lext_extends L (nr_id cur) za));
          unfold nr_id; rewrite F3; exact (pv_nreg ia X U A rho0 PV)|].
  split; [exact G4|]. split; [exact (proj1 post_used)|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split; [exact HB|]. split; [exact UB|].
  split; [rewrite rmX; exact keptX|].
  split; [rewrite rmX; exact canaryX|].
  split; [exact yields_T | exact HKc].
Qed.
End LeafT.

Definition LWc (x : m1v) : sstate := ltac2:(tb__ "0|0|
S1daS1b6Vx;A1U0S1b9Vx;A1A3").
Lemma LW_single x : ltac2:(tb__ "0|0|
S0S44Se8A1S1b6Vx;A1S40Se8SebSf2Vx;A1SeaA2S48Se8A1A3A3"). Proof using . destruct x; reflexivity. Qed.
Definition sT_a : wsub := ltac:(let y := eval vm_compute in (infer_sub NF (stk_only (LWc M1a)) (L_as_ok IEC_U)) in exact y).
Definition sT_b : wsub := ltac:(let y := eval vm_compute in (infer_sub NF (stk_only (LWc M1b)) (L_as_ok IEC_U)) in exact y).
Definition sT_c : wsub := ltac:(let y := eval vm_compute in (infer_sub NF (stk_only (LWc M1c)) (L_as_ok IEC_U)) in exact y).
Definition sT_d : wsub := ltac:(let y := eval vm_compute in (infer_sub NF (stk_only (LWc M1d)) (L_as_ok IEC_U)) in exact y).
Definition sTx (x : m1v) : wsub := ltac2:(tb__ "0|0|
S1a9S19aLx;Vx;S101S102S103S104X1a9x4").
Lemma chk_x x : ltac2:(tb__ "0|0|
S0S42SfcVx;Sf2Vx;A1A2S43A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk2_x x : ltac2:(tb__ "0|0|
S0S42S16Sf1Vx;Sf2Vx;A1A2A1S43A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma ent_x x : ltac2:(tb__ "0|0|
S0S42S196S145Sf2Vx;A1A1S166S165A1Sf4Vx;A1A3S43A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sid_x x : ltac2:(tb__ "0|0|
S0S42S198Sf4Vx;A1ScdA2S43A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma sres_x x : ltac2:(tb__ "0|0|
S0SaS199Sf4Vx;A1S1a0A2SbZ0A1A3"). Proof using . destruct x; reflexivity. Qed.

Variable x : m1v.
Hypothesis Hx : ltac2:(tb__ "0|0|
S1S5dS144Vx;A1Vsc;A2S5dVsc;S143Vx;A1A2A2").
Let Q : assn := ltac2:(tb__ "0|0|
S1a5SccSd1S165VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Theorem leaf_TP : ltac2:(tb__ "0|0|
Se8S27Sb1Se8R2S1b6Vx;A1A3S16aS71Via';VmZ;A2R2A2VTR;VkB;S162SccVKN;Se9R4A1R3A4VQ;A3F_;F_;Frho';FLf;").
Proof using Ecur HE HOg Harm Hgr Hi2 HkB Hx LMI Nf PV RR len m req vmN.
  intros Lf rho' Hin Hag. rewrite LW_single in Hin. destruct Hin as [<-|[]]. cbn [lf_state].
  (apply (trr_skip RR); [lia|]). intros [tr [msF md]] [Hsm [HK Hmd]]. cbn [w_tr w_cfg cfg_model fst snd] in HK, Hmd.
  exact (exit_post x (LWc x) (sTx x) Hx (chk_x x) (chk2_x x) (ent_x x) (sid_x x) (sres_x x) rho' tr msF md Hag Hsm HK Hmd).
Qed.

Theorem gen_TP : ltac2:(tb__ "0|1|
S27S16aS71Via';VmZ;A2R1A2S0SceQ40A1S15R2S2bS13bVx;A1M0A1A2Sd7Vza;A1A3VTR;VkB;S162SccVKN;S1d2G0A1R3A4VQ;A3F_;F_;FrhoT;").
Proof using Ecur HE HOg Harm Hgr Hi2 HkB Hx LMI Nf PV RR len m req vmN. exact (gen_T Kc RF GF TR RR kB HkB ia Hi za cur mWc HLV Hgr x Hx Q leaf_TP). Qed.
End TP.
End Mal_agrp_TP.

Module Mal_agrp_FX.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FrameG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientPriv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G1.Mal_aslot_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_Adefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G3.Mal_agrp_rK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_K OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_T OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_rF OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_F.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition O_fhE (sh : bool) : sobj := ltac2:(tb__ "0|1|
S29SbS1aaA1SbZ18A1M0SbZ20A1S40S10S12G0Z8S42SaLsh;Vsh;SdPffA1S179PbeA1X42x2A3S48S10A1A3S18A5").
Definition O_fmpE : sobj := ltac2:(tb__ "0|2|
S29SdPffA1SbZ0A1M0SbZ8M1A1S40S10S12G0G1S179PbeA1A3S48S10A1A3S18A5").
Definition O_hpnE : sobj := ltac2:(tb__ "0|2|
S29SdP100A1SbZ8M0A1M1SbZ10A1S40S10S12G1G0S179PbeA1A3S48S10A1A3S18A5").
Definition RING (sh : bool) : list sobj := ltac2:(tb__ "0|1|
S42S44SeA1Lsh;Vsh;S40SeS18cS43A1S40SeS18aS40SeS18bS48SeA1M0A3A3A3S40SeS18cS4eA1G0A3X42x2").

Definition CANON (sh : bool) : list cell := ltac2:(tb__ "0|5|
S4bS10S42S44S10A1Lsh;Vsh;S40S10S12SbZ0A1M0Z8M1SdP100A1A3S40S10S12SbG1A1M2G1SdPffA1A3S48S10A1M3A3A3S40S10S12G2G1S179PbeA1M4A3S40S10S12G0G1G4A3G3A3A3X42x2S40S10S12SbZ10A1G1G0A3S40S10S12SbZ18A1G1G0A3S40S10S12SbZ20A1G1G0A3G3A3A3A3A3").
Lemma Lfail_norl l : ltac2:(tb__ "0|0|
S0S42S195Vl;S168S165A1A2S4eA3"). Proof. destruct l; reflexivity. Qed.

Section FX.
Variables (Kc : list event -> Model -> Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let sc : Z := ia_sc ia. Let m : sptr := ia_m ia. Let req : Z := ia_req ia. Let s1 : astate := ia_s ia.
Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S1abVia;VX;VU;VA;Vrho0;A5").

Variables (cur : astate) (Lc : layout) (mWc : word -> option byte) (vmc : VmMaps).
Hypothesis HLV : ltac2:(tb__ "0|0|
S7eVia;Vcur;VLc;VmWc;Vvmc;A5").
Let L : layout := Lc. Let vm : VmMaps := vmc.
Hypothesis EXT : ltac2:(tb__ "0|0|
S187S189VA;A1VLc;S49S90S95S185VA;A1A1A2A3").

Variables (lo hi : Z).
Hypothesis Hx : ltac2:(tb__ "0|0|
S1S5dVlo;Vsc;A2S5dVsc;Vhi;A2A2").

Variable sh : bool.
Variables (fm hp nx pr2 : sptr).
Hypothesis HSH : ltac2:(tb__ "0|4|
S42OLsh;Vsh;S1S0S46S8cA1M0S92Vcur;A1M1S47S8cVfm;A2M2A3S1S0S46S8dA1M3S115Vcur;Vfm;A2S47S8dS8eS47S8cVhp;A2S47S8cVnx;A2A2A2A3S0G3S115Vcur;Vhp;A2S47S8dS8eS47S8cVpr2;A2G2A2A2A3A2A2S0G0G1S4cS8cA1A3X42x2").

Hypothesis YF : ltac2:(tb__ "0|2|
S4aS17cS1b4Vsc;A1S50R1A1A2S5S44S45S9cS54A2A1M0G0S126S45S46S8cA1M1S8fA2S9aR3Vsc;Vreq;S185VA;A1A4R1S41G1S8fS4cS8cA1S19cS7aVia;A1Vcur;A2A4A4Lktr;A2F_;Ffuel;").

Variable P : list od2.
Hypothesis Pchk : ltac2:(tb__ "0|0|
S0S42Sb2S6dS6dS4dS4dS164S169S6eR1A1A2S14bR1A1A2S14aVlo;Vhi;R1A3A2Ld;VP;A3S43A3").
Variable he : bool.
Hypothesis Perrno : ltac2:(tb__ "0|0|
SaSb1S6dS76R1A1VP;A3S1S0S42Vhe;S43A3S0SaR2SbZcA1A3A2F_;Fe;").
Hypothesis Herrno : ltac2:(tb__ "0|0|
S0S42Vhe;S43A3Sb1S6dS76SbZcA1A1VP;A3F_;").
Hypothesis Pgot : In D_got P.
Hypothesis Pguard : In D_guard P.

Hypothesis PCASES : ltac2:(tb__ "0|7|
S6dSb1S6dR1VP;A3S41S54S54S148Via;R2A2S149Via;R2A2A4S45S54S54A2M0S4S1S0S6dR3S76SbZcA1A1A3M1S0G0R1S41S54S54Sd4Sd1A1M2S5eG2Z4A2A4M3A3A2S1S3G1A1S1S4S5S55S55S0S46S55A1M4S14fR4A1S47S55R1A2A3Ll;A2S0G4S14fR3A1S4cS55A1A3A2S1S25R1S41S54S54S5eZ5a3c8M5Z18A2S5eG5Z20A2A4A2S1S25R1G3A2S8cSb1S8cR1S118Vcur;A1A3S25R3S41S54S54Sd3VL;R2A2M6S5eG6Z28A2A4A2F_;Fq;A2A2A2A2A2Tr;F_;Fd;").

Hypothesis ENTRY : ltac2:(tb__ "0|0|
S6dSb1S6dR1VP;A3S3S0S6dR2S76SbZcA1A1A3A1S7fVia;Vcur;VmWc;R3A4F_;F_;Fd;").

Hypothesis PCLIENT : ltac2:(tb__ "0|1|
S6dS54Sb1S6dR2VP;A3S3S0S6dR3S76SbZcA1A1A3A1S0S46S55A1S14fR4A1S4cS55A1A3S1S5dS148Via;R5A2R4A2S5fR4S149Via;R5A2A2A2S4S1S5dSd8Sd1A1M0R5A2S5fR5S5eG0S121A2A2A2S1a1Sd1R5A2A2F_;F_;F_;F_;Fa;Fd;").

Variable Om : sobj.
Hypothesis OmG : ltac2:(tb__ "0|0|
S1S0SaS1bVOm;A1S179PbeA1A3S1S0SaS37VOm;A1SbZ0A1A3S1S0SaS36VOm;A1SbZ28A1A3S0S1dS1cVOm;A1S18A3A2A2A2").
Hypothesis OmC : ltac2:(tb__ "0|0|
S10S7Sb1S10R1S1eVOm;A1A3Sb1S10R1S18eVsh;A1A3A2Fcc;").

Definition HAND : list sobj := ltac2:(tb__ "0|0|
S40SeVOm;S4bSeS15dS6dSeS6eVP;A4S18dVsh;A1A3A3").
Variables (Lf : sstate) (stk : sobj).
Hypothesis EO : ltac2:(tb__ "0|0|
S0S44SeA1S17VLf;A1S40SeVstk;S107A3A3").
Hypothesis STK : ltac2:(tb__ "0|0|
S1S0SaS1bVstk;A1SdPaA1A3S1S0SaS37Vstk;A1SdPfA1A3S1S0SaS36Vstk;A1SbZ0A1A3S0S1dS1cVstk;A1S18A3A2A2A2").
Definition Lfr : sstate := ltac2:(tb__ "0|0|
S2dS32VLf;A1S33VLf;A1S30VLf;A1S2fVLf;A1S34VLf;A1S40SeVstk;S48SeA1A3S2eVLf;A1S2bVLf;A1S31VLf;A1A9").
Hypothesis LFswf : swf Lfr = true.
Hypothesis entF : ltac2:(tb__ "0|1|
S0S42S196S10cS168S165A1M0S1adScdS10cG0A3A3S43A3").
Hypothesis sidF : ltac2:(tb__ "0|0|
S0S42S198S1adScdS10cS168S165A1A3ScdA2S43A3").

Variables (rho6 : valuation) (tr : list event) (msF : machine_state) (md : Model).
Hypothesis Hag : ltac2:(tb__ "0|0|
S16aS71Via;VmWc;A2Vrho6;A2").
Hypothesis H25 : ltac2:(tb__ "0|2|
S42OLsh;Vsh;S1S0SceQ40M0A1M1S15Vrho6;PffA2ScfG0Sd3VL;Vfm;A2A2A3S0G1S15Vrho6;P100A2ScfG0Sd3VL;Vhp;A2A2A3A2S9X42x2").
Hypothesis HsmL : ltac2:(tb__ "0|0|
S20SccVrho6;VLf;S41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4").
Hypothesis HKc : Kc tr md.
Hypothesis Hmd : ltac2:(tb__ "0|0|
S0S180S182Vmd;A1Vvm;A3").

Lemma pX : ltac2:(tb__ "0|0|
S0S44S8cA1S79Via;A1VX;A3"). Proof using PV. exact (pv_X ia X U A rho0 PV). Qed.
Lemma pU : ltac2:(tb__ "0|0|
S0S54S54F_;S78Via;A1VU;A3"). Proof using PV. exact (pv_U ia X U A rho0 PV). Qed.
Lemma pR : ia_R ia = None. Proof using PV. exact (pv_R ia X U A rho0 PV). Qed.
Lemma pSC : ltac2:(tb__ "0|0|
S0S54Vsc;Sd0Q40S15Vrho0;PcA2A2A3"). Proof using PV. exact (pv_sc ia X U A rho0 PV). Qed.
Lemma pREQ : ltac2:(tb__ "0|0|
S0S54Vreq;Sd0Q40S15Vrho0;PdA2A2A3"). Proof using PV. exact (pv_req ia X U A rho0 PV). Qed.
Lemma SCR : 0 <= sc < 48. Proof using Hi. exact (iok_sc ia Hi). Qed.
Lemma REQR : ltac2:(tb__ "0|0|
S1S5dZ0Vreq;A2S5dS5eVreq;S99A2S96Vsc;A1A2A2"). Proof using Hi. exact (iok_req ia Hi). Qed.
Let LMI : ltac2:(tb__ "0|0|
S1b3Sd1S40S8cS7aVia;A1S79Via;A1A3S81Via;A1S78Via;A1S186Vcur;VL;A2S112SccVmWc;A2S113SccVmWc;A2Vvm;A8") := ltac2:(tb__ "0|0|
S84Via;Vcur;VL;VmWc;Vvm;VHLV;A6").
Lemma LI : ltac2:(tb__ "0|0|
S11bS40S8cVm;VX;A3S4cS45S8cS54A2A1VU;Vcur;A4"). Proof using LMI PV. rewrite <- pX, <- pU, <- pR. exact (mig_I LMI). Qed.
Lemma LXr : ltac2:(tb__ "0|0|
S1c1S40S8cVm;VX;A3Vcur;A2"). Proof using HLV L PV vm. rewrite <- pX. exact (lv_Xr ia cur L mWc vm HLV). Qed.
Lemma LL : layout_ok L cur. Proof using LMI. exact (mig_layout LMI). Qed.
Lemma LV : ltac2:(tb__ "0|0|
Sd9VL;Vcur;Vvm;A3"). Proof using LMI. exact (mig_vm LMI). Qed.
Lemma LLG : ledger_ok C_U vm. Proof using LMI. exact (mig_ledger LMI). Qed.
Lemma Lctx : ly_ctx L = 0x5a3d0. Proof using LMI. exact (mig_ctx LMI). Qed.
Lemma Lkey : In m (keys cur). Proof using HLV L vm. exact (lv_key ia cur L mWc vm HLV). Qed.
Lemma Lraw : ltac2:(tb__ "0|3|
S4S0S46S8dA1M0S115Vcur;Vm;A2M1S47S8dS9fA2A3S0G0G1S47S8dS8eS4cS8cA1M2G2A2A2A3A2"). Proof using HLV L vm. exact (lv_raw ia cur L mWc vm HLV). Qed.
Lemma Lma : ltac2:(tb__ "0|0|
S0S54Sd3VL;Vm;A2S77Via;Vm;A2A3"). Proof using HLV vm. exact (lv_m_addr ia cur L mWc vm HLV). Qed.
Lemma ND : List.NoDup (keys cur). Proof using LMI PV m. exact (proj1 (inv_keys LI)). Qed.
Lemma Linit : st_init_done cur = true.
Proof using LMI PV m.
  destruct (st_init_done cur) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 LI) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof Lkey as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.
Lemma HMI0 : ltac2:(tb__ "0|0|
S1b2Sd1S11bS40S8cVm;VX;A3S4cS45S8cS54A2A1VU;A3S186Vcur;VL;A2S112SccVmWc;A2S113SccVmWc;A2Vvm;A6").
Proof using LMI PV. pose proof LMI as M. unfold MInvI in M. rewrite pX, pU, pR in M. exact M. Qed.

Lemma HSHt : ltac2:(tb__ "0|2|
S0S42Vsh;S43A3S1S0S46S8cA1S92Vcur;A1S47S8cVfm;A2M0A3S1S0S46S8dA1M1S115Vcur;Vfm;A2S47S8dS8eS47S8cVhp;A2S47S8cVnx;A2A2A2A3S0G1S115Vcur;Vhp;A2S47S8dS8eS47S8cVpr2;A2G0A2A2A3A2A2F_;").
Proof using HSH. intros Hs. pose proof HSH as H. rewrite Hs in H. exact H. Qed.
Lemma HSHf : ltac2:(tb__ "0|0|
S0S42Vsh;S4eA3S0S46S8cA1S92Vcur;A1S4cS8cA1A3F_;").
Proof using HSH. intros Hs. pose proof HSH as H. rewrite Hs in H. exact H. Qed.
Lemma H25t : ltac2:(tb__ "0|2|
S0S42Vsh;S43A3S1S0SceQ40M0A1M1S15Vrho6;PffA2ScfG0Sd3VL;Vfm;A2A2A3S0G1S15Vrho6;P100A2ScfG0Sd3VL;Vhp;A2A2A3A2F_;").
Proof using H25. intros Hs. pose proof H25 as H. rewrite Hs in H. exact H. Qed.
Lemma fm_ne : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3S1S3S0S8cVfm;Vm;A3A1S3S0S8cVhp;Vm;A3A1A2F_;").
Proof using HLV HSH L vm.
  intros Hs. destruct (HSHt Hs) as (_ & Mfm & Mhp).
  split; intros EQ; [rewrite EQ in Mfm | rewrite EQ in Mhp]; destruct Lraw as [E|E]; first [rewrite E in Mfm; discriminate Mfm | rewrite E in Mhp; discriminate Mhp].
Qed.
Ltac shape_cases := destruct (Sumbool.sumbool_of_bool sh) as [Es|Es].

Definition s' : astate := fm_post m cur.
Lemma free_ring : free_ring_ok m cur.
Proof using HLV HSH L vm.
  intros f Hf. shape_cases.
  - destruct (HSHt Es) as (Hfh & Mfm & Mhp). destruct (fm_ne Es) as [N1 N2]. rewrite Hf in Hfh. injection Hfh as ->.
    split; [exact N1|]. exists (MFree (Some hp) (Some nx)), hp. split; [exact Mfm|]. split; [reflexivity|]. split; [exact N2 | rewrite Mhp; discriminate].
  - rewrite (HSHf Es) in Hf. discriminate Hf.
Qed.
Lemma yields_F : ltac2:(tb__ "0|2|
S4aS17cS1b4Vsc;A1S50R1A1A2S5S44S45S9cS54A2A1M0G0S126S45S46S8cA1M1S8fA2S9aR3Vsc;Vreq;S185VA;A1A4R1S41G1S8fS4cS8cA1S105A4A4Lktr;A2F_;Ffuel;").
Proof using YF. exact YF. Qed.
Lemma GP : ltac2:(tb__ "0|0|
S1beVX;VU;S185VA;A1Vsc;Vreq;S41S46S8cA1S8fS4cS8cA1S105A4A6").
Proof using Hi PV YF.
  destruct (yields_F (need sc) ltac:(lia)) as [ktr Hy]. pose proof SCR. pose proof REQR as [R1 R2].
  exact (alloc_group_post X U (ma_s A) sc req (need sc) ktr (None, s') (pv_I0 ia X U A rho0 PV) SCR R1 R2 ltac:(lia) (pv_hd0 ia X U A rho0 PV) Hy).
Qed.
Lemma post_I : ltac2:(tb__ "0|0|
S11bVX;S4cS45S8cS54A2A1VU;S105A4"). Proof using Hi PV YF. destruct GP as (_ & _ & HI). exact HI. Qed.
Lemma post_hb : ltac2:(tb__ "0|1|
S1S1bfS185VA;A1M0S105Vsc;A3S1bcG0S105A2A2"). Proof using Hi PV YF. destruct GP as (H1 & H2 & _). exact (conj H1 H2). Qed.

Definition t1 : astate := ltac2:(tb__ "0|1|
S1bdVm;S8eS4cS8cA1M0G0A2Vcur;A3").
Lemma s'_eq : ltac2:(tb__ "0|0|
S0S8fS105S1d5S10aVm;A2A3"). Proof using . reflexivity. Qed.
Lemma t1_keys : ltac2:(tb__ "0|0|
S0S44S8cA1S118S10aA1S118Vcur;A1A3"). Proof using HLV L vm. unfold t1. apply keys_upd_In. exact Lkey. Qed.
Lemma t1_ND : List.NoDup (keys t1). Proof using LMI PV. rewrite t1_keys. exact ND. Qed.
Lemma t1_Mm : ltac2:(tb__ "0|1|
S0S46S8dA1S115S10aVm;A2S47S8dS8eS4cS8cA1M0G0A2A2A3"). Proof using . unfold t1. apply MT_upd_same. Qed.
Lemma t1_MT q : ltac2:(tb__ "0|0|
S3S0S8cVq;Vm;A3A1S0S46S8dA1S115S10aVq;A2S115Vcur;Vq;A2A3F_;"). Proof using . intros Hq. unfold t1. apply MT_upd_other. exact Hq. Qed.
Lemma t1_head : ltac2:(tb__ "0|0|
S0S46S8cA1S92S10aA1S92Vcur;A1A3"). Proof using . reflexivity. Qed.
Lemma delta_t1 : ltac2:(tb__ "0|0|
S1a8Vcur;S10aS1a7Vm;A1A3").
Proof using LMI PV.
  destruct Lraw as [E|E]; unfold t1.
  - apply (delta_nu cur m MRaw (MFree None None) ND E I). intros am0 EE. discriminate EE.
  - apply (delta_nu cur m (MFree None None) (MFree None None) ND E I). intros am0 EE. discriminate EE.
Qed.

Lemma t1_ring : ltac2:(tb__ "0|2|
S0S42Vsh;S43A3S1S0S46S8cA1S92S10aA1S47S8cVfm;A2M0A3S1S0S46S8dA1M1S115S10aVfm;A2S47S8dS8eS47S8cVhp;A2S47S8cVnx;A2A2A2A3S1S0G1S115S10aVhp;A2S47S8dS8eS47S8cVpr2;A2G0A2A2A3S1S3S0S8cVfm;Vm;A3A1S3S0S8cVhp;Vm;A3A1A2A2A2A2F_;").
Proof using HLV HSH L vm.
  intros Hs. destruct (HSHt Hs) as (Hfh & Mfm & Mhp). destruct (fm_ne Hs) as [N1 N2].
  rewrite t1_head, (t1_MT fm N1), (t1_MT hp N2). auto.
Qed.
Definition locsF : list loc := ltac2:(tb__ "0|1|
S4bS116S1a7Vm;A1M0S42S44S116A1Lsh;Vsh;S4bS116S4bS116G0S1a7Vhp;A1A3S1a7Vfm;A1A3S4bS116G0S40S116S12dS12cA1S48S116A1A3A3X42x2A3").
Lemma delta_s' : ltac2:(tb__ "0|0|
S1a8Vcur;S105S10fA3").
Proof using HSH LMI PV.
  rewrite s'_eq. unfold locsF. apply (delta_trans cur t1); [exact delta_t1|]. shape_cases; rewrite Es.
  - destruct (t1_ring Es) as (Hfh & Mfm & Mhp & N1 & N2). exact (delta_fq_ring t1 m t1_ND t1_Mm fm hp nx pr2 fm Hfh Mfm Mhp N1 N2).
  - apply (delta_fq_empty t1 m t1_ND t1_Mm). rewrite t1_head. exact (HSHf Es).
Qed.

Lemma s'_Mm : ltac2:(tb__ "0|1|
S0S46S8dA1S115S105Vm;A2S47S8dS42S8dLsh;Vsh;S8eS47S8cVhp;A2S47S8cVfm;A2A2S8eS47S8cVm;A2M0G0A2X42x2A2A3").
Proof using HLV HSH L vm.
  rewrite s'_eq. shape_cases; rewrite Es.
  - destruct (t1_ring Es) as (Hfh & Mfm & Mhp & N1 & N2). exact (MT_fq_g t1 m fm hp nx pr2 fm Hfh Mfm Mhp N1 N2).
  - apply (MT_fq_empty_g t1 m). rewrite t1_head. exact (HSHf Es).
Qed.
Lemma s'_head : ltac2:(tb__ "0|0|
S0S46S8cA1S92S105A1S47S8cS42S8cLsh;Vsh;Vfm;Vm;X42x2A2A3").
Proof using HLV HSH L vm.
  rewrite s'_eq. shape_cases; rewrite Es.
  - destruct (t1_ring Es) as (Hfh & Mfm & Mhp & N1 & N2). exact (head_fq_ring t1 m fm hp nx pr2 fm Hfh Mfm Mhp N1 N2).
  - apply (head_fq_empty t1 m). rewrite t1_head. exact (HSHf Es).
Qed.
Lemma s'_Mfm : ltac2:(tb__ "0|1|
S0S42Vsh;S43A3S0S46S8dA1S115S105Vfm;A2S47S8dS8eS47S8cVm;A2M0S42S46S8cA1L_;Sa5Vfm;Vhp;A2G0S47S8cVnx;A2X42x2A2A2A3F_;").
Proof using HLV HSH L vm.
  intros Hs. rewrite s'_eq. destruct (t1_ring Hs) as (Hfh & Mfm & Mhp & N1 & N2).
  exact (MT_fq_fm t1 m fm hp nx pr2 fm Hfh Mfm Mhp N1 N2).
Qed.
Lemma s'_Mhp : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3S3S0S8cVhp;Vfm;A3A1S0S46S8dA1S115S105Vhp;A2S47S8dS8eS47S8cVpr2;A2S47S8cVm;A2A2A2A3F_;F_;").
Proof using HLV HSH L vm.
  intros Hs Hne. rewrite s'_eq. destruct (t1_ring Hs) as (Hfh & Mfm & Mhp & N1 & N2).
  exact (MT_fq_hp t1 m fm hp nx pr2 fm Hfh Mfm Mhp N1 N2 Hne).
Qed.
Lemma s'_Mother q : ltac2:(tb__ "0|0|
S3S0S8cVq;Vm;A3A1S0S42Vsh;S43A3S1S3S0S8cVq;Vfm;A3A1S3S0S8cVq;Vhp;A3A1A2F_;S0S46S8dA1S115S105Vq;A2S115Vcur;Vq;A2A3F_;F_;").
Proof using HLV HSH L vm.
  intros Hq Hsh. rewrite s'_eq. rewrite <- (t1_MT q Hq). shape_cases.
  - destruct (t1_ring Es) as (Hfh & Mfm & Mhp & N1 & N2). destruct (Hsh Es) as [Q1 Q2].
    exact (MT_fq_other t1 m fm hp nx pr2 fm Hfh Mfm Mhp N1 N2 q Hq Q1 Q2).
  - exact (MT_fq_empty_other t1 m q ltac:(rewrite t1_head; exact (HSHf Es)) Hq).
Qed.
Lemma s'_keys : ltac2:(tb__ "0|0|
S0S44S8cA1S118S105A1S118Vcur;A1A3"). Proof using HSH LMI PV. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 delta_s'))))))). Qed.

Lemma keyR q : ltac2:(tb__ "0|3|
Sb1S8cVq;S118Vcur;A1A3S1S5dZ1000Sd3VL;Vq;A2M0A2S1S5dS5eG0Z28A2M1Sd6VL;A1A2S1S0S54S61G0Z8A2Z0A3S1S4S5dG1Z10000A2S5dZ5b000G0A2A2S4S5dS5eZ5a3d0M2Z3a0A2G0A2S5dG1G2A2A2A2A2A2A2F_;").
Proof using HLV. exact (U.Mal_agrp__G17.Mal_agrp_F.keyR ia cur Lc mWc vmc HLV q). Qed.
Lemma keys_apart q q' : ltac2:(tb__ "0|4|
Sb1S8cVq;S118Vcur;A1M0A3Sb1S8cVq';G0A3S3S0S8cVq;Vq';A3A1S4S5dS5eSd3VL;Vq;A2M1Z28M2A2Sd3VL;Vq';A2M3A2S5dS5eG3G2A2G1A2A2F_;F_;F_;").
Proof using HLV. exact (U.Mal_agrp__G17.Mal_agrp_F.keys_apart ia cur Lc mWc vmc HLV q q'). Qed.
Definition zm : Z := zA ia m.
Definition zfm : Z := addr_of L fm.
Definition zhp : Z := addr_of L hp.

Lemma MR0 : ltac2:(tb__ "0|2|
S1S5dZ1000S106A2S1S5dS5eS106Z28A2M0Sd6S8aVia;A1A1A2S1S0S54S61S106Z8A2Z0A3S1S4S5dG0Z10000A2S5dZ5b000S106A2A2S4S5dS5eZ5a3d0M1Z3a0A2S106A2S5dG0G1A2A2A2A2A2A2").
Proof using Hi. exact (m_R ia Hi). Qed.
Lemma MR : ltac2:(tb__ "0|2|
S1S5dZ1000S106A2S1S5dS5eS106Z28A2M0Sd6VL;A1A2S1S0S54S61S106Z8A2Z0A3S1S4S5dG0Z10000A2S5dZ5b000S106A2A2S4S5dS5eZ5a3d0M1Z3a0A2S106A2S5dG0G1A2A2A2A2A2A2").
Proof using Hi HLV.   pose proof (m_R ia Hi) as H. unfold zm, L. rewrite (lv_top ia cur Lc mWc vmc HLV). exact H. Qed.
Lemma Kfm : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3Sb1S8cVfm;S118Vcur;A1A3F_;"). Proof using HSH. intros Hs. exact (MT_Some_In_keys _ _ _ (proj1 (proj2 (HSHt Hs)))). Qed.
Lemma Khp : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3Sb1S8cVhp;S118Vcur;A1A3F_;"). Proof using HSH. intros Hs. exact (MT_Some_In_keys _ _ _ (proj2 (proj2 (HSHt Hs)))). Qed.
Lemma FR : ltac2:(tb__ "0|c|
S0S42Vsh;S43A3S1S1S5dZ1000M0S108A2S1S5dS5eS108Z28M1A2M2Sd6VL;A1M3A2S1S0S54S61S108Z8M4A2Z0M5A3S1S4S5dG2Z10000M6A2S5dZ5b000M7S108A2A2S4S5dS5eZ5a3d0M8Z3a0A2M9S108A2S5dG2G8A2A2A2A2A2A2S1S1S5dG0S109A2S1S5dS5eS109G1A2MaG3A2S1S0S54S61S109G4A2G5A3S1S4S5dGaG6A2S5dG7S109A2A2S4S5dG9S109A2S5dGaG8A2A2A2A2A2A2S1S4S5dG2S106A2S5dS5eS106G1A2MbS108A2A2S1S4S5dGaS106A2S5dGbS109A2A2S4S0S8cVfm;Vhp;A3S4S5dG2S109A2S5dGaS108A2A2A2A2A2A2A2F_;").
Proof using HLV HSH vm.
  intros Hs. destruct (fm_ne Hs) as [N1 N2]. pose proof (Kfm Hs) as K1. pose proof (Khp Hs) as K2.
  split; [exact (keyR fm K1)|]. split; [exact (keyR hp K2)|].
  pose proof (keys_apart fm m K1 Lkey N1) as D1. pose proof (keys_apart hp m K2 Lkey N2) as D2. rewrite Lma in D1, D2. fold zm zfm zhp in D1, D2.
  split; [exact D1|]. split; [exact D2|].
  destruct (sptr_eq_dec fm hp) as [E|NE]; [left; exact E | right]. exact (keys_apart fm hp K1 K2 NE).
Qed.

Lemma HromF : rom_ok segsU msF. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.
Lemma HroF : ro_clear segsU msF. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HsmL)))))). Qed.
Lemma Erm : ltac2:(tb__ "0|0|
S0SceQ40A1S46SceQ8A1A1F_;S26Vrho6;A1VmWc;A3"). Proof using Hag. exact (proj2 (proj2 Hag)). Qed.
Lemma E190 : ltac2:(tb__ "0|1|
S0SceQ40M0A1S14Vrho6;S179PbeA1A2ScfG0S106A2A3").
Proof using Hag. cbn [eval v]. rewrite (proj1 Hag 190%positive eq_refl). reflexivity. Qed.
Lemma E255 : ltac2:(tb__ "0|1|
S0S42Vsh;S43A3S0SceQ40M0A1S14Vrho6;SdPffA1A2ScfG0S108A2A3F_;"). Proof using H25. intros Hs. cbn [eval]. exact (proj1 (H25t Hs)). Qed.
Lemma E256 : ltac2:(tb__ "0|1|
S0S42Vsh;S43A3S0SceQ40M0A1S14Vrho6;SdP100A1A2ScfG0S109A2A3F_;"). Proof using H25. intros Hs. cbn [eval]. exact (proj2 (H25t Hs)). Qed.

Lemma RGm : ltac2:(tb__ "0|0|
S0S45S54S54A2S24Vrho6;VOm;A2S41S54S54S5eS106Z0A2S5eS106Z28A2A4A3").
Proof using Hag Hi OmG. pose proof OmG as (G1 & G2 & G3 & _). unfold obj_range, obj_lo_of, obj_hi_of. rewrite G1, G2, G3. rewrite E190, !soff_lit_small, u64 by (pose proof MR0; top_ranges; lia). reflexivity. Qed.
Lemma RGfh : ltac2:(tb__ "0|1|
S0S45S54S54A2S24Vrho6;S18cVsh;A1A2S41S54S54S5eZ5a3c8M0Z18A2S5eG0Z20A2A4A3").
Proof using req sc. unfold obj_range, obj_lo_of, obj_hi_of, O_fhE, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small, u64 by lia. reflexivity. Qed.
Lemma RGfmp : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3S0S45S54S54A2S24Vrho6;S18aA2S41S54S54S5eS108Z0A2S5eS108Z8A2A4A3F_;").
Proof using H25 HLV HSH m req sc vm. intros Hs. pose proof (proj1 (FR Hs)) as F. unfold obj_range, obj_lo_of, obj_hi_of, O_fmpE. cbn [ob_base ob_lo ob_hi]. rewrite (E255 Hs), !soff_lit_small, u64 by (top_ranges; lia). reflexivity. Qed.
Lemma RGhpn : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3S0S45S54S54A2S24Vrho6;S18bA2S41S54S54S5eS109Z8A2S5eS109Z10A2A4A3F_;").
Proof using H25 HLV HSH m req sc vm. intros Hs. pose proof (proj1 (proj2 (FR Hs))) as F. unfold obj_range, obj_lo_of, obj_hi_of, O_hpnE. cbn [ob_base ob_lo ob_hi]. rewrite (E256 Hs), !soff_lit_small, u64 by (top_ranges; lia). reflexivity. Qed.

Lemma DSP d : ltac2:(tb__ "0|0|
Sb1S6dVd;VP;A3S14eVia;Vd;A2F_;").
Proof using Hx Pchk.
  intros Hd. pose proof (proj1 (forallb_forall _ _) Pchk d Hd) as CK. apply andb_prop in CK as [CK C3]. apply andb_prop in CK as [C1 C2].
  split; [exact C1|]. split; [| exact (dcond2b_sound _ _ _ d Hx C3)].
  unfold od2_semb in C2. apply forallb_forall. intros [[o' w'] e] Hc. cbn [snd].
  pose proof (proj1 (forallb_forall _ _) C2 e (dcells2_svs _ d _ _ e Hc)) as S. unfold sv_sem in S. apply andb_prop in S as [_ S]. exact S.
Qed.
Lemma RGP d : ltac2:(tb__ "0|0|
Sb1S6dVd;VP;A3S0S45S54S54A2S24Vrho6;S6eVd;A1A2S41S54S54S148Via;Vd;A2S149Via;Vd;A2A4A3F_;").
Proof using Hag Hi Hx Pchk. intros Hd. exact (rngD ia Hi mWc d rho6 (DSP d Hd) Hag). Qed.
Lemma RGP_cases d : ltac2:(tb__ "0|8|
Sb1S6dVd;VP;A3S41S54S54S148Via;Vd;A2S149Via;Vd;A2A4S45S54S54A2M0S4S1S0S6dVd;S76SbZcA1A1A3M1S0G0R1S41S54S54Sd4Sd1A1M2S5eG2Z4A2A4M3A3A2S1S3G1A1S1S4S5S55S55S0S46S55A1M4S14fVd;A1M5S47S55R1A2A3Ll;A2S0G4G5S4cS55A1A3A2S1S25R1S41S54S54S5eZ5a3c8M6Z18A2S5eG6Z20A2A4A2S1S25R1G3A2S8cSb1S8cR1S118Vcur;A1A3S25R3S41S54S54Sd3VL;R2A2M7S5eG7Z28A2A4A2F_;Fq;A2A2A2A2A2Tr;F_;").
Proof using PCASES. exact (PCASES d). Qed.

Definition mF : word -> option byte := ltac2:(tb__ "0|0|
S1c0Vrho6;S107VmsF;A3").
Definition rhoA : valuation := ltac2:(tb__ "0|0|
S35S15Vrho6;A1S1fVrho6;A1S10bA3").
Lemma rel : ltac2:(tb__ "0|4|
S1S20SccS111S10cS41S44S17fA1S17dVtr;S17eVmsF;Vmd;A2A4A4S1SceQ40A1M0S3S197Vrho6;S107R1A3M1A1S0S46SceQ8A1A1M2S10bR2A1M3S26Vrho6;R2A2A3F_;Fa;S1G0G1S0G2G3S192VmsF;R2A2A3F_;Fa;S160SeS22SccVrho6;VmsF;A3S107A3A2A2A2").
Proof using EO HsmL LFswf. exact (smatch_release_suffix segsU rho6 Lf tr msF md [stk] HAND (ss_next Lf) HsmL EO LFswf). Qed.
Lemma HOLD o : ltac2:(tb__ "0|0|
Sb1SeVo;S107A3S22SccVrho6;VmsF;Vo;A4F_;").
Proof using EO HsmL LFswf. intros Ho. exact (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 rel))) o Ho). Qed.
Lemma In_m5 : In Om HAND. Proof using . left. reflexivity. Qed.
Lemma In_P d : ltac2:(tb__ "0|0|
Sb1S6dVd;VP;A3Sb1SeS6eVd;A1S107A3F_;"). Proof using . intros Hd. right. apply in_app_iff. left. apply in_map. exact Hd. Qed.
Lemma In_R o : ltac2:(tb__ "0|0|
Sb1SeVo;S18dVsh;A1A3Sb1SeVo;S107A3F_;"). Proof using . intros Ho. right. apply in_app_iff. right. exact Ho. Qed.
Lemma In_fh : ltac2:(tb__ "0|0|
Sb1SeS18cVsh;A1S107A3"). Proof using H25 HSH OmC. apply In_R. unfold RING. destruct sh; left; reflexivity. Qed.
Lemma In_fmp : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3Sb1SeS18aS107A3F_;"). Proof using . intros Hs. apply In_R. unfold RING. rewrite Hs. right. left. reflexivity. Qed.
Lemma In_hpn : ltac2:(tb__ "0|0|
S0S42Vsh;S43A3Sb1SeS18bS107A3F_;"). Proof using . intros Hs. apply In_R. unfold RING. rewrite Hs. right. right. left. reflexivity. Qed.

Definition touched (y : Z) : Prop := ltac2:(tb__ "0|3|
S4S1S5dS106Vy;A2S5fVy;S5eS106Z28A2A2A2S4S1S5dS5eZ5a3c8M0Z18A2Vy;A2S5fVy;S5eG0Z20A2A2A2S4S1S0S42Vhe;S43A3S1S5dSd4Sd1A1M1Vy;A2S5fVy;S5eG1Z4A2A2A2A2S1S0S42Vsh;S43A3S4S1S5dS108Vy;A2S5fVy;S5eS108Z8M2A2A2A2S1S5dS5eS109G2A2Vy;A2S5fVy;S5eS109Z10A2A2A2A2A2A2A2A2").
Lemma touched_dec y : ltac2:(tb__ "0|1|
S1acS10eVy;A1M0S3G0A1A2").
Proof using H25 HSH Herrno OmC Perrno.
  unfold touched.
  destruct (Z_le_dec zm y) as [A1|A1]; [destruct (Z_lt_dec y (zm + 40)) as [A2|A2]; [left; lia|]|].
  all: destruct (Z_le_dec (0x5a3c8 + 24) y) as [B1|B1]; [destruct (Z_lt_dec y (0x5a3c8 + 32)) as [B2|B2]; [left; lia|]|].
  all: assert (HE : {he = true /\ mc_errno C_U <= y < mc_errno C_U + 4} + {~ (he = true /\ mc_errno C_U <= y < mc_errno C_U + 4)})
    by (destruct he; [|right; intros [H _]; discriminate H]; destruct (Z_le_dec (mc_errno C_U) y); [destruct (Z_lt_dec y (mc_errno C_U + 4)); [left; split; [reflexivity|lia]|]|]; right; intros [_ H]; lia).
  all: destruct HE as [HE|HE]; [left; right; right; left; exact HE|].
  all: assert (HS : {sh = true /\ (zfm <= y < zfm + 8 \/ zhp + 8 <= y < zhp + 16)} + {~ (sh = true /\ (zfm <= y < zfm + 8 \/ zhp + 8 <= y < zhp + 16))})
    by (destruct sh; [|right; intros [H _]; discriminate H];
        destruct (Z_le_dec zfm y); [destruct (Z_lt_dec y (zfm + 8)); [left; split; [reflexivity|lia]|]|];
        (destruct (Z_le_dec (zhp + 8) y); [destruct (Z_lt_dec y (zhp + 16)); [left; split; [reflexivity|lia]|]|]); right; intros [_ H]; lia).
  all: destruct HS as [HS|HS]; [left; do 3 right; exact HS|].
  all: right; intros [H|[H|[H|H]]]; first [lia | exact (HE H) | exact (HS H)].
Qed.

Lemma hand_cases a : ltac2:(tb__ "0|1|
S197Vrho6;S107Va;A3S4S10eSd0Q40Va;A2M0A1S5S6dS6dS1Sb1S6dR1VP;A3S1S3S0S6dR1S76SbZcA1A1A3A1S1S5dS148Via;R1A2G0A2S5fG0S149Via;R1A2A2A2A2A2Ld;A2A2F_;").
Proof using H25 HLV HSH Hag Herrno Hi Hx OmG PCASES Pchk Perrno vm.
  intros (o & Ho & R). unfold HAND in Ho. destruct Ho as [<- | Ho]; [|apply in_app_iff in Ho as [Ho | Ho]].
  - left. rewrite RGm in R. cbn [fst snd] in R. unfold touched. lia.
  - apply in_map_iff in Ho as (d & <- & Hd). rewrite (RGP d Hd) in R. cbn [fst snd] in R.
    destruct (RGP_cases d Hd) as [[-> E] | (NE & _)]; [left | right; exists d; auto].
    pose proof (proj1 (Perrno _ Hd)) as HE.
    clear E. unfold dlo2, dhi2, od2_range, od2_rangeP in R. cbn [fst snd] in R. unfold touched, mc_errno. right. right. left. split; [exact HE | lia].
  - left. unfold RING in Ho. destruct (Sumbool.sumbool_of_bool sh) as [Es|Es]; rewrite Es in Ho.
    + destruct Ho as [<-|[<-|[<-|[]]]].
      * rewrite <- Es, RGfh in R. cbn [fst snd] in R. unfold touched. lia.
      * rewrite (RGfmp Es) in R. cbn [fst snd] in R. unfold touched. do 3 right. split; [exact Es | lia].
      * rewrite (RGhpn Es) in R. cbn [fst snd] in R. unfold touched. do 3 right. split; [exact Es | lia].
    + destruct Ho as [<-|[]]. rewrite <- Es, RGfh in R. cbn [fst snd] in R. unfold touched. lia.
Qed.

Lemma HOLDW d : ltac2:(tb__ "0|0|
Sb1S6dVd;VP;A3S3S0S6dVd;S76SbZcA1A1A3A1S22SccS71Via;VmWc;A2S177VmsF;VmWc;A2S6eVd;A1A4F_;F_;").
Proof using ENTRY HLV Hi HsmL L vm. intros Hd NE. exact (od2_hold ia Hi cur L mWc vm HLV msF HromF d (ENTRY d Hd NE)). Qed.

Lemma pass_bytes d y : ltac2:(tb__ "0|1|
Sb1S6dVd;VP;A3S3S0S6dVd;S76SbZcA1A1A3A1S1S5dS148Via;Vd;A2Vy;A2S5fVy;S149Via;Vd;A2A2A2S1S0S46SceQ8A1A1S112SccS10bScfQ40Vy;A2M0A3S112SccVmWc;G0A3A3S0S42S113SccS10bG0A3S113SccVmWc;G0A3A3A2F_;F_;F_;").
Proof using ENTRY EO HLV Hag Hi HsmL Hx L LFswf Pchk vm.
  intros Hd NE Hy. pose proof (DSP d Hd) as DD. pose proof (range64D ia Hi d DD) as R64.
  assert (Hy64 : 0 <= y < 2 ^ 64) by lia.
  assert (INR : in_ranges rho6 HAND (Z_to_bv 64 y)).
  { exists (obj_of2 d). split; [exact (In_P d Hd)|]. rewrite (RGP d Hd). cbn [fst snd]. rewrite u64 by lia. lia. }
  pose proof (proj1 (proj2 (proj2 rel)) _ INR) as IN.
  destruct (drom2 d) as [l|] eqn:Ed.
  - destruct (romD ia Hi cur L mWc vm HLV d l y DD Ed Hy) as [Hro Hnone].
    assert (E : mF (Z_to_bv 64 y) = mWc (Z_to_bv 64 y)) by (rewrite IN, Hnone; exact (HroF _ Hro)).
    split; [exact (rd_of_mem segsU _ _ _ E) | exact (wok_of_mem segsU _ _ _ E)].
  - destruct (coverD ia Hi d y DD Ed Hy) as (off & w & e & Hc & Hoff).
    destruct (cellsD ia Hi mWc d off w e DD Hc) as (c & Hcin & Hval & Hw & Haddr).
    pose proof (HOLD (obj_of2 d) (In_P d Hd)) as H6. pose proof (HOLDW d Hd NE) as HW.
    set (j := Z.to_nat (y - (dlo2 ia d + off))).
    assert (Hj : (j < Z.to_nat (c_width c))%nat) by (rewrite Hw; subst j; lia).
    pose proof (cell_bytes_sym segsU rho6 msF (obj_of2 d) c j H6 Hcin Hj) as B6.
    pose proof (cell_bytes_sym segsU (rho2 ia mWc) (with_mem msF mWc) (obj_of2 d) c j HW Hcin Hj) as BW.
    rewrite (Haddr rho6 Hag) in B6. rewrite (Haddr (rho2 ia mWc) (agrees_refl _)) in BW.
    replace (dlo2 ia d + off + Z.of_nat j) with y in B6, BW by (subst j; lia).
    pose proof (semD ia Hi mWc d off w e DD Hc) as [Sv Sz].
    rewrite Hval, (EVR ia mWc rho6 e Hag Sv Sz) in B6. rewrite Hval, (EVR ia mWc (rho2 ia mWc) e (agrees_refl _) Sv Sz) in BW.
    split.
    + rewrite (rd_of_at segsU mF msF _ HromF IN), (rd_of_at segsU mWc (with_mem msF mWc) _ HromF eq_refl). rewrite B6, BW. reflexivity.
    + pose proof H6 as (_ & WV6 & _). pose proof HW as (_ & WVW & _).
      assert (Hoff' : obj_lo_of rho6 (obj_of2 d) <= y - bv_unsigned (eval rho6 (ob_base (obj_of2 d))) < obj_hi_of rho6 (obj_of2 d)).
      { pose proof (RGP d Hd) as RG. unfold obj_range in RG. injection RG as E1 E2. lia. }
      assert (HoffW : obj_lo_of (rho2 ia mWc) (obj_of2 d) <= y - bv_unsigned (eval (rho2 ia mWc) (ob_base (obj_of2 d))) < obj_hi_of (rho2 ia mWc) (obj_of2 d)).
      { pose proof (rngD ia Hi mWc d (rho2 ia mWc) DD (agrees_refl _)) as RG. unfold obj_range in RG. injection RG as E1 E2. lia. }
      pose proof (WV6 _ Hoff' ltac:(rewrite (dunkD ia d DD Ed); reflexivity)) as W6.
      pose proof (WVW _ HoffW ltac:(rewrite (dunkD ia d DD Ed); reflexivity)) as WW. cbn [with_mem ms_mem] in WW.
      replace (bv_unsigned (eval rho6 (ob_base (obj_of2 d))) + (y - bv_unsigned (eval rho6 (ob_base (obj_of2 d))))) with y in W6 by lia.
      replace (bv_unsigned (eval (rho2 ia mWc) (ob_base (obj_of2 d))) + (y - bv_unsigned (eval (rho2 ia mWc) (ob_base (obj_of2 d))))) with y in WW by lia.
      rewrite (wok_of_at segsU mF msF _ IN W6). symmetry. apply wok_of_wview. exact WW.
Qed.

Lemma V1 y : ltac2:(tb__ "0|4|
S1S5dZ0Vy;A2S5fVy;S60Z2Z40A2A2A2S3S10eVy;A1A1S1S0S46S54A1M0Sd2S112SccS10bA2M1S113SccS10bA2Vy;A3Sd2S112SccVmWc;A2M2S113SccVmWc;A2Vy;A3A3S0G0Sd2G1SceQ40A1S43L_;M3Vy;A3Sd2G2G3Vy;A3A3A2F_;F_;").
Proof using ENTRY EO H25 HLV HSH Hag Herrno Hi HsmL Hx LFswf OmG PCASES Pchk Perrno vm.
  intros Hy NT.
  assert (E : Glue.rd_of segsU mF (Z_to_bv 64 y) = Glue.rd_of segsU mWc (Z_to_bv 64 y) /\ Glue.wok_of segsU mF (Z_to_bv 64 y) = Glue.wok_of segsU mWc (Z_to_bv 64 y)).
  { destruct (in_ranges_dec rho6 HAND (Z_to_bv 64 y)) as [I0 | O0].
    - destruct (hand_cases _ I0) as [T | (d & Hd & NE & R)]; [exfalso; apply NT; rewrite u64 in T by lia; exact T|].
      rewrite u64 in R by lia. exact (pass_bytes d y Hd NE R).
    - pose proof (proj1 (proj2 rel) _ O0) as E0. rewrite Erm in E0. split; [exact (rd_of_mem segsU _ _ _ E0) | exact (wok_of_mem segsU _ _ _ E0)]. }
  destruct E as [E1 E2]. unfold byteview_of. rewrite E1, E2. split; reflexivity.
Qed.

Lemma m_notX : ~ In m X.
Proof using H25 HLV HSH Hi OmC PV YF vm. intros Hin. pose proof (proj2 (inv_X post_I m Hin)) as M. rewrite s'_Mm in M. destruct sh; exact M. Qed.
Lemma post_X : xraw X s'.
Proof using H25 HLV HSH Hi OmC PV YF vm.
  intros q Hq. assert (Hq' : In q (m :: X)) by (right; exact Hq). pose proof (LXr q Hq') as R.
  assert (NQ : q <> m) by (intros ->; exact (m_notX Hq)).
  rewrite (s'_Mother q NQ); [exact R|]. intros Hs. destruct (HSHt Hs) as (_ & Mfm & Mhp).
  split; intros ->; destruct R as [E|E]; first [rewrite E in Mfm; discriminate Mfm | rewrite E in Mhp; discriminate Mhp].
Qed.
Lemma D_fp : ltac2:(tb__ "0|0|
S0S44S45S116S54A2A1S11aS105A1S11aVcur;A1A3"). Proof using HSH LMI PV. exact (proj1 delta_s'). Qed.
Lemma D_ub : ltac2:(tb__ "0|0|
S0S44S45S8cS54A2A1S120S105A1S120Vcur;A1A3"). Proof using HSH LMI PV. exact (proj1 (proj2 delta_s')). Qed.
Lemma D_init : ltac2:(tb__ "0|0|
S0S42Sa7S105A1Sa7Vcur;A1A3"). Proof using HSH LMI PV. exact (proj1 (proj2 (proj2 delta_s'))). Qed.
Lemma D_regions : ltac2:(tb__ "0|0|
S0S44S90A1S95S105A1S95Vcur;A1A3"). Proof using HSH LMI PV. exact (proj1 (proj2 (proj2 (proj2 (proj2 delta_s'))))). Qed.
Lemma D_brk : ltac2:(tb__ "0|0|
S0Sa1S98S105A1S98Vcur;A1A3"). Proof using HSH LMI PV. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 delta_s')))))). Qed.
Lemma D_cells : ltac2:(tb__ "0|0|
S114Sb1S114R1S4bS114S11dS105A1S18fS105A1A3A3S4Sb1S114R2S4bS114S11dVcur;A1S18fVcur;A1A3A3Sb1S116S119R2A1S10fA3A2F_;Fc;").
Proof using HSH LMI PV. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 delta_s'))))))))))). Qed.
Lemma region_of' k : ltac2:(tb__ "0|0|
S0S46S90A1S125S105Vk;A2S125Vcur;Vk;A2A3"). Proof using HSH LMI PV. unfold region_of. rewrite D_regions. reflexivity. Qed.
Lemma HL' : layout_ok L s'.
Proof using HSH LMI PV.
  pose proof LL as (A1 & B & C' & D). split; [exact A1|]. split; [|rewrite D_fp; split; [exact C' | exact D]].
  intros k rg Hr Hl. rewrite region_of' in Hr. exact (B k rg Hr Hl).
Qed.
Lemma Hbounded' : bounded s'.
Proof using HSH LMI PV.
  pose proof (mig_bounded LMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4. pose proof delta_s' as (_&_&_&Da&Dr&_&_&Du&Dsh&Dac&Dap&_).
  unfold bounded. unfold usage_of in *. rewrite Du, Dsh, Da, Dac, Dap, Dr. auto.
Qed.
Lemma Hvm' : ltac2:(tb__ "0|0|
Sd9VL;S105Vvm;A3").
Proof using HSH LMI PV.
  pose proof LV as (V1' & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). unfold vm_ok.
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V1' r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V2 r rg Hr)|].
  split; [rewrite D_brk; exact V3|].
  split; [rewrite D_fp; exact V4|].
  split; [intros r rg off Hr; rewrite region_of' in Hr; exact (V5 r rg off Hr)|].
  split; [intros r1 r2 rg1 rg2 Hne H1 H2; rewrite region_of' in H1, H2; exact (V6 r1 r2 rg1 rg2 Hne H1 H2)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V7 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V8 r rg Hr)|].
  split; [intros r rg q n0 Hr Hk Hl Hin Hne; rewrite region_of' in Hr; rewrite D_fp in Hin; exact (V9 r rg q n0 Hr Hk Hl Hin Hne)|].
  split; [intros rb p k rgk Hb Hr Hk Hl; rewrite region_of' in Hr; rewrite D_brk in Hb; exact (V10 rb p k rgk Hb Hr Hk Hl)|].
  exact V11.
Qed.

Definition bv1 : byteview := ltac2:(tb__ "0|0|
Sd2S112SccS10bA2S113SccS10bA2A2").
Lemma hand_byte o c j : ltac2:(tb__ "0|7|
Sb1SeVo;S107A3S0S1dS1cVo;A1S18A3Sb1S10Vc;S1eVo;A1A3S17bVj;S6cS3cVc;A1A1M0A2Sd0Q40S14Vrho6;S1bVo;A1A2A2S54S1S5dS23Vrho6;Vo;A2S5eS3eVrho6;S3aVc;A1A2M1S62Vj;A1M2A2M3A2S5fG3S21Vrho6;Vo;A2A2A2S1S5dZ0M4S5eS5eR2G1A2G2A2M5A2S5fG5S60Z2Z40A2A2A2S0S46S54A1S10dS5eS5eR3G1A2G2A2A1S47S54Sd0Q8M6S15fSceG6A1Vj;S3dG0S14Vrho6;S3bVc;A1A2A2ScfG6G4A2A4A2A2A3F_;F_;Tb;F_;F_;F_;F_;").
Proof using EO HsmL LFswf req sc.
  intros Ho Hd Hc Hj b Hoff Hy. pose proof (HOLD o Ho) as H6.
  assert (INR : in_ranges rho6 HAND (Z_to_bv 64 (b + soff rho6 (c_off c) + Z.of_nat j))).
  { exists o. split; [exact Ho|]. unfold obj_range. cbn [fst snd]. rewrite u64 by lia. subst b. lia. }
  pose proof (proj1 (proj2 (proj2 rel)) _ INR) as IN.
  pose proof (cell_bytes_sym segsU rho6 msF o c j H6 Hc Hj) as B6. fold b in B6.
  pose proof H6 as (_ & WV & _). pose proof (WV (soff rho6 (c_off c) + Z.of_nat j) Hoff ltac:(rewrite Hd; reflexivity)) as W6.
  replace (bv_unsigned (eval rho6 (ob_base o)) + (soff rho6 (c_off c) + Z.of_nat j)) with (b + soff rho6 (c_off c) + Z.of_nat j) in W6 by (subst b; lia).
  unfold bv1, byteview_of. replace ((0 <=? b + soff rho6 (c_off c) + Z.of_nat j) && (b + soff rho6 (c_off c) + Z.of_nat j <? 2 ^ 64)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite (wok_of_at segsU mF msF _ IN W6). cbn [andb]. rewrite (rd_of_at segsU mF msF _ HromF IN), B6. reflexivity.
Qed.

Lemma cell_from_bytes (bv : byteview) c z : ltac2:(tb__ "0|2|
S0S46S54A1M0S193VL;Vc;A2S47S54Vz;A2A3S4aS17bR1S11eVc;A1M1A2S0G0Vbv;S5eS117VL;S119Vc;A1A2S62R2A1A2A1S47S54S123Vz;G1R2A3A2A3F_;Fj;S11fVL;Vbv;Vc;A3F_;F_;").
Proof using Lc. intros Hz BY. destruct c as [loc wc val]. cbn in Hz, BY |- *. unfold MallocInv.cell_holds. cbn [mc_loc mc_w mc_val]. destruct val; try (injection Hz as <-; exact BY). discriminate. Qed.
Lemma le_byte_0 w j : le_byte 0 w j = 0.
Proof using req sc. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.

Lemma cell8 o c (off : Z) (e : sv) (mc : mcell) (z : Z) : ltac2:(tb__ "0|7|
Sb1SeVo;S107A3S0S1dS1cVo;A1S18A3Sb1S10Vc;S1eVo;A1A3S0S10Vc;S12SbVoff;A1Z8M0Ve;A3A3S5dS23Vrho6;Vo;A2Voff;A2S5dS5eVoff;G0A2S21Vrho6;Vo;A2A2S1S5dS68S60Z2M1Z3eA2M2A1Voff;A2S5dVoff;G2A2A2S5dZ0M3S5eSd0Q40M4S14Vrho6;S1bVo;A1A2A2Voff;A2M5A2S5fS5eG5G0A2S60G1Z40A2M6A2S0S54S117VL;S119Vmc;A1A2G5A3S0S4aS11eVmc;A1U8A3S0S46S54A1S193VL;Vmc;A2S47S54Vz;A2A3S1S5dG3Vz;A2S5fVz;G6A2A2S0SceG4A1S14Vrho6;Ve;A2ScfG4Vz;A2A3S11fVL;S10dVmc;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EO HsmL LFswf Lc req sc.
  intros Ho Hd Hc Ec Hlo Hhi Hoff Hb0 Hb1 Ha Hw Hz Hzr He. apply (cell_from_bytes bv1 mc z Hz). intros j Hj. rewrite Ha, Hw. rewrite Hw in Hj.
  pose proof (hand_byte o c j Ho Hd Hc ltac:(subst c; cbn; lia)) as B. subst c. cbn [c_off c_width c_val] in B. rewrite soff_lit_small in B by lia.
  rewrite (B ltac:(lia) ltac:(lia)). change (Z.to_nat 8) with 8%nat. rewrite He, nth_enc_bytes by lia. f_equal. rewrite Z_to_bv_unsigned. pose proof (le_byte_range z 8 j) as LR. apply bv_wrap_small. change (bv_modulus 8%N) with 256. exact LR.
Qed.

Lemma cell4z o c (off : Z) (mc : mcell) (k : nat) : ltac2:(tb__ "0|5|
Sb1SeVo;S107A3S0S1dS1cVo;A1S18A3Sb1S10Vc;S1eVo;A1A3S0S10Vc;S12SbVoff;A1Z8M0SbZ0M1A1A3A3S5dS23Vrho6;Vo;A2Voff;A2S5dS5eVoff;G0A2S21Vrho6;Vo;A2A2S1S5dS68S60Z2M2Z3eA2M3A1Voff;A2S5dVoff;G3A2A2S5dG1S5eSd0Q40S14Vrho6;S1bVo;A1A2A2Voff;A2M4A2S5fS5eG4G0A2S60G2Z40A2A2S0S54S117VL;S119Vmc;A1A2S5eG4S62Vk;A1A2A3S17cS1d0Vk;S11eVmc;A1A2U8A2S0S46S54A1S193VL;Vmc;A2S47S54G1A2A3S11fVL;S10dVmc;A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EO HsmL LFswf Lc req sc.
  intros Ho Hd Hc Ec Hlo Hhi Hoff Hb0 Hb1 Ha Hw Hz. apply (cell_from_bytes bv1 mc 0 Hz). intros j Hj. rewrite Ha.
  pose proof (hand_byte o c (k + j) Ho Hd Hc ltac:(subst c; cbn; lia)) as B. subst c. cbn [c_off c_width c_val eval] in B. rewrite soff_lit_small in B by lia.
  replace (bv_unsigned (eval rho6 (ob_base o)) + off + Z.of_nat k + Z.of_nat j) with (bv_unsigned (eval rho6 (ob_base o)) + off + Z.of_nat (k + j)) by lia.
  rewrite (B ltac:(lia) ltac:(lia)). change (Z.to_nat 8) with 8%nat. rewrite nth_enc_bytes, !le_byte_0 by lia. reflexivity.
Qed.

Lemma loc_m off : ltac2:(tb__ "0|0|
S0S54S117VL;S11cS9eVm;Voff;A2A1A2S5eS106Voff;A2A3"). Proof using HLV vm. rewrite (loc_addr_padd L m off), Lma. reflexivity. Qed.
Lemma loc_q q off : ltac2:(tb__ "0|0|
S0S54S117VL;S11cS9eVq;Voff;A2A1A2S5eSd3VL;Vq;A2Voff;A2A3"). Proof using Lc. exact (loc_addr_padd L q off). Qed.
Lemma cellZ_optr p : ltac2:(tb__ "0|0|
S0S46S54A1S193VL;S122S11cVp;A1U8S132S47S8cVp;A2A1A3A2S47S54Sd3VL;Vp;A2A2A3"). Proof using Lc. reflexivity. Qed.

Definition gmeets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S5S4aS4aS1S17bR1S11eVc;A1A2S10eS5eS117VL;S119Vc;A1A2S62R1A1A2A1A2Lk;A2").
Lemma keys' q : ltac2:(tb__ "0|0|
Sb1S8cVq;S118Vcur;A1A3Sb1S8cVq;S118S105A1A3F_;"). Proof using HSH LMI PV. rewrite s'_keys. exact (fun H => H). Qed.
Lemma no_cell_errno c : ltac2:(tb__ "0|0|
Sb1S114Vc;S4bS114S11dS105A1S18fS105A1A3A3S1c2VL;Vc;Sd4Sd1A1Z4A4S8F_;F_;").
Proof using H25 HSH Hi LMI OmC PV YF.
  intros Hc (k & Hk & R). pose proof Lctx as HCX.
  destruct (cell_in_footprintI X None U s' L post_I post_X c Hc) as ([l n] & Hrg & [I1 I2]).
  unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2.
  destruct (footprint_entry_cases' s' l n Hrg) as [[-> ->] | [p ->]].
  - change (loc_addr L (LCtx 0)) with (ly_ctx L + 0) in I1, I2. rewrite HCX in I1, I2. rewrite errno_U in R. unfold CTX_SIZE in *. lia.
  - pose proof (fp_mem_range C_U L s' vm p n Hvm' LLG Hrg ltac:(lia)) as (R1 & R2 & R3).
    change (loc_addr L (LMem p)) with (addr_of L p) in I1, I2. rewrite errno_U in R. cbn [mc_img_lo mc_img_hi C_U] in R3. lia.
Qed.

Lemma m5_cells : ltac2:(tb__ "0|5|
S10S7Sb1S10R1S1eVOm;A1A3Sb1S10R1S4bS10S42S44S10A1Lsh;Vsh;S40S10S12SbZ0A1M0Z8M1SdP100A1A3S40S10S12SbG1A1M2G1SdPffA1A3S48S10A1M3A3A3S40S10S12G2G1S179PbeA1M4A3S40S10S12G0G1G4A3G3A3A3X42x2S40S10S12SbZ10A1G1G0A3S40S10S12SbZ18A1G1G0A3S40S10S12SbZ20A1G1G0A3G3A3A3A3A3A3A2Fcc;").
Proof using OmC. exact OmC. Qed.
Lemma m5_geom : ltac2:(tb__ "0|0|
S1S0S54S23Vrho6;VOm;A2Z0A3S1S0S54S21Vrho6;VOm;A2Z28A3S1S0S54Sd0Q40S14Vrho6;S1bVOm;A1A2A2S106A3S0S1dS1cVOm;A1S18A3A2A2A2").
Proof using Hag Hi OmG.
  pose proof MR0 as M. top_ranges. pose proof OmG as (G1 & G2 & G3 & G4). unfold obj_lo_of, obj_hi_of. rewrite G1, G2, G3, G4. rewrite !soff_lit_small, E190, u64 by lia. repeat split; reflexivity.
Qed.
Lemma fh_geom : ltac2:(tb__ "0|2|
S1S0S54S23Vrho6;S18cVsh;A1M0A2Z18M1A3S1S0S54S21Vrho6;G0A2Z20A3S1S0S54Sd0Q40S14Vrho6;S1bG0A1A2A2Z5a3c8A3S1S0S1dS1cG0A1S18A3S0S44S10A1S1eG0A1S40S10S12SbG1A1Z8S42SaLsh;Vsh;SdPffA1S179PbeA1X42x2A3S48S10A1A3A3A2A2A2A2").
Proof using req sc. unfold obj_lo_of, obj_hi_of, O_fhE, U.Mal_agrp__G1.Mal_agrp_St.LK. cbn [ob_lo ob_hi ob_base ob_dflt ob_cells eval]. rewrite !soff_lit_small, u64 by lia. repeat split; reflexivity. Qed.
Lemma fmp_geom : ltac2:(tb__ "0|2|
S0S42Vsh;S43A3S1S0S54S23Vrho6;S18aA2Z0M0A3S1S0S54S21Vrho6;S18aA2Z8M1A3S1S0S54Sd0Q40S14Vrho6;S1bS18aA1A2A2S108A3S1S0S1dS1cS18aA1S18A3S0S44S10A1S1eS18aA1S40S10S12SbG0A1G1S179PbeA1A3S48S10A1A3A3A2A2A2A2F_;").
Proof using H25 HLV HSH m req sc vm. intros Hs. pose proof (proj1 (FR Hs)) as F. top_ranges. unfold obj_lo_of, obj_hi_of, O_fmpE. cbn [ob_lo ob_hi ob_base ob_dflt ob_cells]. rewrite !soff_lit_small, (E255 Hs), u64 by lia. repeat split; reflexivity. Qed.
Lemma hpn_geom : ltac2:(tb__ "0|1|
S0S42Vsh;S43A3S1S0S54S23Vrho6;S18bA2Z8M0A3S1S0S54S21Vrho6;S18bA2Z10A3S1S0S54Sd0Q40S14Vrho6;S1bS18bA1A2A2S109A3S1S0S1dS1cS18bA1S18A3S0S44S10A1S1eS18bA1S40S10S12SbG0A1G0S179PbeA1A3S48S10A1A3A3A2A2A2A2F_;").
Proof using H25 HLV HSH m req sc vm. intros Hs. pose proof (proj1 (proj2 (FR Hs))) as F. top_ranges. unfold obj_lo_of, obj_hi_of, O_hpnE. cbn [ob_lo ob_hi ob_base ob_dflt ob_cells]. rewrite !soff_lit_small, (E256 Hs), u64 by lia. repeat split; reflexivity. Qed.
Lemma Em : ltac2:(tb__ "0|1|
S0SceQ40M0A1S14Vrho6;S179PbeA1A2ScfG0Sd3VL;Vm;A2A2A3"). Proof using HLV Hag vm. rewrite Lma. exact E190. Qed.

Ltac kill_cell T Hk := exfalso; cbn [mc_loc mc_w] in T, Hk; rewrite ?loc_m, ?loc_q in T; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, zfm, zhp in T; lia.

Ltac fin8 INm Es G1 G2 G3 LOCM E256 E255 Em LMA :=
  first [ reflexivity
        | exact (E256 Es) | exact (E255 Es) | exact Em
        | apply (proj2 (INm _)); rewrite Es; cbn; tauto
        | cbn [mc_loc]; rewrite LOCM, G3; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; lia
        | rewrite ?G1, ?G2, ?G3, ?LMA; unfold zm in *; lia
        | cbn; lia ].
Theorem VIN c : ltac2:(tb__ "0|0|
Sb1S114Vc;S4bS114S11dS105A1S18fS105A1A3A3S110Vc;A1S11fVL;S10dVc;A3F_;F_;").
Proof using EO H25 HSH Hag Hi HsmL Hx LFswf LMI OmC OmG PV STK YF.
  intros Hc (k & Hk & T). pose proof E256 as E256'. pose proof E255 as E255'. pose proof Em as Em'. pose proof loc_m as loc_m'. pose proof Lma as Lma'. pose proof MR as M. top_ranges. pose proof Lctx as HCX. pose proof m5_geom as (G1 & G2 & G3 & G4).
  pose proof m5_cells as INm.
  destruct T as [Tm | [Tfh | [[_ Terr] | [Es Tq]]]].
  -
    assert (CM : cmeets L c (addr_of L m) META_SIZE) by (exists k; split; [exact Hk|]; rewrite Lma; fold zm; unfold META_SIZE; lia).
    pose proof (meta_zone X None U s' L post_I post_X HL' m c (keys' m Lkey) Hc CM) as IN6. rewrite s'_Mm in IN6.
    destruct (Sumbool.sumbool_of_bool sh) as [Es|Es]; rewrite Es in IN6; cbn [meta_slot_cells] in IN6.
    + pose proof (proj1 (FR Es)) as (F1 & F2 & _). pose proof (proj1 (proj2 (FR Es))) as (P1 & P2 & _). top_ranges.
      destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      * apply (cell8 Om (mkCell (SLit 0) 8 (SVar 256%positive)) 0 (SVar 256%positive) _ zhp In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 8) 8 (SVar 255%positive)) 8 (SVar 255%positive) _ zfm In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 16) 8 (SLit 0)) 16 (SLit 0) _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell4z Om (mkCell (SLit 24) 8 (SLit 0)) 24 _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell4z Om (mkCell (SLit 24) 8 (SLit 0)) 24 _ 4 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 32) 8 (SLit 0)) 32 (SLit 0) _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
    + destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      * apply (cell8 Om (mkCell (SLit 0) 8 (v 190)) 0 (v 190) _ (addr_of L m) In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 8) 8 (v 190)) 8 (v 190) _ (addr_of L m) In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 16) 8 (SLit 0)) 16 (SLit 0) _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell4z Om (mkCell (SLit 24) 8 (SLit 0)) 24 _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell4z Om (mkCell (SLit 24) 8 (SLit 0)) 24 _ 4 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
      * apply (cell8 Om (mkCell (SLit 32) 8 (SLit 0)) 32 (SLit 0) _ 0 In_m5 G4); fin8 INm Es G1 G2 G3 loc_m' E256' E255' Em' Lma'.
  -
    assert (CM : cmeets L c (ly_ctx L + CTX_free_meta_head) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_free_meta_head; lia).
    pose proof (ctx_fmh_cell X None U s' L post_I post_X HL' c Hc CM) as ->. rewrite s'_head.
    pose proof fh_geom as (H1 & H2 & H3 & H4 & H5).
    apply (cell8 (O_fhE sh) (mkCell (SLit 24) 8 (if sh then SVar 255%positive else v 190)) 24 (if sh then SVar 255%positive else v 190) _ (addr_of L (if sh then fm else m)) In_fh H4);
      first [ reflexivity | rewrite H5; left; reflexivity
            | cbn [mc_loc loc_addr]; rewrite HCX, H3; unfold CTX_free_meta_head; lia
            | destruct (Sumbool.sumbool_of_bool sh) as [Es|Es]; rewrite Es; first [exact (E255 Es) | exact Em]
            | destruct (Sumbool.sumbool_of_bool sh) as [Es|Es]; rewrite Es; [pose proof (proj1 (FR Es)) as (F1 & F2 & _); unfold zfm in *; top_ranges; lia | rewrite Lma; fold zm; lia]
            | rewrite ?H1, ?H2, ?H3; lia ].
  -   exfalso. apply (no_cell_errno c Hc). exists k. split; [exact Hk | exact Terr].
  -
    pose proof (FR Es) as ((F1 & F2 & _) & (P1 & P2 & _) & Dfm & Dhp & Dfh). pose proof (HSHt Es) as (Hfh & Mfm & Mhp).
    destruct Tq as [Tfm | Thp].
    + assert (CM : cmeets L c (addr_of L fm) META_SIZE) by (exists k; split; [exact Hk|]; fold zfm; unfold META_SIZE; lia).
      pose proof (meta_zone X None U s' L post_I post_X HL' fm c (keys' fm (Kfm Es)) Hc CM) as IN6. rewrite (s'_Mfm Es) in IN6. cbn [meta_slot_cells] in IN6.
      pose proof (fmp_geom Es) as (H1 & H2 & H3 & H4 & H5).
      destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try (kill_cell Tfm Hk).
      apply (cell8 O_fmpE (mkCell (SLit 0) 8 (v 190)) 0 (v 190) _ (addr_of L m) (In_fmp Es) H4);
        first [ reflexivity | rewrite H5; left; reflexivity | exact Em
              | cbn [mc_loc]; rewrite loc_q, H3; unfold META_prev, zfm; lia
              | rewrite ?H1, ?H2, ?H3, ?Lma; fold zm; top_ranges; lia ].
    + assert (CM : cmeets L c (addr_of L hp) META_SIZE) by (exists k; split; [exact Hk|]; fold zhp; unfold META_SIZE; lia).
      pose proof (meta_zone X None U s' L post_I post_X HL' hp c (keys' hp (Khp Es)) Hc CM) as IN6.
      pose proof (hpn_geom Es) as (H1 & H2 & H3 & H4 & H5).
      assert (NEXT : c = MCell (LMem (padd hp META_next)) 8 (optr (Some m))).
      { destruct (sptr_eq_dec hp fm) as [E|NE].
        - rewrite E. rewrite E in IN6. rewrite (s'_Mfm Es) in IN6. rewrite E, sptr_eqb_refl in IN6. cbn [meta_slot_cells] in IN6.
          unfold zhp in Thp. rewrite E in Thp. fold zfm in Thp.
          destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try reflexivity; kill_cell Thp Hk.
        - rewrite (s'_Mhp Es NE) in IN6. cbn [meta_slot_cells] in IN6.
          destruct IN6 as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; try reflexivity; kill_cell Thp Hk. }
      rewrite NEXT. apply (cell8 O_hpnE (mkCell (SLit 8) 8 (v 190)) 8 (v 190) _ (addr_of L m) (In_hpn Es) H4);
        first [ reflexivity | rewrite H5; left; reflexivity | exact Em
              | cbn [mc_loc]; rewrite loc_q, H3; unfold META_next, zhp; lia
              | rewrite ?H1, ?H2, ?H3, ?Lma; fold zm; top_ranges; lia ].
Qed.

End FX.
End Mal_agrp_FX.

Module Mal_agrp_NTs.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ErrnoFrame.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma errno_any (mm : word -> option byte) : ltac2:(tb__ "0|0|
S5S54S54S1S1S5dZ0R1A2S5fR1S60Z2Z20A2A2A2Sd5Sd2S112SccVmm;A2SceQ40A1S43L_;A2Sd4Sd1A1U4R1A4A2Lerv;A2").
Proof.
  assert (R : exists erv, holds (byteview_of (Glue.rd_of segsU mm) (fun _ => true)) (mc_errno C_U) 4 erv).
  { apply holds_of_readable. intros k Hk. assert (EE : mc_errno C_U = 0x3a02c) by reflexivity. rewrite EE. unfold byteview_of.
    replace ((0 <=? 0x3a02c + Z.of_nat k) && (0x3a02c + Z.of_nat k <? 2 ^ 64) && true)%bool with true
      by (symmetry; rewrite Bool.andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    assert (IMG : exists b, image_byte segsU (Z_to_bv 64 (0x3a02c + Z.of_nat k)) = Some b).
    { pose proof (forall_range_dec (fun k => match image_byte segsU (Z_to_bv 64 (0x3a02c + k)) with Some _ => true | None => false end) 0 4
                    ltac:(vm_compute; reflexivity) (Z.of_nat k) ltac:(lia)) as T. cbn beta in T.
      destruct (image_byte segsU (Z_to_bv 64 (0x3a02c + Z.of_nat k))) as [b|]; [exists b; reflexivity | discriminate]. }
    destruct IMG as [b Hb]. unfold Glue.rd_of. destruct (mm (Z_to_bv 64 (0x3a02c + Z.of_nat k))) as [b'|].
    - exists (bv_unsigned b'). split; [reflexivity|]. pose proof (urange_n 8 b') as R8. change (2 ^ Z.of_N 8) with 256 in R8. lia.
    - rewrite Hb. exists (bv_unsigned b). split; [reflexivity|]. pose proof (urange_n 8 b) as R8. change (2 ^ Z.of_N 8) with 256 in R8. lia. }
  destruct R as [erv H]. exists (erv mod 2 ^ 32). split; [apply Z.mod_pos_bound; lia|].
  intros k Hk. rewrite (H k Hk). f_equal. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma nok_intro ia Kc rhoK tr mdK : ltac2:(tb__ "0|0|
S1c5Via;VKc;VrhoK;Vtr;VmdK;A5S1VKc;Vtr;VmdK;A2S5S188S188S5S8cS8cS5S94S94S13fVia;VrhoK;VmdK;R3R2R1A6Lamg;A2Lg;A2LA2;A2A2F_;").
Proof.
  intros ((F1 & F2 & F3 & F4) & HKc & A2 & g & amg & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  split; [exact HKc|]. exists A2, g, amg. constructor; assumption.
Qed.

Definition leafN_ok (sc cnt0 : Z) (Lf : sstate) : bool := ltac2:(tb__ "0|3|
S4dS4dS1d9Vsc;VLf;A2S1d7Vsc;Vcnt0;S1d8VLf;A1M0A3A2S1adScdS145G0A1M1S166S165A1M2A3S19aS4dS4dS196G1G2R1A3S198R1ScdA2A2S3fS199R1S1a0A2SbZ0A1A2A2TsT;A2").

Lemma halve_while_even_le f cnt u : ltac2:(tb__ "0|2|
S5dZ0M0Vcnt;A2S1S5dG0S9bVf;Vcnt;Vu;A3M1A2S5dG1Vcnt;A2A2F_;").
Proof.
  revert cnt. induction f as [|f IH]; intros cnt Hc; cbn; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt))%bool; [|lia]. pose proof (IH (cnt / 2) ltac:(Z.to_euclidean_division_equations; lia)). Z.to_euclidean_division_equations; lia.
Qed.
Lemma halve_while_even_clamp f cnt u : ltac2:(tb__ "0|1|
S1S5dZ0M0Vcnt;A2S5dVcnt;Z20A2A2S5dG0Vu;A2S0S54S9bVf;Vcnt;Vu;A3S9bVf;Vcnt;S66Vu;Z80A2A3A3F_;F_;").
Proof.
  revert cnt. induction f as [|f IH]; intros cnt Hc Hu; cbn; [reflexivity|].
  replace (Z.min u 128 <? 4 * cnt) with (u <? 4 * cnt).
  2:{ destruct (Z.ltb_spec u (4 * cnt)); [symmetry; apply Z.ltb_lt; lia | symmetry; apply Z.ltb_ge; lia]. }
  destruct (Z.even cnt && (u <? 4 * cnt))%bool; [|reflexivity]. apply IH; [Z.to_euclidean_division_equations; lia | exact Hu].
Qed.
Lemma small_cnt_clamp sc u : ltac2:(tb__ "0|1|
S1S5dZ0M0Vsc;A2S5fVsc;Z9A2A2S5dG0Vu;A2S0S54Sa4Vsc;Vu;A2Sa4Vsc;S66Vu;Z80A2A2A3F_;F_;").
Proof.
  intros Hsc Hu. unfold small_cnt. cbn zeta. set (row := nth (Z.to_nat sc) small_cnt_tab []).
  assert (TAB : forallb (fun r => forallb (fun x => (0 <=? x) && (x <=? 31)) r) small_cnt_tab = true) by reflexivity.
  assert (ROW : forall k, 0 <= znth k row <= 31).
  { intros k. unfold znth. destruct (nth_in_or_default (Z.to_nat k) row 0) as [Hin| ->]; [|lia].
    assert (Hr : In row small_cnt_tab \/ row = []) by (unfold row; destruct (nth_in_or_default (Z.to_nat sc) small_cnt_tab []) as [H|H]; auto).
    destruct Hr as [Hr|Hr]; [|rewrite Hr in Hin; destruct Hin].
    pose proof (proj1 (forallb_forall _ _) TAB row Hr) as T. pose proof (proj1 (forallb_forall _ _) T _ Hin) as T2.
    apply andb_prop in T2 as [T2 T3]. apply Z.leb_le in T2. apply Z.leb_le in T3. lia. }
  pose proof (ROW 0) as R0. pose proof (ROW 1) as R1.
  replace (Z.min u 128 <? 4 * znth 0 row) with (u <? 4 * znth 0 row).
  2:{ destruct (Z.ltb_spec u (4 * znth 0 row)); [symmetry; apply Z.ltb_lt; lia | symmetry; apply Z.ltb_ge; lia]. }
  replace (Z.min u 128 <? 4 * znth 1 row) with (u <? 4 * znth 1 row).
  2:{ destruct (Z.ltb_spec u (4 * znth 1 row)); [symmetry; apply Z.ltb_lt; lia | symmetry; apply Z.ltb_ge; lia]. }
  reflexivity.
Qed.
Lemma initial_cnt_clamp sc u : ltac2:(tb__ "0|1|
S1S5dZ0M0Vsc;A2S5fVsc;Z30A2A2S5dG0Vu;A2S0S54S97Vsc;Vu;A2S97Vsc;S66Vu;Z80A2A2A3F_;F_;").
Proof.
  intros Hsc Hu. unfold initial_cnt.
  assert (MED : 0 <= znth (Z.land sc 3) med_cnt_tab <= 32).
  { pose proof (forall_range_dec (fun x => (0 <=? znth (Z.land x 3) med_cnt_tab) && (znth (Z.land x 3) med_cnt_tab <=? 32)) 0 48 ltac:(vm_compute; reflexivity) sc ltac:(lia)) as T.
    cbn beta in T. apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2. lia. }
  destruct (Z.ltb_spec sc 9).
  - rewrite (small_cnt_clamp sc u) by lia. reflexivity.
  - rewrite (halve_while_even_clamp 8 _ u MED Hu). reflexivity.
Qed.
Definition nests (sc cnt : Z) : bool := ltac2:(tb__ "0|0|
S6aS5eS63S96Vsc;A1Vcnt;A2S93A2S64S91Z2A2A2").
Definition memZZ (p : Z * Z) (l : list (Z * Z)) : bool := ltac2:(tb__ "0|1|
Sb3S45S54S54A2M0G0S4dS67S51S54S54R1A3S51S54S54Vp;A3A2S67S4fS54S54R1A3S4fS54S54Vp;A3A2A2Lq;Vl;A3").
Lemma memZZ_In p l : ltac2:(tb__ "0|0|
S0S42S174Vp;Vl;A2S43A3Sb1S45S54S54A2Vp;Vl;A3F_;").
Proof.
  unfold memZZ. intros H. apply existsb_exists in H as (q & Hq & E). apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
  destruct p, q. cbn in E1, E2. subst. exact Hq.
Qed.
Lemma nvars_grid : ltac2:(tb__ "0|2|
S54S1S5dZ0M0R1A2S5fR1S5eG0S62U30A1A2A2A2S0S42Sb2S54S54S53S52S175R3S97R3R1A2M1A2A1S174S41S54S54R3G1A4S138A2A2Lu;S15dS4aS54S4aS5eG0S62R1A1A2Lk;S161U0U81A2A4A3S43A3F_;Fsc;").
Proof. apply (forall_range_dec (fun sc => forallb _ _)). vm_cast_no_check (@eq_refl bool true). Qed.
Theorem nvars_complete sc u : ltac2:(tb__ "0|2|
S1S5dZ0M0Vsc;A2S5fVsc;Z30A2A2S5dG0Vu;A2S5dS5eS63S96Vsc;A1S97Vsc;Vu;A2M1A2S93A2S64S91Z2A2A2Sb1S45S54S54A2S41S54S54Vsc;G1A4S138A3F_;F_;F_;").
Proof.
  intros Hsc Hu Hn. rewrite (initial_cnt_clamp sc u Hsc Hu) in Hn |- *.
  pose proof (proj1 (forallb_forall _ _) (nvars_grid sc ltac:(lia)) (Z.min u 128) ltac:(apply in_map_iff; exists (Z.to_nat (Z.min u 128)); split; [lia | apply in_seq; lia])) as T.
  cbn beta in T. apply Bool.orb_prop in T as [T|T]; [|exact (memZZ_In _ _ T)].
  exfalso. unfold nests in T. apply Bool.negb_true_iff in T. apply Z.leb_gt in T. lia.
Qed.

Section NTs.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1b5SccVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S5dS5eS63S7dVia;A1S75Via;A1A2S93A2S64S91Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S17bS167S83Via;A1A1S167S74Via;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S13fVia;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Let j : Z := ij ia.
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation NF0 := (@U.Mal_agrp__G17.Mal_agrp_IN.NF0 ia Hi Hnest Htier).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
Sd5Sd2S112SccS13dVrhoK;A1A2SceQ40A1S43L_;A2Sd4Sd1A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Notation "§1§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh) (at level 10, h__ global).
Local Abbreviation HiN := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.HiN).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).
Local Abbreviation ZF_NTg := (§1§ U.Mal_agrp__G17.Mal_agrp_IN.ZF_NTg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S1abVia;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S1a5SccSd1S165VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Theorem leaf_NPb : ltac2:(tb__ "0|1|
S19S27S0S42S173Vsc;S75Via;A1R2A3S43A3S16aS71S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0S13dVrhoK;A1A2R2A2VTR;VkB;S162SccS17aVKc;G0A2R4R3A4VQ;A3F_;F_;Frho';FLf;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Lf rho' CK Hag. unfold leafN_ok in CK.
  apply andb_prop in CK as [CK C345]. apply andb_prop in CK as [C1 C2]. cbn zeta in C345. apply andb_prop in C345 as [C34 C5]. apply andb_prop in C34 as [C3 C4].
  apply sv_eqb_sound in C5.
  exact (leaf_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV Lf _ rho' C1 C2 C3 C4 C5 Hag).
Qed.

Theorem leaves_NP (leaves : list leaf) : ltac2:(tb__ "0|1|
S0S42Sb2Se8Se8S173Vsc;S75Via;A1Se9R1A1A3Ll;Vleaves;A3S43A3Se8S27Sb1Se8R2Vleaves;A3S39S139S71S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0S13dVrhoK;A1A2R2A3VTR;VkB;S162SccS17aVKc;G0A2Se9R4A1R3A4VQ;A3F_;F_;Frho';FLf;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros ALL Lf rho' Hin Hab. apply (leaf_NPb (lf_state Lf) rho' (proj1 (forallb_forall _ _) ALL Lf Hin)).
  eapply agrees_below; [apply agrees_refl | exact Hab | cbv; discriminate].
Qed.

Lemma ZF_N3z : ltac2:(tb__ "0|1|
S160SfS135S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1A2S137Vj;S13eVamg;A1A2A3").
Proof using Herv Hervh Hi Hnest Htier NK.
  pose proof NF0 as (_ & _ & _ & _ & F5 & _).
  unfold factsN3. apply Forall_app. split; [exact (ZF_G iaN HiN)|]. apply Forall_app. split; [exact (ZF_M iaN HiN)|].
  apply ZF_NTg. rewrite (ze_lit iaN). apply Z.mod_small. lia.
Qed.

Theorem nt_entry tr ms : ltac2:(tb__ "0|2|
S20SccVrhoK;S1c4S41S44S17fA1S17dVtr;S17eVms;VmdK;A2A4M0A4VKc;Vtr;VmdK;A2S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A2S136S13eVamg;A1A1S71G1S13dVrhoK;A1A2G0A5F_;F_;").
Proof using Herv Hervh Hi Hnest Htier NK.
  intros Hsm HKc. split; [exact (smatch_SN3s ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh tr ms Hsm)|].
  cbn [w_tr w_cfg cfg_model]. split; [exact HKc | reflexivity].
Qed.

Theorem lit_N (S' : sstate) (d : list (sv * sv)) (nf : list sprop) (b : bool) w : ltac2:(tb__ "0|7|
S0S46S45S44S45SaSaA2A1M0S44SfA1M1A2M2A1S176S136Vb;A1M3VS';A2S47G2S41G0G1Vd;Vnf;A4A2A3S0S42S16VS';A1S43A3S178S71S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M4S13dVrhoK;A1A2M5Vd;A2S0S42Sb2SfSfSb3SfS1aR1A1S137Vj;Vb;A2A3Lp;Vnf;A3S43A3S0S42Vb;S13eVamg;A1A3S162SccS17aVKc;G4A2M6G3G5Vw;A5S162SccG6VS';G5Vw;A5F_;F_;F_;F_;F_;F_;").
Proof using Herv Hervh Hi Hnest Htier NK.
  intros Hsd Hwf Hd Hnf -> [Hsm HK]. split; [|exact HK].
  apply (smatch_restate segsU (rho2 iaN mWN) (SN3s bzN) S' w d nf Hsm Hwf Hsd Hd).
  apply (nf_of_big iaN mWN (rho2 iaN mWN) nf (factsN3 j bzN) (agrees_refl _) Hnf); [destruct bzN; reflexivity | destruct bzN; reflexivity | exact ZF_N3z].
Qed.
End NTs.

Theorem nt_wrap (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop) (RR : tr_rules segsU Kc RF GF TR) (kB : Z) (HkB : 0 <= kB)
  (ia : instA) (Hi : instA_ok ia) (Hnest : isize ia * icnt0 ia + UNIT <= PGSZ / 2) (Htier : (ContractI.tier (ij ia) < ContractI.tier (ia_sc ia))%nat) (Q : assn) : ltac2:(tb__ "0|1|
S27S183S188S8cS94S13fVia;R5R4R3R2R1A6S54S1S5dZ0R1A2S5fR1S60Z2Z20A2A2A2Sd5Sd2S112SccS13dR8A1A2SceQ40A1S43L_;A2Sd4Sd1A1U4R2A4VTR;VkB;S162SccS17aVKc;S13cVia;R9R8R7R6R5R3A7M0A2S136S13eR5A1A1S71G0S13dR9A1A2A4VQ;A3FHervh;FHerv;Ferv;FNK;Famg;Fg;FA2;FmdK;FrhoK;S27VTR;VkB;S163SccS1c5Via;VKc;A2S1c4R1A4VQ;A3FrhoK;F_;").
Proof.
  intros INNER rhoK. (apply (trr_inhP RR); [lia|]). intros [tr [ms mdK]] [Hsm HC]. cbn [w_tr w_cfg cfg_model J_ofP] in HC.
  destruct (nok_intro ia Kc rhoK tr mdK HC) as (HKc & A2 & g & amg & NK).
  destruct (errno_any (mWN rhoK)) as (erv & Herv & Hervh).
  exists (SymSoundR.SP segsU (K_ia Kc (iaN ia rhoK mdK A2 g amg erv)) (SN3s (bzN amg)) (rho2 (iaN ia rhoK mdK A2 g amg erv) (mWN rhoK))).
  split; [exact (nt_entry Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh tr ms Hsm HKc) | exact (INNER rhoK mdK A2 g amg NK erv Herv Hervh)].
Qed.
End Mal_agrp_NTs.

Module Mal_agrp_NT2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_A OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_Pv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G15.Mal_agrp_NCdefs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G16.Mal_agrp_NC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_IN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G17.Mal_agrp_NP OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G18.Mal_agrp_NTs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_rN2.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dN_4_25_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_4_25_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_25_L : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S4eA1S1e5A2S47G0S1c6A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_25_L)). Qed.
Lemma nfN_4_25_L : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z17S4eA2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1c6A3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_25_L : swf SN_4_25_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_25_L : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z4Z19Se9R1A1A3Ll;S1dbA3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_4_25_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_4_25_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_4_25_Z : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S43A1S1e6A2S47G0S1c7A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_4_25_Z)). Qed.
Lemma nfN_4_25_Z : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z17S43A2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1c7A3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_4_25_Z : swf SN_4_25_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_4_25_Z : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z4Z19Se9R1A1A3Ll;S1dcA3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_5_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_5_5_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_5_L : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S4eA1S1ebA2S47G0S1ccA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_5_L)). Qed.
Lemma nfN_5_5_L : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137ZfS4eA2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1ccA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_5_L : swf SN_5_5_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_5_L : ltac2:(tb__ "0|1|
S0S42Sb2Se8Se8S173Z5M0G0Se9R1A1A3Ll;S1e1A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_5_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_5_5_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_5_Z : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S43A1S1ecA2S47G0S1cdA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_5_Z)). Qed.
Lemma nfN_5_5_Z : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137ZfS43A2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1cdA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_5_Z : swf SN_5_5_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_5_Z : ltac2:(tb__ "0|1|
S0S42Sb2Se8Se8S173Z5M0G0Se9R1A1A3Ll;S1e2A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_10_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_5_10_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_10_L : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S4eA1S1e7A2S47G0S1c8A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_10_L)). Qed.
Lemma nfN_5_10_L : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z13S4eA2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1c8A3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_10_L : swf SN_5_10_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_10_L : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z5ZaSe9R1A1A3Ll;S1ddA3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_10_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_5_10_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_10_Z : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S43A1S1e8A2S47G0S1c9A2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_10_Z)). Qed.
Lemma nfN_5_10_Z : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z13S43A2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1c9A3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_10_Z : swf SN_5_10_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_10_Z : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z5ZaSe9R1A1A3Ll;S1deA3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_21_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_5_21_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_21_L : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S4eA1S1e9A2S47G0S1caA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_21_L)). Qed.
Lemma nfN_5_21_L : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z17S4eA2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1caA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_21_L : swf SN_5_21_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_21_L : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z5Z15Se9R1A1A3Ll;S1dfA3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_5_21_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_5_21_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_5_21_Z : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S43A1S1eaA2S47G0S1cbA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_5_21_Z)). Qed.
Lemma nfN_5_21_Z : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137Z17S43A2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1cbA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_5_21_Z : swf SN_5_21_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_5_21_Z : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z5Z15Se9R1A1A3Ll;S1e0A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_6_4_L : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s false) SN_6_4_L with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_4_L : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S4eA1S1edA2S47G0S1ceA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_4_L)). Qed.
Lemma nfN_6_4_L : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137ZfS4eA2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1ceA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_4_L : swf SN_6_4_L = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_4_L : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z6Z4Se9R1A1A3Ll;S1e3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition dN_6_4_Z : list (sv * sv) * list sprop := ltac:(let x := eval vm_compute in (match state_diff (SN3s true) SN_6_4_Z with Some d => d | None => ([], []) end) in exact x).
Lemma sdN_6_4_Z : ltac2:(tb__ "0|1|
S0S46S45S44S45SaSaA2A1S44SfA1A2M0A1S176S136S43A1S1eeA2S47G0S1cfA2A3").
Proof. vm_cast_no_check (@eq_refl (option (list (sv * sv) * list sprop)) (Some dN_6_4_Z)). Qed.
Lemma nfN_6_4_Z : ltac2:(tb__ "0|0|
S0S42Sb2SfSfSb3SfS1aR1A1S137ZfS43A2A3Lp;S4fS44S45SaSaA2A1S44SfA1S1cfA3A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma swfN_6_4_Z : swf SN_6_4_Z = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lvsN_6_4_Z : ltac2:(tb__ "0|0|
S0S42Sb2Se8Se8S173Z6Z4Se9R1A1A3Ll;S1e4A3S43A3"). Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section NT.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S1b5SccVKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Hypothesis HOg : Og.

Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Hypothesis HR0 : ia_R ia = None.
Hypothesis Hnest : ltac2:(tb__ "0|0|
S5dS5eS63S7dVia;A1S75Via;A1A2S93A2S64S91Z2A2A2").
Hypothesis Htier : ltac2:(tb__ "0|0|
S17bS167S83Via;A1A1S167S74Via;A1A1A2").
Variables (rhoK : valuation) (mdK : Model) (A2 : MA) (g : sptr) (amg : ameta).
Hypothesis NK : ltac2:(tb__ "0|0|
S13fVia;VrhoK;VmdK;VA2;Vg;Vamg;A6").
Let sc : Z := ia_sc ia.
Let s2 : astate := ma_s A2.
Local Abbreviation nidx := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx rhoK).
Let j : Z := ij ia.
Local Abbreviation nstrd := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd ia).
Local Abbreviation mWN := (@U.Mal_agrp__G17.Mal_agrp_IN.mWN rhoK).
Local Abbreviation nstrd_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nstrd_range ia Hi Hnest Htier).
Local Abbreviation nidx_range := (@U.Mal_agrp__G17.Mal_agrp_IN.nidx_range ia Hi Hnest Htier rhoK mdK A2 g amg NK).
Variable erv : Z.
Hypothesis Herv : 0 <= erv < 2 ^ 32.
Hypothesis Hervh : ltac2:(tb__ "0|0|
Sd5Sd2S112SccS13dVrhoK;A1A2SceQ40A1S43L_;A2Sd4Sd1A1U4Verv;A4").
Local Abbreviation iaN := (@U.Mal_agrp__G17.Mal_agrp_IN.iaN ia rhoK mdK A2 g amg erv).
Local Abbreviation HiN := (@U.Mal_agrp__G17.Mal_agrp_IN.HiN ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh).
Local Notation "§2§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv) (at level 10, h__ global).
Local Abbreviation zgm_range := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.zgm_range).
Local Notation "§3§ h__" := (h__ ia Hi Hnest Htier rhoK mdK A2 g amg erv Herv) (at level 10, h__ global).
Local Abbreviation zeN170 := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.zeN170).
Local Abbreviation zeN171 := (@U.Mal_agrp__G17.Mal_agrp_IN.zeN171 ia Hi Htier rhoK mdK A2 g amg erv Herv).
Local Abbreviation zeN178 := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.zeN178).
Local Abbreviation zeN181 := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.zeN181).
Local Abbreviation zp := (@U.Mal_agrp__G17.Mal_agrp_IN.zp ia rhoK A2 amg).
Local Abbreviation ze_pslot := (§2§ U.Mal_agrp__G17.Mal_agrp_IN.ze_pslot).
Local Abbreviation ze_cj := (§3§ U.Mal_agrp__G17.Mal_agrp_IN.ze_cj).
Local Abbreviation bzN := (@U.Mal_agrp__G17.Mal_agrp_IN.bzN amg).

Variables (X : list sptr) (U : Z -> Z) (A : MA) (rho0 : valuation).
Hypothesis PV : ltac2:(tb__ "0|0|
S1abVia;VX;VU;VA;Vrho0;A5").
Let Q : assn := ltac2:(tb__ "0|0|
S1a5SccSd1S165VNf;VOg;VX;VU;VA;VKc;Vrho0;Aa").

Lemma zsN170 : ltac2:(tb__ "0|1|
S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1SdPaaA1A3Vj;A3"). Proof using Herv Hi Hnest Htier. exact zeN170. Qed.
Lemma zsN171 : ltac2:(tb__ "0|1|
S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1SdPabA1A3S75Via;A1A3"). Proof using Herv Hi Htier. exact zeN171. Qed.
Lemma zsN178 : ltac2:(tb__ "0|1|
S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1SdPb2A1A3S142VrhoK;A1A3"). Proof using Herv Hi Hnest Htier NK. exact zeN178. Qed.
Lemma zsN181 : ltac2:(tb__ "0|1|
S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1SdPb5A1A3S140Via;A1A3"). Proof using Herv Hi Hnest Htier. exact zeN181. Qed.
Lemma zsN_cj k : ltac2:(tb__ "0|1|
S1S5dZ0Vk;A2S5fVk;S60Z2Z20A2A2A2S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1ScS56ScS57SdPaaA1SbZ3A1A3SbVk;A1A3A3S5eS63Z8Vj;A2Vk;A2A3F_;"). Proof using Herv Hi Hnest Htier. exact (ze_cj k). Qed.
Lemma zsN_pslot : ltac2:(tb__ "0|1|
S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1ScS56ScS56SdPb4A1S11S58SdPb5A1SdPb2A1A3A3SbZ10A1A3A3S141Via;VrhoK;VA2;Vamg;A4A3"). Proof using Herv Hi Hnest Htier NK. exact ze_pslot. Qed.
Lemma zsN_pslotZ z : ltac2:(tb__ "0|1|
S0S54Vz;S140Via;A1A3S0S54S134S70S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A1S6fG0A1ScS56ScS56SdPb4A1S11S58SbVz;A1SdPb2A1A3A3SbZ10A1A3A3S141Via;VrhoK;VA2;Vamg;A4A3F_;").
Proof using Herv Hi Hnest Htier NK. intros ->. exact (ze_pslotZ ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv). Qed.

Local Ltac sem2 HagX := lazymatch goal with |- eval ?r ?e1 = eval ?r ?e2 =>
  rewrite (EVw _ _ r e1 HagX) by reflexivity; rewrite (EVw _ _ r e2 HagX) by reflexivity; f_equal end.
Local Ltac finN Esc Ecnt Ej := unfold isize, j, sc; cbn [ia_sc ia_req U.Mal_agrp__G17.Mal_agrp_IN.iaN]; unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd; rewrite ?Esc, ?Ecnt, ?Ej; try reflexivity; Z.to_euclidean_division_equations; lia.
Local Ltac pairsN HagR Esc Ecnt Ej :=
  unfold diffs_ok; repeat (apply Forall_cons; [cbn [fst snd];
    first [ solve_scratch
          | sem2 HagR; rewrite ?zsN_pslot; try (erewrite zsN_pslotZ by (unfold U.Mal_agrp__G17.Mal_agrp_IN.nstrd, j; rewrite Ej; reflexivity));
            zsimp constr:(iaN) constr:(HiN); rewrite ?zsN170, ?zsN171, ?zsN178, ?zsN181; rewrite ?zsN_cj by lia;
            rewrite ?(ze_alu iaN), ?zsN181, ?ze_lit; cbn [zalu]; finN Esc Ecnt Ej ] |]);
  apply Forall_nil.

Theorem nt_4_25 : ltac2:(tb__ "0|1|
S0S54S74Via;A1Z4A3S0S54S75Via;A1Z19A3VTR;VkB;S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S136S13eVamg;A1A1S71G0S13dVrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_25_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_25_Z (fst dN_4_25_Z) (snd dN_4_25_Z) true w0 sdN_4_25_Z swfN_4_25_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_4_25_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_25_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_25_Z LN_4_25_Z (rho2 iaN mWN) Q HkB (eq_trans runN_4_25_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_25_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_25_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_4_25_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_4_25_L (fst dN_4_25_L) (snd dN_4_25_L) false w0 sdN_4_25_L swfN_4_25_L _ _ (eq_sym EB) _).
      - cbn [fst dN_4_25_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_4_25_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_4_25_L LN_4_25_L (rho2 iaN mWN) Q HkB (eq_trans runN_4_25_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_4_25_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_4_25_L | exact Hin | exact Hab].
Qed.

Theorem nt_5_5 : ltac2:(tb__ "0|2|
S0S54S74Via;A1Z5M0A3S0S54S75Via;A1G0A3VTR;VkB;S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M1A2S136S13eVamg;A1A1S71G1S13dVrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_5_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_5_Z (fst dN_5_5_Z) (snd dN_5_5_Z) true w0 sdN_5_5_Z swfN_5_5_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_5_5_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_5_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_5_Z LN_5_5_Z (rho2 iaN mWN) Q HkB (eq_trans runN_5_5_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_5_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_5_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_5_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_5_L (fst dN_5_5_L) (snd dN_5_5_L) false w0 sdN_5_5_L swfN_5_5_L _ _ (eq_sym EB) _).
      - cbn [fst dN_5_5_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_5_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_5_L LN_5_5_L (rho2 iaN mWN) Q HkB (eq_trans runN_5_5_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_5_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_5_L | exact Hin | exact Hab].
Qed.

Theorem nt_5_10 : ltac2:(tb__ "0|1|
S0S54S74Via;A1Z5A3S0S54S75Via;A1ZaA3VTR;VkB;S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S136S13eVamg;A1A1S71G0S13dVrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 19) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_10_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_10_Z (fst dN_5_10_Z) (snd dN_5_10_Z) true w0 sdN_5_10_Z swfN_5_10_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_5_10_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_10_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_10_Z LN_5_10_Z (rho2 iaN mWN) Q HkB (eq_trans runN_5_10_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_10_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_10_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_10_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_10_L (fst dN_5_10_L) (snd dN_5_10_L) false w0 sdN_5_10_L swfN_5_10_L _ _ (eq_sym EB) _).
      - cbn [fst dN_5_10_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_10_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_10_L LN_5_10_L (rho2 iaN mWN) Q HkB (eq_trans runN_5_10_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_10_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_10_L | exact Hin | exact Hab].
Qed.

Theorem nt_5_21 : ltac2:(tb__ "0|1|
S0S54S74Via;A1Z5A3S0S54S75Via;A1Z15A3VTR;VkB;S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S136S13eVamg;A1A1S71G0S13dVrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 23) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_21_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_21_Z (fst dN_5_21_Z) (snd dN_5_21_Z) true w0 sdN_5_21_Z swfN_5_21_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_5_21_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_21_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_21_Z LN_5_21_Z (rho2 iaN mWN) Q HkB (eq_trans runN_5_21_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_21_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_21_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_5_21_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_5_21_L (fst dN_5_21_L) (snd dN_5_21_L) false w0 sdN_5_21_L swfN_5_21_L _ _ (eq_sym EB) _).
      - cbn [fst dN_5_21_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_5_21_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_5_21_L LN_5_21_L (rho2 iaN mWN) Q HkB (eq_trans runN_5_21_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_5_21_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_5_21_L | exact Hin | exact Hab].
Qed.

Theorem nt_6_4 : ltac2:(tb__ "0|1|
S0S54S74Via;A1Z6A3S0S54S75Via;A1Z4A3VTR;VkB;S162SccS17aVKc;S13cVia;VrhoK;VmdK;VA2;Vg;Vamg;Verv;A7M0A2S136S13eVamg;A1A1S71G0S13dVrhoK;A1A2A4VQ;A3F_;F_;").
Proof using HOg Herv Hervh Hi HkB Hnest Htier NK Nf PV RR.
  intros Esc Ecnt.
  assert (Ej : ij ia = 15) by (rewrite <- (nj_eq ia Hi Hnest Htier erv Herv); rewrite Esc, Ecnt; reflexivity).
  assert (HagR : agrees (rhoW iaN mWN) (rho2 iaN mWN)) by apply agrees_refl.
  pose proof (iok_sc ia Hi) as SC. pose proof nstrd_range as SR. pose proof nidx_range as (IR & _). pose proof zgm_range as ZG.
  destruct bzN eqn:EB.
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_4_Z (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_4_Z (fst dN_6_4_Z) (snd dN_6_4_Z) true w0 sdN_6_4_Z swfN_6_4_Z _ _ (eq_sym EB) _).
      - cbn [fst dN_6_4_Z]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_4_Z.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_4_Z LN_6_4_Z (rho2 iaN mWN) Q HkB (eq_trans runN_6_4_Z eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_4_Z); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_4_Z | exact Hin | exact Hab].
  - apply (trr_pre RR (SymSoundR.SP segsU (K_ia Kc iaN) SN_6_4_L (rho2 iaN mWN))).
    { intros w0 HSP. refine (lit_N Kc ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh SN_6_4_L (fst dN_6_4_L) (snd dN_6_4_L) false w0 sdN_6_4_L swfN_6_4_L _ _ (eq_sym EB) _).
      - cbn [fst dN_6_4_L]. pairsN HagR Esc Ecnt Ej.
      - unfold j. rewrite Ej. exact nfN_6_4_L.
      - exact HSP. }
    apply ((trr_run RR) kB 500%nat CUTS_N (K_ia Kc iaN) SN_6_4_L LN_6_4_L (rho2 iaN mWN) Q HkB (eq_trans runN_6_4_L eq_refl) eq_refl (K_ia_impl Kc iaN)).
    intros Lf rho' Hin Hab. apply (leaves_NP Kc RF GF TR RR kB HkB Nf Og HOg ia Hi Hnest Htier rhoK mdK A2 g amg NK erv Herv Hervh X U A rho0 PV LN_6_4_L); [unfold sc; rewrite Esc, Ecnt; exact lvsN_6_4_L | exact Hin | exact Hab].
Qed.
End NT.
End Mal_agrp_NT2.
