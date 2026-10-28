(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "iff"; "True"; "False"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "Zpos"; "N"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "region"; "am_sc"; "astate"; "MFree"; "am_last"; "am_next"; "st_free_meta_head"; "ameta"; "am_freed"; "am_maplen"; "am_prev"; "RkMap"; "am_mem"; "bit"; "ones"; "page_round"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_regions"; "usage_of"; "IRet"; "MUsed"; "itree"; "nontrivial_free"; "sptr_eqb"; "padd"; "size_classes"; "st_brk"; "st_init_done"; "st_usage"; "znth"; "am_avail"; "am_set_links"; "brkst"; "zset"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "eqb"; "modulo"; "of_nat"; "opp"; "to_nat"; "mul"; "leb"; "ltb"; "div"; "testbit"; "@Corelib.Init.Datatypes"; "cons"; "option"; "bool"; "true"; "Some"; "nat"; "pair"; "list"; "prod"; "andb"; "false"; "None"; "nil"; "app"; "negb"; "fst"; "snd"; "orb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "pre_fregs"; "NF"; "callee_saved"; "pre_reg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "rw"; "SLit"; "reg_sv"; "rm"; "sprop"; "SVar"; "valuation"; "sv_eqb"; "obj_holds"; "eval"; "smatch"; "SPBranch"; "cell"; "holds"; "ss_lenient"; "ss_objs"; "obj_range"; "ss_fcsr"; "ss_fregs"; "ss_next"; "sfcsr"; "DUnknown"; "SAlu"; "ob_cells"; "ss_pc"; "ss_resv"; "FcsrFrm0"; "mkObj"; "sstate"; "swf"; "SPNot"; "mkSS"; "ob_base"; "ob_dflt"; "soff"; "c_off"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_regs"; "SExt"; "SPUle"; "mkVal"; "ranges_disjoint"; "SAluW"; "SLBytes"; "SMd"; "c_val"; "c_width"; "enc_bytes"; "freg_sv"; "obj_hi_of"; "obj_lo_of"; "obj_wf"; "odefault"; "outside_all"; "pairwise_disjoint"; "regs_match"; "rl"; "ro_addr"; "rom_ok"; "sprop_eqb"; "@Stdlib.Lists.List"; "In"; "forallb"; "tl"; "existsb"; "hd"; "nth_error"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "od"; "dhi"; "dlo"; "obj_of"; "OD_meta"; "sv_sem"; "OD_sct"; "ds_checkb"; "KG"; "DS"; "KN"; "OD_act"; "OD_bptr"; "OD_parea"; "OD_pbase"; "OD_pmeta"; "OD_secret"; "OD_shdr"; "dcond"; "drom"; "KP"; "OD_usage"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9.V.PhaseF"; "odF"; "s5"; "dloF"; "dhiF"; "obj_ofF"; "DSF"; "FD_free"; "fkey4"; "dcellsF"; "K4g"; "dromF"; "K4m"; "flo4"; "od_okF"; "rngDF"; "FD_fmh"; "FD_guard"; "HzlN"; "HzrN"; "ds_checkbF"; "od_okF_at"; "regs_okbF"; "K4t"; "cellsDF"; "cellsInDF"; "dunkDF"; "fbase4"; "fcond4"; "fptr4"; "leaf_okbF"; "range64DF"; "semDF"; "EmN"; "dsF_of"; "dszF"; "oStkF4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "C_U"; "byteview_of"; "topL"; "holds"; "mc_chk_guard"; "vm_ok"; "size_classes_bytes"; "statics_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "loc"; "MT"; "loc_addr"; "keys"; "active_hd";
"usedX"; "image"; "Inv"; "mc_loc"; "mc_w"; "alloc_owned"; "region_of"; "LCtx"; "cell_holds"; "ly_reg"; "CTX_usage"; "footprint"; "LMem"; "le_byte"; "user_blocks"; "CTX_SIZE"; "CTX_free_meta_head"; "MCell"; "ly_ctx"; "memb"; "meta_slot_cells"; "optr"; "zseq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zsupported"; "toS"; "zholds"; "psupported"; "zl_of"; "zle"; "zr_of"; "zsublist"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "lf_state"; "stop_reason"; "lf_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8.V.PhaseF"; "rhoN"; "zrN"; "fmQ4"; "zlN"; "Sh4"; "O_graw"; "ftQ4"; "fmL4"; "fshape4"; "o_stk_top"; "rwN"; "zF4"; "zFn4"; "zFp4"; "zTTn4"; "zTTp4"; "N4"; "ftL4"; "stk_vars"; "rw4v"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "m_vmmaps"; "VmMaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8"; "rhoN"; "zlN"; "zrN"; "fshape4"; "N4"; "fmQ4"; "o_stk_top"; "ftQ4"; "zFp4"; "O_graw"; "Sh4"; "fmL4"; "ftL4"; "zF4"; "zFn4"; "zTTn4"; "zTTp4"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA"; "ma_owned"; "ma_s"; "ma_L"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7"; "s3v"; "od_chgC"; "s3r"; "NRELW"; "dsX"; "stk"; "amPar'"; "m'c"; "oStkF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z"; "D0"; "sp0"; "od_disj"; "od_pairwise"; "zfree"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NTE_U"; "magree"; "Posts_nt"; "in_zslots"; "Pre_nt"; "L_nt"; "nt_stack"; "xzomb"; "NT_D"; "J_nt_pre"; "zslotb"; "zv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "zG"; "sc"; "zl1"; "zr1"; "gPar"; "amPar"; "iPar"; "nQ"; "optrA"; "zM"; "mask"; "pQ"; "rho1"; "flinks0"; "zNn"; "apQ"; "rl1"; "zPp"; "zU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "in_vars"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@Corelib.Init.Peano"; "le"; "lt"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "state_diff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "o_stk_saved"; "S_t2n_of"; "CUTS0"; "O_guard_"; "S_b_of"; "PVNV"; "pm_facts"; "o_gmeta"; "L_t2n0"; "L_t2n1"; "L_t2n2"; "NXA"; "facts_t2"; "nt_maplen"; "objs_b"; "regs_t2n"; "F_all"; "F_base"; "F_freeable"; "F_sc48"; "lfs"; "objs_t2n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "reprO"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db"; "od_ok_at"; "od_ok"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "leb"; "add"; "eqb"; "of_nat"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "tier"; "reach_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "objs_matchb"; "m'"; "touched"; "remove_nth"; "EVu"; "cell_from_od";
"cell_from_od_zero"; "keys_distinct"; "m'_in"; "m'_out"; "scratch_of"; "touched_dec"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9.V.PhaseF.ReabF"; "m''"; "m5v"; "stk4"; "oStkF4"; "HdsF5"; "touchedV5"; "meets5"; "s5r"; "HdsC_sub5"; "NRELF"; "meetsR5"; "rho'"; "rw'"; "stkb4"; "od_chgF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "obj_vars_all"; "sv_vars_all"; "sprop_vars_all"; "agree_vals"; "state_vars_all"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_GE"; "ALU_SLL"; "ALU_ADD"; "ALU_AND"; "ALU_SRL"; "M_MUL"; "aluop"; "mulop"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal"; "zomb_rel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib"; "O_freeK"; "O_fmh"; "free_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3"; "gl_nv"; "gl_pv"; "riding"; "svl_eqb"; "pvnv_okb"; "scratch_pairb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11.V"; "b_leaf_okb"; "dsB_live"; "ds_newN"; "e_pidx"; "pbN"; "bP"; "b_run_okb"; "link_okbN"; "regs_b_okb"; "ds_liveN"; "e_psc"; "canonN"; "movedN"; "prefix_leaf_okbN"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "ms_regs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "canary_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules"; "TRrules"; "tr_conseq"; "tr_disj"; "tr_pointwise"; "tr_pure"; "tr_refl"; "tr_run"; "tr_seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "fneed"; "nf_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4"; "l1_locs"; "E_usage"; "an2"; "E_avN"; "E_frN"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10"; "J_nt_preT"; "@Corelib.Init.Specif"; "sumbool"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "odefault_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "alloc_static"; "errno_range"; "rd_of"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "V_DEPTH"; "mem_kept_owned"; "top_high"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "fgm_s1"; "fq_post"; "shape_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V11"; "cells_eqb"; "obj_eqb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9"; "L_t2n"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.Riscv.Sem"; "reg_get"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "deltaU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_activate"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c"; "reg_of_var"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_V8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S196Se1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;S13fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SefVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PcA2A2Se0VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation Hres := (@U.Mal_nt__G1.Mal_nt_I.Hres s L X U g am i vm rd0 wok0 HMI Hu).
Local Abbreviation R_all := (@U.Mal_nt__G1.Mal_nt_I.R_all s L X U g am i gd vm rd0 wok0 HMI Hu Hgd).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation flinks0 := (@U.Mal_nt__G1.Mal_nt_I.flinks0).
Local Notation "§1§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§1§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§1§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§1§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation rl1 := (@U.Mal_nt__G1.Mal_nt_I.rl1 rho).
Local Abbreviation rho1 := (@U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd rd0).
Local Abbreviation rw1_low := (@U.Mal_nt__G1.Mal_nt_I.rw1_low s L g am i rho gd rd0 Hgd).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S34Z1000Sa2Q40S5cVrho;PaA2A2M0A2S0S8S3aG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S34S10aZ40Sa2Q40S5cVrho;PfA2A2A2M0N60A2S34S3cS37Z2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;Vrd0;S106S55VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sa0Q40A1S45F_;Vwok0;S107S55VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1Z60A2A2S0S44Sa0Q8A1M0A1VmV;Sa1Q40S35Z108ecR2A2A2A1S4eG0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Se4Se2Vrd0;Sa0Q40A1S46L_;A2Se5Se1A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Se2S106S55VmV;A2S107S55VmV;A2A2").
Local Abbreviation rv_byte := (@U.Mal_nt__G1.Mal_nt_Ib.rv_byte mV).
Local Abbreviation guard_wseg := (@U.Mal_nt__G1.Mal_nt_Ib.guard_wseg).
Local Abbreviation cellZ_optr := (@U.Mal_nt__G1.Mal_nt_Ib.cellZ_optr L).
Local Abbreviation O_fmh := (@U.Mal_nt__G1.Mal_nt_Ib.O_fmh).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation O_freeK := (@U.Mal_nt__G1.Mal_nt_Ib.O_freeK).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S152VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation g_zone := (@U.Mal_nt__G2.Mal_nt_Z.g_zone s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd).
Local Abbreviation HZ_at := (@U.Mal_nt__G2.Mal_nt_Z.HZ_at L X rho gd Hgd mV mW HZ).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S34Se3VL;A1S35S14dVrho;A1S14cVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S4aS12aA1S12bOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1e9S55VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
SddVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1eeS55VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
SddSddSddVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1f0S55VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSddSddR3VTR;R3R2A2F_;VTR;SdeS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1edS55VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
SddSddSddSddSdeR4R1A1M0R6R2A1F_;Fw;SdeG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1eaS55VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
SddSddSdeR3R1A1VTR;SdeS0SdeR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1ecS55VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
SddSddSddVTR;R3R1A2VTR;R3R2A2VTR;SdeS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1ebS55VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1cbVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sf1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrho;PdA2Sa1G0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis HKc : ltac2:(tb__ "0|1|
S4aS12aA1M0S12bVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S12bR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S66S55Vrho;S155S151A1S49S4aS12aA1S173Vtr;S174Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S8S34Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S4bS44ScA1M0G0A2S49G0G0S18Vam;A1S13Vam;A1A4S49G0G0S4eScA1M1G1A4A3A1S2S0G0SeeVs;SfVam;A1A2S47ScVg;A2A3A1S2S0S8S16Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S8S35S167Vam;A1S1bVi;A1A2S1cS12Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml0 : am_maplen am = 0.
Local Abbreviation s3v := (§1§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Section PhaseF.
Variables (rhoL : valuation) (msL : machine_state) (t4 : astate) (mv4 : word -> option byte) (rbase rlen : Z).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S66S55VrhoL;S156S151A1S49S4aS12aA1S173Vtr;S174VmsL;Vmd;A2A4A4").
Hypothesis HMI4 : ltac2:(tb__ "0|0|
S196Se1S43ScVg;VX;A3S4eS4bScS8A2A1VU;S13fVt4;VL;A2S106S55Vmv4;A2S107S55Vmv4;A2Vvm;A8").
Hypothesis HZ4 : ltac2:(tb__ "0|0|
S152VL;S43ScVg;VX;A3Vmv4;S5fVrhoL;A1A4").
Hypothesis HXz4 : ltac2:(tb__ "0|0|
S158S43ScVg;VX;A3Vt4;A2").
Hypothesis Cr4 : ltac2:(tb__ "0|0|
S1f1S43ScVg;VX;A3S143Vs;Vg;Vam;A3Vt4;A3").
Hypothesis UB4 : ub_same s3v t4.
Hypothesis Hreach4 : reach_ok t4.
Hypothesis Hres : ltac2:(tb__ "0|1|
S4S1S0S8Vrlen;Z0M0A3S0S8Vrbase;G0A3A2S1S36G0Vrlen;A2S3S48S48S3SeSeS1S0S44SeA1Sf5Vt4;R2A2S47SeR1A2A3S1S0S22S1fR1A1S19A3S1S0S45S21R1A1S46A3S1S0S8S20R1A1S1dVrlen;A1A3S1S0S8Sf8VL;R2A2Vrbase;A3ScS15SefS43ScVg;VX;A3Vt4;R2R1A4S36G0S17R2A1A2S2S0S48S1eS1aR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2Lrg;A2Lk;A2A2A2").
Hypothesis Hres64 : ltac2:(tb__ "0|2|
S1S1S34Z0M0Vrbase;A2S36Vrbase;S37Z2Z40A2M1A2A2S1S34G0Vrlen;A2S36Vrlen;G1A2A2A2").

Hypothesis HrL10 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;PaA2Sa1G0S38S14dVrho;A1Z60A2A2A3").
Hypothesis HrL15 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrhoL;PfA2A2S3aS35S14cVrho;A1Z60A2S37Z2Z40A2A2A3").
Hypothesis HrL11 : rw rhoL 11%positive = Z_to_bv 64 0x20ad4.
Hypothesis HrL28 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P1cA2Sa1G0S166VL;Vam;A2A2A3").
Hypothesis HrL29 : rw rhoL 29%positive = Z_to_bv 64 0x5a338.
Hypothesis HrL38 : rw rhoL 38%positive = Z_to_bv 64 0x5a3d0.
Hypothesis HrL39 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P27A2Sa1G0S15dVL;Vg;A2A2A3").
Hypothesis HrLlow : ltac2:(tb__ "0|0|
S9S9aS9R1S43S9P17S43S9P18S43S9P28S43S9P29S43S9P2aS43S9P2bS43S9P2cS43S9P2dS43S9P2eS43S9P2fS4fS9A1A3A3A3A3A3A3A3A3A3A3A3S0Sa0Q40A1S5cVrhoL;R2A2S5cVrho;R2A2A3F_;Fj;").
Hypothesis HrLf : ltac2:(tb__ "0|0|
S9S1S199P3cR1A2S19aR1P5cA2A2S0Sa0Q40A1S5cVrhoL;R2A2S5cVrho;R2A2A3F_;Fj;").
Hypothesis HrL110 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P6eA2Sa1G0Vrbase;A2A3").
Hypothesis HrL111 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P6fA2Sa1G0Vrlen;A2A3").

Definition o_stk_top : sobj := ltac2:(tb__ "0|0|
S77S61PaA1S5dN60A1S5dZ0A1S73S17eA1S71A5").
Hypothesis Hstk : ltac2:(tb__ "0|0|
S64S55VrhoW;S17cVmsL;S5fVrhoL;A1A2S11fA4").
Hypothesis Hkept4 : ltac2:(tb__ "0|2|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2S2S140Se1S13fVs;VL;A2R2A3A1S2S140Se1S13fVt4;VL;A2R3A3A1S2S1feSe1R4A2A1S2S1fdSe1R5A2A1S2S1S34S38S14dVrho;A1M0Z60A2R6A2S36R6G0A2A2A1S0S44Sa0Q8A1A1S5fVrhoL;Sa1Q40R7A2M1A2S5fVrho;G1A2A3F_;F_;F_;F_;F_;F_;Fa;").
Hypothesis Hcanary4 : ltac2:(tb__ "0|0|
S1e8S55Se1S5fVrho;A1S5fVrhoL;A1A4").
Hypothesis HK4 : K tr md.

Variables (t4r : astate) (r4 : option (nat * Z)).
Hypothesis Hz4 : ltac2:(tb__ "0|0|
S1cbS43ScVg;VX;A3Vt4r;Vt4;A3").
Hypothesis HI4r : ltac2:(tb__ "0|0|
Sf1S43ScVg;VX;A3S4eS4bScS8A2A1VU;Vt4r;A4").
Hypothesis Hres_r : ltac2:(tb__ "0|4|
S4S1S0S44S4bS48S8A2M0A1M1Vr4;S4eG0A1A3S1S0S8Vrlen;Z0M2A3S0S8Vrbase;G2A3A2A2S3S48S48S3SeSeS1S0G1Vr4;S47G0S49S48S8R2S20R1A1M3A4A2A3S1S36G2Vrlen;A2S1S0S44SeA1Sf5Vt4r;R2A2S47SeR1A2A3S1S0S22S1fR1A1S19A3S1S0S45S21R1A1S46A3S1S0S8G3S1dVrlen;A1A3S1S0S8Sf8VL;R2A2Vrbase;A3ScS15SefS43ScVg;VX;A3Vt4r;R2R1A4S36G2S17R2A1A2S2S0S48S1eS1aR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2A2A2Lrg;A2Lk;A2A2").
Hypothesis Heq4 : ltac2:(tb__ "0|2|
S48S17aS1f2SfS162Vs;Vg;Vam;A3A1A1R1A2S0S27S10S4bS44S4bS48S8A2A1M0S10A2M1A2S28R2S161Vs;Vg;Vam;A3S163Vs;Vg;Vam;A3S145Vs;Vg;Vam;Vsr;A4A4S25S10G1S49G0S10Vr4;Vt4r;A4A3A3F_;FF;").
Hypothesis Hxk4 : ltac2:(tb__ "0|0|
ScS9aScR1S43ScVg;VX;A3A3S0S44SdA1SebVt4r;R2A2SebS145Vs;Vg;Vam;Vsr;A4R2A2A3F_;Fx;").

Lemma HI4 : ltac2:(tb__ "0|0|
Sf1S43ScVg;VX;A3S4eS4bScS8A2A1VU;Vt4;A4"). Proof using HMI4. exact (mig_I HMI4). Qed.
Lemma HXr4 : ltac2:(tb__ "0|0|
S213S43ScVg;VX;A3Vt4;A2"). Proof using HXz4. exact (xzomb_xraw _ _ HXz4). Qed.
Lemma HL4 : layout_ok L t4. Proof using HMI4. exact (mig_layout HMI4). Qed.
Lemma HV4 : ltac2:(tb__ "0|0|
Se6VL;Vt4;Vvm;A3"). Proof using HMI4. exact (mig_vm HMI4). Qed.
Lemma HLG4 : ledger_ok C_U vm. Proof using HMI4. exact (mig_ledger HMI4). Qed.
Lemma Hctx4 : ly_ctx L = 0x5a3d0. Proof using HMI4. exact (mig_ctx HMI4). Qed.
Lemma HreprO4 : ltac2:(tb__ "0|0|
S195VL;Vt4;Se2S106S55Vmv4;A2S107S55Vmv4;A2A2A3"). Proof using HMI4. exact (mig_reprO HMI4). Qed.
Lemma Hstat4 : ltac2:(tb__ "0|1|
Se8Se1Se2S106S55Vmv4;A2M0Sa0Q40A1S46L_;A2Se2G0S107S55Vmv4;A2A2A3").
Proof using HMI4. drop_sp. exact (mig_statics HMI4). Qed.
Lemma ND4 : List.NoDup (keys t4). Proof using HMI4. exact (proj1 (inv_keys HI4)). Qed.
Lemma Mg4 : ltac2:(tb__ "0|1|
S0S44SdA1SebVt4;Vg;A2S47SdS11S4eScA1M0G0A2A2A3"). Proof using HXz4. apply HXz4. left. reflexivity. Qed.
Lemma Kg4 : In g (keys t4). Proof using HXz4. eapply MT_Some_In_keys. exact Mg4. Qed.
Lemma key_range4 q : ltac2:(tb__ "0|1|
S9aScVq;SedVt4;A1A3S1S34Z1000Se0VL;Vq;A2M0A2S34S35G0Z28A2Se3VL;A1A2A2F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp. intros Hq. pose proof (key_range (g :: X) None U t4 L HI4 HL4 C_U vm q Hq HV4 HLG4) as (K1 & K2 & _). unfold META_SIZE, PGSZ in *. lia. Qed.
Lemma keys_apart4 q q' : ltac2:(tb__ "0|4|
S9aScVq;SedVt4;A1M0A3S9aScVq';G0A3S2S0ScVq;Vq';A3A1S4S34S35Se0VL;Vq;A2M1Z28M2A2Se0VL;Vq';A2M3A2S34S35G3G2A2G1A2A2F_;F_;F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp. intros Hq Hq' Hne. pose proof (meta_ranges_disjoint (g :: X) None U t4 L HI4 HL4 q q' Hq Hq' Hne). unfold SymState.ranges_disjoint, META_SIZE in *. cbn [fst snd] in *. lia. Qed.
Lemma key_zone4 q : ltac2:(tb__ "0|3|
S9aScVq;SedVt4;A1A3S1S34Z1000Se0VL;Vq;A2M0A2S1S34S35G0Z28A2M1Se3VL;A1A2S1S4S34G1Z10000A2S34Z5b000G0A2A2S4S34S35Z5a3d0M2Z3a0A2G0A2S34G1G2A2A2A2A2A2F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp.
  intros Hq. pose proof (key_range (g :: X) None U t4 L HI4 HL4 C_U vm q Hq HV4 HLG4) as (K1 & K2 & K3 & K4).
  rewrite Hctx4 in K4. cbn [mc_img_lo mc_img_hi C_U] in K3. unfold META_SIZE, PGSZ, CTX_SIZE in *. lia.
Qed.

Definition fmQ4 : sptr := ltac2:(tb__ "0|0|
S44ScA1ScLx;S14Vt4;A1ScR1Lf;Vg;X44x2").
Definition fmL4 : option sptr * option sptr := ltac2:(tb__ "0|0|
S16aSebVt4;S118A2A1").
Definition ftQ4 : sptr := ltac2:(tb__ "0|1|
S44ScA1M0ScLx;S52G0G0S11dA3ScR1Lt;S118X44x2").
Definition ftL4 : option sptr * option sptr := ltac2:(tb__ "0|0|
S16aSebVt4;S11cA2A1").
Definition zF4 : Z := ltac2:(tb__ "0|0|
S165VL;S14Vt4;A1A2").
Definition zFp4 : Z := optrA L (fst fmL4).
Definition zFn4 : Z := optrA L (snd fmL4).
Definition zTTp4 : Z := optrA L (fst ftL4).
Definition zTTn4 : Z := optrA L (snd ftL4).
Definition fshape4 : nat := ltac2:(tb__ "0|0|
S44ScA1S48Lx;S14Vt4;A1ScS45S48L_;S29S11cS118A2U1U2X45x2Ls0;U0X44x2").

Lemma ring4_cases : ltac2:(tb__ "0|b|
S4S1S0S44ScA1M0S14Vt4;A1M1S4eScA1M2A3S1S0ScS118Vg;A3S1S0S4bG0G0A2M3S11dS49G0G0G2G2A4M4A3S1S0ScS11cVg;A3S0G3S127G4A3A2A2A2A2S3ScScS3ScScS3ScScS3ScScS3ScScS1S0G0G1S47ScR5A2A3S1S0ScS118R5A3S1S0S44SdA1M5SebVt4;R5A2S47SdS11S47ScR4A2M6S47ScR3A2M7A2A2A3S1S0G3S11dS49G0G0G6G7A4A3S1S0ScS11cR4A3S1S0G5SebVt4;R4A2S47SdS11S47ScR2A2M8S47ScR1A2M9A2A2A3S1S0G3S127S49G0G0G8G9A4A3S1S2S0ScR5Vg;A3A1S1S2S0ScR4Vg;A3A1S1S9aScR5SedVt4;A1MaA3S1S9aScR4GaA3S1S9aScR3GaA3S1S9aScR2GaA3S9aScR1GaA3A2A2A2A2A2A2A2A2A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2Lfm;A2A2").
Proof using HMI4 HXz4. drop_sp.
  unfold ftL4, ftQ4, fmL4, fmQ4. destruct (st_free_meta_head t4) as [fm|] eqn:Hfh.
  - right. pose proof (free_ring_head (g :: X) None U t4 HI4 fm Hfh) as (hp & nx & pr2 & nx2 & M1 & M2 & X1 & X2 & K1 & K2).
    assert (N1 : fm <> g) by (intros ->; rewrite memb_cons, sptr_eqb_refl in X1; discriminate).
    assert (N2 : hp <> g) by (intros ->; rewrite memb_cons, sptr_eqb_refl in X2; discriminate).
    exists fm, hp, nx, pr2, nx2. rewrite M1. cbn [U.Mal_nt__G1.Mal_nt_I.flinks0 fst]. rewrite M2. cbn [U.Mal_nt__G1.Mal_nt_I.flinks0].

    destruct (proj1 (inv_rings HI4)) as (msr & Rg & _).
    assert (HfmIn : In fm msr) by (pose proof Rg as Rg'; rewrite Hfh in Rg'; exact (proj1 (ring_head_In _ _ _ Rg'))).
    destruct (fr_member (g :: X) t4 msr fm Rg HfmIn) as (hpX & nxX & MX & HhpIn & HnxIn & _ & _).
    rewrite M1 in MX. assert (EhpX : hpX = hp) by congruence. assert (EnxX : nxX = nx) by congruence. subst hpX nxX.
    destruct (fr_member (g :: X) t4 msr nx Rg HnxIn) as (u1 & u2 & _ & _ & _ & Knx & _).
    destruct (fr_member (g :: X) t4 msr hp Rg HhpIn) as (pr2X & nx2X & MhpX & Hpr2In & Hnx2In & _ & _).
    rewrite M2 in MhpX. assert (E1 : pr2X = pr2) by congruence. assert (E2 : nx2X = nx2) by congruence. subst pr2X nx2X.
    destruct (fr_member (g :: X) t4 msr pr2 Rg Hpr2In) as (u3 & u4 & _ & _ & _ & Kpr2 & _).
    destruct (fr_member (g :: X) t4 msr nx2 Rg Hnx2In) as (u5 & u6 & _ & _ & _ & Knx2 & _).
    repeat split; auto.
  - left. rewrite Mg4. cbn [U.Mal_nt__G1.Mal_nt_I.flinks0 fst]. rewrite Mg4. cbn [U.Mal_nt__G1.Mal_nt_I.flinks0]. auto.
Qed.
Lemma optr_range4 (o : option sptr) : ltac2:(tb__ "0|1|
ScS0S44ScA1Vo;S47ScR1A2A3S9aScR2SedVt4;A1A3F_;Fq;S1S34Z0S165VL;Vo;A2M0A2S34S35G0Z28A2Se3VL;A1A2A2F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp.
  intros Ho. destruct o as [q|]; cbn [optrA].
  - pose proof (key_range4 q (Ho q eq_refl)). lia.
  - pose proof (ceiling_small L). top_ranges; lia.
Qed.
Lemma zF4_range : ltac2:(tb__ "0|0|
S1S34Z0S121A2S34S35S121Z28A2Se3VL;A1A2A2").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp. unfold zF4. apply optr_range4. intros q Hq. destruct ring4_cases as [(E & _)|(fm & hp & nx & pr2 & nx2 & E & _ & _ & _ & _ & _ & _ & _ & _ & KK & _)]; rewrite E in Hq; [discriminate|]. injection Hq as <-. exact KK. Qed.
Lemma zFp4_range : ltac2:(tb__ "0|0|
S1S34Z0S123A2S34S35S123Z28A2Se3VL;A1A2A2").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp. unfold zFp4. apply optr_range4. intros q Hq. destruct ring4_cases as [(_ & _ & E & _)|(fm & hp & nx & pr2 & nx2 & _ & _ & _ & E & _ & _ & _ & _ & _ & _ & KK & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact KK. Qed.
Lemma zFn4_range : ltac2:(tb__ "0|0|
S1S34Z0S122A2S34S35S122Z28A2Se3VL;A1A2A2").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp. unfold zFn4. apply optr_range4. intros q Hq. destruct ring4_cases as [(_ & _ & E & _)|(fm & hp & nx & pr2 & nx2 & _ & _ & _ & E & _ & _ & _ & _ & _ & _ & _ & KK & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact KK. Qed.
Lemma zTTp4_range : ltac2:(tb__ "0|0|
S1S34Z0S125A2S34S35S125Z28A2Se3VL;A1A2A2").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp. unfold zTTp4. apply optr_range4. intros q Hq. destruct ring4_cases as [(_ & _ & _ & _ & E)|(fm & hp & nx & pr2 & nx2 & _ & _ & _ & _ & _ & _ & E & _ & _ & _ & _ & _ & KK & _)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact KK. Qed.
Lemma zTTn4_range : ltac2:(tb__ "0|0|
S1S34Z0S124A2S34S35S124Z28A2Se3VL;A1A2A2").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp. unfold zTTn4. apply optr_range4. intros q Hq. destruct ring4_cases as [(_ & _ & _ & _ & E)|(fm & hp & nx & pr2 & nx2 & _ & _ & _ & _ & _ & _ & E & _ & _ & _ & _ & _ & _ & KK)]; rewrite E in Hq; cbn in Hq; [discriminate|]. injection Hq as <-. exact KK. Qed.

Definition rw4v (j : positive) : option Z := ltac2:(tb__ "0|1|
SaVj;A1S8S45S44S8A1L_;M0S39R1Z8eA2S47S8S166VL;Vam;A2A2G0S39R1Z8fA2S47S8Vgd;A2G0S39R1Za0A2S47S8Se0VL;S118A2A2G0S39R1Za1A2S47S8S123A2G0S39R1Za2A2S47S8S122A2G0S39R1Za3A2S47S8S125A2G0S39R1Za4A2S47S8S124A2G0S39R1Zb4A2S47S8Vrbase;A2G0S39R1Zb5A2S47S8Vrlen;A2S4eS8A1X45x2X45x2X45x2X45x2X45x2X45x2X45x2X45x2X45x2Tz;").

Definition rwN (j : positive) : word := ltac2:(tb__ "0|4|
S44S8A1Sa0Q40M0A1M1Lx;S129Vj;A1S8Sa1G0R1A2Lz;S45G1L_;S4cS3fZc8M2SaVj;A1M3A2S40G3Ze8A2A2S20eS1e7VmsL;A1Sa1Q5S38G3G2A2A2A2S5cVrho;Vj;A2X45x2X44x2").
Definition rhoN : valuation := ltac2:(tb__ "0|0|
S86S120S16dVrho;A1S5fVrhoL;A1A3").
Definition zrN : positive -> Z := zr_of rhoN.
Definition zlN : positive -> list Z := zl_of rhoN.

Lemma rwN_low j : ltac2:(tb__ "0|0|
S19aVj;P64A2S0Sa0Q40A1S120Vj;A1S5cVrho;Vj;A2A3F_;").
Proof using Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hj. unfold rwN, rw4v.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; first [apply Z.eqb_eq in e | apply andb_prop in e as [e _]; apply Z.leb_le in e]; lia|] end.
  reflexivity.
Qed.
Lemma zrN_v j z : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S120Vj;A1Sa1G0Vz;A2A3S1S34Z0Vz;A2S36Vz;S37Z2Z40A2A2A2S0S8S117Vj;A1Vz;A3F_;F_;").
Proof using . drop_sp. intros E Hz. unfold zrN, zr_of, rhoN. cbn [rw]. rewrite E. apply u64. exact Hz. Qed.
Lemma fmQ4_key : In fmQ4 (keys t4).
Proof using HMI4 HXz4. drop_sp. destruct ring4_cases as [(_ & -> & _)|(fm & hp & nx & pr2 & nx2 & _ & -> & _ & _ & _ & _ & _ & _ & _ & KK & _)]; [exact Kg4 | exact KK]. Qed.
Lemma zeN_142 : zrN 142%positive = zM. Proof using HMI Hgd Hsc48 Hsp Hu. apply (zrN_v 142 _ eq_refl). pose proof R_all. lia. Qed.
Lemma zeN_143 : zrN 143%positive = gd. Proof using Hgd. apply (zrN_v 143 _ eq_refl). exact Hgd. Qed.
Lemma zeN_160 : ltac2:(tb__ "0|0|
S0S8S117Pa0A1Se0VL;S118A2A3"). Proof using HMI4 HXz4 Hgd Hsc48 Hsp. apply (zrN_v 160 _ eq_refl). pose proof (key_range4 _ fmQ4_key). pose proof (ceiling_small L). lia. Qed.
Lemma zeN_161 : zrN 161%positive = zFp4. Proof using HMI4 HXz4 Hgd Hsc48 Hsp. apply (zrN_v 161 _ eq_refl). pose proof zFp4_range. pose proof (ceiling_small L). lia. Qed.
Lemma zeN_162 : zrN 162%positive = zFn4. Proof using HMI4 HXz4 Hgd Hsc48 Hsp. apply (zrN_v 162 _ eq_refl). pose proof zFn4_range. pose proof (ceiling_small L). lia. Qed.
Lemma zeN_163 : zrN 163%positive = zTTp4. Proof using HMI4 HXz4 Hgd Hsc48 Hsp. apply (zrN_v 163 _ eq_refl). pose proof zTTp4_range. pose proof (ceiling_small L). lia. Qed.
Lemma zeN_164 : zrN 164%positive = zTTn4. Proof using HMI4 HXz4 Hgd Hsc48 Hsp. apply (zrN_v 164 _ eq_refl). pose proof zTTn4_range. pose proof (ceiling_small L). lia. Qed.
Lemma zeN_180 : zrN 180%positive = rbase. Proof using Hgd Hres64 Hsc48. apply (zrN_v 180 _ eq_refl). lia. Qed.
Lemma zeN_181 : zrN 181%positive = rlen. Proof using Hgd Hres Hres64 Hsc48. apply (zrN_v 181 _ eq_refl). lia. Qed.
Lemma zeN_12 : zrN 12%positive = zG. Proof using HP12 Hgd Hsc48 Hsp. unfold zrN, zr_of, rhoN. cbn [rw]. rewrite (rwN_low 12) by lia. exact HP12. Qed.
Lemma zeN_10 : zrN 10%positive = sp0. Proof using Hgd Hsc48 Hsp. unfold zrN, zr_of, rhoN. cbn [rw]. rewrite (rwN_low 10) by lia. reflexivity. Qed.
Lemma evNu e : ltac2:(tb__ "0|0|
S0S45S109Ve;A1S46A3S0S8Sa2Q40S65S116Ve;A2A2S108S117S119Ve;A3A3F_;").
Proof using . drop_sp. intros He. unfold zrN, zlN. apply eval_zeval. exact He. Qed.
Lemma evN e : ltac2:(tb__ "0|1|
S0S45S109Ve;A1S46A3S0Sa0Q40M0A1S65S116Ve;A2Sa1G0S108S117S119Ve;A3A2A3F_;").
Proof using . drop_sp. intros He. rewrite <- (evNu e He). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma zeNv j : ltac2:(tb__ "0|0|
S0S8S108S117S119SdfVj;A1A3S117Vj;A1A3").
Proof using . drop_sp. cbn [zeval v]. apply Z.mod_small. unfold zrN, zr_of. apply urange. Qed.

Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).
Ltac inpos := cbn [In]; repeat (try (left; reflexivity); right).
Let bv4 : byteview := ltac2:(tb__ "0|0|
Se2S106S55Vmv4;A2S107S55Vmv4;A2A2").
Lemma cell_bytes4 : ltac2:(tb__ "0|4|
Se9S8S9aSe9R2Sf0Vt4;A1A3S0S44S8A1S1d1VL;R3A2S47S8R2A2A3S48S17bR1Sf3R5A1A2S1S1S34Z0S35SecVL;Sf2R6A1A2S3bR2A1A2M0A2S36G0S37Z2Z40A2A2A2S1S0S45S107S55Vmv4;Sa1Q40G0A2M1A3S46A3S0S44Sa0Q8M2A1M3A1S106S55Vmv4;G1A3S47G3Sa1G2SfcR5Sf3R6A1R2A3A2A2A3A2A2F_;Fj;F_;F_;Fz;Fc;").
Proof using HMI4. drop_sp.
  intros c z Hc Hz j Hj.
  assert (CH : MallocInv.cell_holds L bv4 c) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO4))) c Hc).
  exact (cell_bytes L _ _ c z CH Hz j Hj).
Qed.
Lemma cell_rw4 : ltac2:(tb__ "0|3|
Se9S8S8S8S48S9aSe9R5Sf0Vt4;A1A3S0S44S8A1S1d1VL;R6A2S47S8R5A2A3S0S48Sf3R7A1R3A3S0S8SecVL;Sf2R8A1A2S35R6R5A2A3S8S1S34S35R8R7A2M0R1A2S36R1S35G0S3bR6A1A2A2A2S1S0S45S107S55Vmv4;Sa1Q40M1R2A2A3S46A3S3Sa0Q8A1M2G2S0S44G2A1S106S55Vmv4;Sa1G1R3A2A3S47G2R1A2A3Lbb;A2A2F_;Fx;F_;F_;F_;F_;Fkk;Foffs;Fb;Fz;Fc;").
Proof using HMI4 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros c z b offs kk Hc Hz Hw Ha x Hx.
  destruct (cell_bytes4 c z Hc Hz (Z.to_nat (x - (b + offs))) ltac:(rewrite Hw; lia)) as (_ & W & R).
  rewrite Ha in W, R. rewrite Z2Nat.id in W, R by lia. replace (b + offs + (x - (b + offs))) with x in W, R by lia.
  split; [exact W | eexists; exact R].
Qed.
Lemma cell_view4 : ltac2:(tb__ "0|3|
Se9S8S8S8S48S5aS9aSe9R6Sf0Vt4;A1A3S0S44S8A1S1d1VL;R7A2S47S8R6A2A3S0S48Sf3R8A1R4A3S17aR5U8A2S0S8SecVL;Sf2RaA1A2S35R8R7A2A3S0Sa0Q40M0A1S65S116R6A2Sa1G0RaA2A3S48S17bR1R9A2S0S44Sa0Q8M1A1M2A1S106S55Vmv4;Sa1G0S35S35RcRbA2S3bR2A1A2A2A3S47G2S179G2R2S8dRaS65S116R9A2A2Sa1G1Z0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Fkk;Foffs;Fb;Fz;Fc;").
Proof using HMI4. drop_sp.
  intros c z b offs kk e Hc Hz Hw Hk Ha He j Hj.
  destruct (cell_bytes4 c z Hc Hz j ltac:(rewrite Hw; exact Hj)) as (_ & _ & R).
  rewrite Ha in R. rewrite R, He, Hw. rewrite nth_enc_bytes by assumption. reflexivity.
Qed.

Ltac flia := let H := fresh "KEEP" in pose proof I as H; clear - H; top_ranges; lia.
Ltac cells_inside_tac4 := unfold cells_inside; repeat constructor; cbn; flia.
Lemma AG4 q d : ltac2:(tb__ "0|0|
S0S8SecVL;SfbS2aVq;Vd;A2A1A2S35Se0VL;Vq;A2Vd;A2A3").
Proof using Hgd Hsc48 rho. drop_sp. unfold addr_of, loc_addr. destruct q; cbn [padd]. lia. Qed.
Lemma HromL : rom_ok segsU msL. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.

Lemma fmh_cell_In4 : ltac2:(tb__ "0|0|
S9aSe9S100Sf6SffA1U8S104S14Vt4;A1A1A3Sf0Vt4;A1A3").
Proof using Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp. try clear Hsp_high. unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. Qed.
Lemma hold_fmh4 (x : sv) : ltac2:(tb__ "0|0|
S0S45S109Vx;A1S46A3S0S8S108S117S119Vx;A3S121A3S64S55S116S17cVmsL;Vmv4;A2S1cdVx;A1A4F_;F_;").
Proof using HMI4 Hdepth Hgd Hres Hres64 Hres_r Hsc48 HsmL Hsp. try clear Hsp_high.
  intros Sx Ex. pose proof Hctx4 as HCX. pose proof fmh_cell_In4 as CI.
  change (O_fmh x) with (carved (SLit 0x5a3d0) 16 24 [(16, 8%nat, x)]).
  assert (B : bv_unsigned (eval rhoN (SLit 0x5a3d0)) = 0x5a3d0) by (cbn [eval]; apply u64; lia).
  assert (AGc : loc_addr L (mc_loc (MCell (LCtx CTX_free_meta_head) 8 (MallocInv.optr (st_free_meta_head t4)))) = 0x5a3d0 + 16) by (cbn [mc_loc loc_addr]; rewrite HCX; reflexivity).
  apply obj_holds_frame_lit; rewrite ?B; try exact HromL; try lia.
  - cells_inside_tac4.
  - intros o Ho. apply (cell_rw4 _ zF4 0x5a3d0 16 8 CI (cellZ_optr _ _ _) eq_refl AGc). lia.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj.
    apply (cell_view4 _ zF4 0x5a3d0 16 8 x CI (cellZ_optr _ _ _) eq_refl ltac:(lia) AGc); [|exact Hj].
    rewrite (evN x Sx), Ex. reflexivity.
Qed.

Lemma hold_freeK4 (q : sptr) pr nx (bv : sv) five (pv nv : sv) : ltac2:(tb__ "0|4|
S0S44SdA1SebVt4;Vq;A2S47SdS11Vpr;Vnx;A2A2A3S9aScVq;SedVt4;A1M0A3ScS0S44ScA1M1Vpr;S47ScR1A2M2A3S9aScR2G0A3M3F_;Fp;ScS0G1Vnx;G2A3G3F_;Fp;S0S45S109Vbv;A1S46A3S0S45S109Vpv;A1S46A3S0S45S109Vnv;A1S46A3S0S8S108S117S119Vbv;A3Se0VL;Vq;A2A3S0S8S108S117S119Vpv;A3S165VL;Vpr;A2A3S0S8S108S117S119Vnv;A3S165VL;Vnx;A2A3S64S55S116S17cVmsL;Vmv4;A2S1ccVbv;Vfive;Vpv;Vnv;A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using HMI4 Hgd Hsc48 HsmL Hsp. try clear Hsp_high. try clear Hdepth.
  intros Mq Kq Kpr Knx Sb Sp Sn Eb Ep En. pose proof (ceiling_small L) as CS. pose proof (key_range4 q Kq) as (B1 & B2).
  pose proof (optr_range4 pr Kpr) as P12. pose proof (optr_range4 nx Knx) as N12.
  assert (B : bv_unsigned (eval rhoN bv) = addr_of L q) by (rewrite evNu by exact Sb; exact Eb).
  pose proof (fun c Hc => meta_cells_in_imageI (g :: X) None U t4 HI4 q c Kq Hc) as MI. rewrite Mq in MI. cbn [meta_slot_cells] in MI.
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in MI.
  assert (C0 : In (MCell (LMem (padd q 0)) 8 (MallocInv.optr pr)) (image t4)) by (apply MI; inlist).
  assert (C1 : In (MCell (LMem (padd q 8)) 8 (MallocInv.optr nx)) (image t4)) by (apply MI; inlist).
  assert (C2 : In (MCell (LMem (padd q 16)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C3 : In (MCell (LMem (padd q 24)) 4 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C4 : In (MCell (LMem (padd q 28)) 4 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C5 : In (MCell (LMem (padd q 32)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (RW : forall o, 0 <= o < 40 -> Glue.wok_of segsU mv4 (Z_to_bv 64 (addr_of L q + o)) = true /\ exists x, Glue.rd_of segsU mv4 (Z_to_bv 64 (addr_of L q + o)) = Some x).
  { intros o Ho.
    destruct (Z_lt_dec o 8) as [C8|C8]; [apply (cell_rw4 _ _ (addr_of L q) 0 8 C0 (cellZ_optr _ _ _) eq_refl); [apply AG4 | clear - Ho C8; lia]|].
    destruct (Z_lt_dec o 16) as [C16|C16]; [apply (cell_rw4 _ _ (addr_of L q) 8 8 C1 (cellZ_optr _ _ _) eq_refl); [apply AG4 | clear - Ho C8 C16; lia]|].
    destruct (Z_lt_dec o 24) as [C24|C24]; [apply (cell_rw4 _ 0 (addr_of L q) 16 8 C2 eq_refl eq_refl); [apply AG4 | clear - Ho C16 C24; lia]|].
    destruct (Z_lt_dec o 28) as [C28|C28]; [apply (cell_rw4 _ 0 (addr_of L q) 24 4 C3 eq_refl eq_refl); [apply AG4 | clear - Ho C24 C28; lia]|].
    destruct (Z_lt_dec o 32) as [C32|C32]; [apply (cell_rw4 _ 0 (addr_of L q) 28 4 C4 eq_refl eq_refl); [apply AG4 | clear - Ho C28 C32; lia]|].
    apply (cell_rw4 _ 0 (addr_of L q) 32 8 C5 eq_refl eq_refl); [apply AG4 | clear - Ho C32; lia]. }

  assert (ZB : forall off (w : nat) c, In c (image t4) -> cellZ L c = Some 0 -> mc_w c = w -> loc_addr L (mc_loc c) = addr_of L q + off ->
               forall t, (t < w)%nat -> Glue.rd_of segsU mv4 (Z_to_bv 64 (addr_of L q + off + Z.of_nat t)) = Some (Z_to_bv 8 0)).
  { intros off w c Hc Hz Hw Ha t Ht. destruct (cell_bytes4 c 0 Hc Hz t ltac:(rewrite Hw; exact Ht)) as (_ & _ & R). rewrite Ha in R. rewrite R.
    f_equal. f_equal. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; flia). rewrite Z.shiftr_0_l. reflexivity. }
  pose proof (ZB 16 8%nat _ C2 eq_refl eq_refl (AG4 q 16)) as Z16.
  pose proof (ZB 24 4%nat _ C3 eq_refl eq_refl (AG4 q 24)) as Z24.
  pose proof (ZB 28 4%nat _ C4 eq_refl eq_refl (AG4 q 28)) as Z28.
  pose proof (ZB 32 8%nat _ C5 eq_refl eq_refl (AG4 q 32)) as Z32.
  assert (ZERO : forall (k t : nat), (t < k)%nat -> (k <= 8)%nat -> nth t (enc_bytes k (eval rhoN (SLit 0))) (Z_to_bv 8 0) = Z_to_bv 8 0).
  { intros k t Ht Hk. cbn [eval]. rewrite nth_enc_bytes by (clear - Ht Hk; lia). unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; flia). reflexivity. }
  unfold O_freeK. destruct five; cbn [free_cells];
    (apply obj_holds_frame_lit; rewrite ?B; try exact HromL; try (clear - B1 B2 CS; unfold PGSZ in *; lia); [cells_inside_tac4 | intros o Ho; apply RW; clear - Ho; lia |]);
    unfold cells_in_view.
  - constructor; [intros t Ht; apply (cell_view4 _ _ (addr_of L q) 0 8 _ C0 (cellZ_optr _ _ _) eq_refl ltac:(flia) (AG4 q 0)); [rewrite evN by exact Sp; rewrite Ep; reflexivity | exact Ht]|].
    constructor; [intros t Ht; apply (cell_view4 _ _ (addr_of L q) 8 8 _ C1 (cellZ_optr _ _ _) eq_refl ltac:(flia) (AG4 q 8)); [rewrite evN by exact Sn; rewrite En; reflexivity | exact Ht]|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(flia)); apply Z16; exact Ht|].
    constructor.
    { intros t Ht. rewrite (ZERO 8%nat t Ht ltac:(flia)). destruct (Nat.lt_ge_cases t 4) as [T|T].
      - apply Z24. exact T.
      - replace (addr_of L q + 24 + Z.of_nat t) with (addr_of L q + 28 + Z.of_nat (t - 4)) by (clear - T; lia). apply Z28. clear - Ht T; lia. }
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(flia)); apply Z32; exact Ht|]. constructor.
  - constructor; [intros t Ht; apply (cell_view4 _ _ (addr_of L q) 0 8 _ C0 (cellZ_optr _ _ _) eq_refl ltac:(flia) (AG4 q 0)); [rewrite evN by exact Sp; rewrite Ep; reflexivity | exact Ht]|].
    constructor; [intros t Ht; apply (cell_view4 _ _ (addr_of L q) 8 8 _ C1 (cellZ_optr _ _ _) eq_refl ltac:(flia) (AG4 q 8)); [rewrite evN by exact Sn; rewrite En; reflexivity | exact Ht]|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(flia)); apply Z16; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 4%nat t Ht ltac:(flia)); apply Z24; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 4%nat t Ht ltac:(flia)); apply Z28; exact Ht|].
    constructor; [intros t Ht; rewrite (ZERO 8%nat t Ht ltac:(flia)); apply Z32; exact Ht|]. constructor.
Qed.

Definition O_graw : sobj := ltac2:(tb__ "0|0|
S77SdfPcA1S5dZ0A1S5dZ28A1S4fS68A1S71A5").
Lemma gslot_some4 o : ltac2:(tb__ "0|1|
S1S34Z0Vo;A2S36Vo;Z28A2A2S3Sa0Q8A1M0G0S0S44G0A1S5fVrhoL;Sa1Q40S35S15dVL;Vg;A2Vo;A2A2A2S47G0R1A2A3Lb;A2F_;").
Proof using HMI HMI4 HXz4 HZ4 Hgd Hsc48 Hsp Hu bv4. try clear Hsp_high. try clear Hdepth.
  intros Ho. pose proof g_zone as GZ.
  pose proof (fun c Hc => meta_cells_in_imageI (g :: X) None U t4 HI4 g c Kg4 Hc) as MI. rewrite Mg4 in MI. cbn [meta_slot_cells] in MI.
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in MI.
  assert (C0 : In (MCell (LMem (padd g 0)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C1 : In (MCell (LMem (padd g 8)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C2 : In (MCell (LMem (padd g 16)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C3 : In (MCell (LMem (padd g 24)) 4 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C4 : In (MCell (LMem (padd g 28)) 4 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (C5 : In (MCell (LMem (padd g 32)) 8 (VZ 0)) (image t4)) by (apply MI; inlist).
  assert (W : Glue.wok_of segsU mv4 (Z_to_bv 64 (zG + o)) = true).
  { unfold zG, U.Mal_nt__G1.Mal_nt_I.zG.
    destruct (Z_lt_dec o 8); [apply (cell_rw4 _ 0 (addr_of L g) 0 8 C0 eq_refl eq_refl (AG4 g 0)); lia|].
    destruct (Z_lt_dec o 16); [apply (cell_rw4 _ 0 (addr_of L g) 8 8 C1 eq_refl eq_refl (AG4 g 8)); lia|].
    destruct (Z_lt_dec o 24); [apply (cell_rw4 _ 0 (addr_of L g) 16 8 C2 eq_refl eq_refl (AG4 g 16)); lia|].
    destruct (Z_lt_dec o 28); [apply (cell_rw4 _ 0 (addr_of L g) 24 4 C3 eq_refl eq_refl (AG4 g 24)); lia|].
    destruct (Z_lt_dec o 32); [apply (cell_rw4 _ 0 (addr_of L g) 28 4 C4 eq_refl eq_refl (AG4 g 28)); lia|].
    apply (cell_rw4 _ 0 (addr_of L g) 32 8 C5 eq_refl eq_refl (AG4 g 32)); lia. }
  unfold Glue.wok_of in W. destruct (mv4 (Z_to_bv 64 (zG + o))) as [b|] eqn:E.
  - destruct (rm rhoL (Z_to_bv 64 (zG + o))) as [b'|] eqn:E'; [exists b'; reflexivity|]. exfalso.
    pose proof (proj2 (proj2 HZ4 (Z_to_bv 64 (zG + o))) E') as C. rewrite C in E. discriminate.
  - exfalso. change (Glue.wseg_addr segsU (Z_to_bv 64 (zG + o))) with (Contract.wseg_addr segsU (Z_to_bv 64 (zG + o))) in W.
    pose proof (ClientLaws.wseg_in_image_U _ W) as WI. cbn [mc_img_lo mc_img_hi C_U] in WI. top_ranges. rewrite u64_of_sum in WI by lia. lia.
Qed.
Lemma hold_graw4 : ltac2:(tb__ "0|0|
S64S55S116S17cVmsL;S5fVrhoL;A1A2S11bA4").
Proof using HMI HMI4 HP12 HXz4 HZ4 Hgd Hsc48 HsmL Hsp Hu bv4. try clear Hsp_high. try clear Hdepth.
  pose proof g_zone as GZ. top_ranges.
  assert (B : bv_unsigned (eval rhoN (v 12)) = zG) by (rewrite evNu by reflexivity; rewrite zeNv; exact zeN_12).
  unfold O_graw, obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite B. rewrite !soff_lit_small by lia.
  split; [lia|]. split.
  { intros off Hoff _. cbn [with_mem ms_mem]. destruct (gslot_some4 off Hoff) as [b Hb]. apply (wview_of_views segsU); unfold Glue.wok_of, Glue.rd_of; rewrite Hb; [reflexivity | exists b; reflexivity]. }
  split; [constructor|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. destruct (gslot_some4 off Hoff) as [b Hb]. exists b. rewrite (rd_with_mem segsU) by exact HromL. unfold Glue.rd_of. rewrite Hb. reflexivity.
Qed.

Lemma rdG4 m : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;S1ffS55Vm;A2S106S55Vm;A2A3"). Proof using . reflexivity. Qed.
Lemma guard_bytes4 j : ltac2:(tb__ "0|3|
S17bVj;U8M0A2S0S44Sa0Q8M1A1M2A1S106S55S5fVrhoL;A1Sa1Q40S35Z5a338S3bVj;A1A2A2A3S47G2Sa1G1SfcVgd;G0Vj;A3A2A2A3F_;").
Proof using EmW Erd HMI4 HZ Hcanary4 Hgd Hgd_holds Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hj. pose proof (Hcanary4 (0x5a338 + Z.of_nat j) ltac:(cbn [mc_chk_guard_got mc_chk_guard C_U]; lia)) as HC. rewrite !rdG4 in HC. rewrite HC.
  pose proof (Hgd_holds j Hj) as E. rewrite Erd in E. cbn [mc_chk_guard C_U] in E.
  pose proof (rv_byte _ _ E) as R. unfold Glue.rd_of in R. unfold Contract.rd_of, Glue.rd_of. rewrite <- EmW.
  rewrite <- (HZ_at (Z_to_bv 64 (369464 + Z.of_nat j))); [exact R|].
  intros x Hx Rx. rewrite u64_of_sum in Rx by lia. pose proof (key_zone4 x ltac:(pose proof (proj1 (inv_X HI4 x ltac:(right; exact Hx))); assumption)). lia.
Qed.
Lemma hold_guard4 : ltac2:(tb__ "0|0|
S64S55S116S17cVmsL;S5fVrhoL;A1A2S181A4").
Proof using EmW Erd HMI4 HZ Hcanary4 Hgd Hgd_holds Hsc48 HsmL Hsp. try clear Hsp_high. try clear Hdepth.
  change O_guard_ with (carved (SLit 0x5a338) 0 8 [(0, 8%nat, v 143)]).
  assert (B : bv_unsigned (eval rhoN (SLit 0x5a338)) = 0x5a338) by (cbn [eval]; apply u64; lia).
  apply obj_holds_frame_lit; rewrite ?B; try exact HromL; try lia.
  - cells_inside_tac4.
  - intros o Ho. split.
    + unfold Glue.wok_of. destruct (rm rhoL (Z_to_bv 64 (369464 + o))); [reflexivity|]. exact (forall_range_dec _ 0x5a338 8 guard_wseg (369464 + o) ltac:(lia)).
    + pose proof (guard_bytes4 (Z.to_nat o) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. eexists. exact E.
  - unfold cells_in_view. constructor; [|constructor]. intros j Hj. rewrite Z.add_0_r.
    rewrite (guard_bytes4 j Hj). f_equal. rewrite (evN (v 143) eq_refl), zeNv, zeN_143, nth_enc_bytes by lia. reflexivity.
Qed.

Lemma HZ4_at a : ltac2:(tb__ "0|2|
ScS9aScR1S43ScVg;VX;A3A3S2S1S34Se0VL;R2A2M0Sa2Q40Va;A2M1A2S36G1S35G0Z28A2A2A2A1F_;Fx;S0S44Sa0Q8A1A1Vmv4;Va;A1S5fVrhoL;Va;A2A3F_;").
Proof using HZ4 Hgd Hsc48 rho. drop_sp. intros H1. apply (proj1 HZ4 a). intros (x & Hx & R). exact (H1 x Hx ltac:(unfold META_SIZE in R; lia)). Qed.
Lemma hold_real4 (o : sobj) lo hi : ltac2:(tb__ "0|1|
S0S4bS8S8A2S6cS116Vo;A2S49S8S8Vlo;Vhi;A4A3ScS9aScR1S43ScVg;VX;A3A3S4S34Vhi;Se0VL;R2A2M0A2S34S35G0Z28A2Vlo;A2A2F_;Fx;S64S55S116S17cVmsL;Vmv4;A2Vo;A4S64S55S116S17cVmsL;S5fVrhoL;A1A2Vo;A4F_;F_;F_;").
Proof using HZ4 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros R XS HO. pose proof (urange (eval rhoN (ob_base o))) as Ub.
  pose proof HO as ((B1 & B2 & B3 & B4) & _). unfold obj_range in R. pose proof (f_equal fst R) as E1. pose proof (f_equal snd R) as E2. cbn [fst snd] in E1, E2.
  apply (obj_holds_mem_ext segsU rhoN (with_mem msL mv4) (with_mem msL (rm rhoL)) o); [intros; reflexivity | | exact HO].
  intros off Hoff. cbn [ms_mem with_mem]. symmetry. apply HZ4_at. intros x Hx Rx. rewrite u64_of_sum in Rx by lia. destruct (XS x Hx); lia.
Qed.
Lemma XS_key4 x : ltac2:(tb__ "0|0|
S9aScVx;S43ScVg;VX;A3A3S9aScVx;SedVt4;A1A3F_;").
Proof using HMI4. drop_sp. intros Hx. exact (proj1 (inv_X HI4 x Hx)). Qed.
Lemma XS_free x : ltac2:(tb__ "0|1|
S9aScVx;S43ScVg;VX;A3A3S0S44SdA1SebVt4;Vx;A2S47SdS11S4eScA1M0G0A2A2A3F_;"). Proof using HXz4. exact (HXz4 x). Qed.

Lemma sp0_range4 : ltac2:(tb__ "0|1|
S1S1S34Z1000S14dVrho;A1M0A2S36G0S37Z2Z40A2A2A2S0S8S3aG0Z10A2Z0A3A2"). Proof using Hgd Hsc48 Hsp. unfold sp0, U.Mal_nt__G2.Mal_nt_Z.sp0. pose proof Hsp. pose proof (urange (rw rho 10%positive)). lia. Qed.
Lemma D0_range4 : ltac2:(tb__ "0|1|
S1S34S3cS37Z2Z28A2A1S14cVrho;A1M0A2S34G0N60A2A2"). Proof using Hdepth Hgd Hsc48. unfold D0, U.Mal_nt__G2.Mal_nt_Z.D0. pose proof Hdepth. lia. Qed.
Lemma stk_frame4 a : ltac2:(tb__ "0|2|
S2S1S34S35S14dVrho;A1M0S14cVrho;A1A2Sa2Q40Va;A2M1A2S36G1S38G0Z60A2A2A2A1S0S44Sa0Q8A1A1S1e6VmsL;Va;A2S5fVrhoL;Va;A2A3F_;").
Proof using Hdepth Hgd HrL10 HrL15 Hsc48 HsmL Hsp. try clear Hsp_high.
  intros Ha. pose proof HsmL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hfr) & _). cbn [fst snd cfg_ms cfg_model] in Hfr.
  apply Hfr. unfold outside_all. cbn [ss_objs L_nt]. constructor; [|constructor].
  cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi eval]. unfold V_DEPTH.
  rewrite HrL10, u64_of_sum by (pose proof sp0_range4; pose proof D0_range4; lia).
  rewrite soff_lit_small by lia.
  unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. rewrite HrL15, toS_mod by lia.
  rewrite (toS_small 64 (D0 + 96)) by (pose proof D0_range4; lia). unfold in_rng. cbn [fst snd]. lia.
Qed.
Lemma evN_10 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S65S116S61PaA1A2A2S14dVrho;A1A3"). Proof using Hgd Hsc48 Hsp. cbn [eval rhoN rw]. rewrite (rwN_low 10) by lia. reflexivity. Qed.
Lemma soffN_15 : ltac2:(tb__ "0|0|
S0S8S7eS116S61PfA1A2S14cVrho;A1A3"). Proof using Hgd Hsc48 Hsp. unfold soff. cbn [eval rhoN rw]. rewrite (rwN_low 15) by lia. rewrite bv_signed_toS by (cbn; lia). reflexivity. Qed.
Definition stk_vars (vv : positive) : bool := ltac2:(tb__ "0|0|
S9dS9S19dVvv;A1S43S9PaS43S9PbS43S9P1cS43S9P1dS43S9P26S43S9P27S43S9P8fS4fS9A1A3A3A3A3A3A3A3A3").
Lemma stk_vars_ok : ltac2:(tb__ "0|0|
S0S45S1bdS128S11fA2S46A3"). Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma stk_vars_agree vv : ltac2:(tb__ "0|0|
S0S45S128Vvv;A1S46A3S0Sa0Q40A1S5cS116Vvv;A2S5cVrhoW;Vvv;A2A3F_;").
Proof using Hgd Hsc48 Hsp i mW rd0 s. try clear Hsp_high. try clear Hdepth.
  unfold stk_vars. intros H. apply existsb_exists in H as (u & Hux & E). apply Pos.eqb_eq in E. subst u.
  cbn [rw rhoN rhoW rho1].
  destruct Hux as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; try (rewrite (rwN_low _) by lia; rewrite (rw1_low _) by lia; reflexivity).
  reflexivity.
Qed.
Lemma hold_stk_top4 : ltac2:(tb__ "0|0|
S64S55S116VmsL;S11fA4").
Proof using Hdepth Hgd HrL10 HrL15 Hsc48 HsmL Hsp Hstk. try clear Hsp_high.
  pose proof sp0_range4 as SPR. pose proof D0_range4 as DR.
  assert (T' : obj_holds segsU rhoN (with_mem msL (rm rhoL)) o_stk_top).
  { apply (obj_holds_agreeing segsU stk_vars rhoW rhoN); [exact stk_vars_agree | intros; reflexivity | exact stk_vars_ok | exact Hstk]. }
  apply (obj_holds_mem_ext segsU rhoN (with_mem msL (rm rhoL)) msL o_stk_top); [intros; reflexivity | | exact T'].
  intros off Hoff. unfold obj_lo_of, obj_hi_of, o_stk_top in Hoff. cbn [ob_base ob_lo ob_hi] in Hoff. rewrite !soff_lit_small in Hoff by lia.
  change (ob_base o_stk_top) with (SVar 10). rewrite evN_10. cbn [with_mem ms_mem]. apply stk_frame4. rewrite u64_of_sum by lia. lia.
Qed.
Lemma hold_stk4 : ltac2:(tb__ "0|0|
S64S55S116VmsL;S17eA4").
Proof using Hdepth Hgd HrL10 HrL15 Hsc48 HsmL Hsp Hsp_high Hstk.
  pose proof sp0_range4 as SPR. pose proof D0_range4 as DR. pose proof Hsp_high as SH. pose proof (ceiling_small L) as CS.
  pose proof hold_stk_top4 as HST. pose proof evN_10 as evN_10'. pose proof soffN_15 as soffN_15'.
  clear - SPR DR SH CS HST evN_10' soffN_15' HsmL HrL10 HrL15.
  top_ranges.

  assert (E10 : bv_unsigned (rw rhoL 10%positive) = sp0 - 96) by (rewrite HrL10; apply u64_of_sum; lia).
  assert (EL : soff rhoL (SVar 15) = D0 + 96).
  { unfold soff. cbn [eval]. rewrite bv_signed_toS by (cbn; lia). change (Z.of_N 64) with 64. unfold V_DEPTH in HrL15. rewrite HrL15, toS_mod by lia. apply toS_small; lia. }
  assert (E0 : soff rhoL (SLit 0) = 0) by (apply soff_lit_small; lia).
  assert (EN0 : soff rhoN (SLit 0) = 0) by (apply soff_lit_small; lia). assert (EN96 : soff rhoN (SLit (-96)) = -96) by (apply soff_lit_small; lia).

  pose proof HsmL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallL & _ & _) & _). cbn [fst snd cfg_ms cfg_model ss_objs L_nt] in HallL.
  apply Forall_cons_iff in HallL as [HW _].
  destruct HW as ((W1 & W2 & W3 & W4) & Ww & _ & Wd & _). unfold obj_lo_of, obj_hi_of, stack_win in W1, W2, W3, W4, Ww, Wd. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in W1, W2, W3, W4, Ww, Wd.
  unfold V_DEPTH in *. cbn [eval] in W1, W2, W3, W4, Ww, Wd.
  rewrite ?E10, ?EL, ?E0 in W1. rewrite ?E10, ?EL, ?E0 in W2. rewrite ?E10, ?EL, ?E0 in W3. rewrite ?E10, ?EL, ?E0 in W4. rewrite ?E10, ?EL, ?E0 in Ww. rewrite ?E10, ?EL, ?E0 in Wd.

  pose proof HST as ((T1 & T2 & T3 & T4) & Tw & Tc & Td & _). unfold obj_lo_of, obj_hi_of, o_stk_top in T1, T2, T3, T4, Tw, Tc, Td. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in T1, T2, T3, T4, Tw, Tc, Td.
  rewrite ?evN_10', ?EN0, ?EN96 in T1. rewrite ?evN_10', ?EN0, ?EN96 in T2. rewrite ?evN_10', ?EN0, ?EN96 in T3. rewrite ?evN_10', ?EN0, ?EN96 in T4.
  rewrite ?evN_10', ?EN0, ?EN96 in Tw. rewrite ?evN_10', ?EN0, ?EN96 in Td.
  unfold obj_holds, obj_lo_of, obj_hi_of, o_stk_saved. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite evN_10', soffN_15', EN0.
  split; [clear - SPR DR SH CS W1 W2 W3 W4 T1 T2 T3 T4; lia|]. split.
  { intros off Hoff Hw. destruct (Z_lt_dec off (-96)) as [LT|GE].
    - replace (sp0 + off) with (sp0 - 96 + (off + 96)) by flia. apply Ww; [clear - SPR DR SH CS EN0 EN96 E0 EL Hoff LT; lia | exact Hw].
    - apply Tw; [clear - SPR DR SH CS EN0 EN96 E0 EL Hoff GE; lia | exact Hw]. }
  split.
  { apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Tc c Hc) as (C1 & C2 & C3). split; [clear - SPR DR SH CS C1 EN0 EN96; lia|]. split; [exact C2 | exact C3]. }
  split; [|exact I].
  intros off Hoff NC. destruct (Z_lt_dec off (-96)) as [LT|GE].
  - replace (sp0 + off) with (sp0 - 96 + (off + 96)) by flia. apply Wd; [clear - SPR DR SH CS EN0 EN96 E0 EL Hoff LT; lia|]. intros Cv. inversion Cv.
  - apply Td; [clear - SPR DR SH CS EN0 EN96 E0 EL Hoff GE; lia | exact NC].
Qed.

Definition N4 (f : nat) : list sobj := ltac2:(tb__ "0|6|
S48S4aS5bA1M0Lf;Vf;S43S5bS11bS43S5bS181S43S5bS1cdS5dZ0A1A1S4fS5bA1M1A3A3A3S48S48G0Ln;R1S43S5bS11bS43S5bS181S43S5bS1cdSdfPa0A1M2A1M3S43S5bS1ccG2S4dG2SdfPa2A1M4A4G1A3A3A3A3S48S43S5bS11bS43S5bS181S43S5bG3S43S5bS1ccG2S4dSdfPa1A1M5G4A4S43S5bS1ccG5S4dSdfPa3A1SdfPa4A1A4G1A3A3A3A3A3Ln0;X48x2Ln;X48x2").
Lemma objs_t2n_eq f : ltac2:(tb__ "0|0|
S17aVf;U2A2S0S4aS5bA1S193Vf;A1S43S5bS17eS126Vf;A1A3A3F_;").
Proof using . drop_sp. intros Hf. destruct f as [|[|f]]; reflexivity. Qed.
Definition Sh4 (f : nat) : sstate := ltac2:(tb__ "0|0|
S7bZ20c1cS18dS56S76S4eS5aA1S43S5bS17eS4fS5bA1A3S18aVf;A1S189S4dA9").
Lemma S_t2n_eq f : ltac2:(tb__ "0|1|
S17aVf;U2A2S0S78S17fVf;A1S7bS74S11aVf;A1M0A1S83G0A1S6eG0A1S6dG0A1S75G0A1S50S5bS6bG0A1S126Vf;A1A3S82G0A1S189S6aG0A1A9A3F_;").
Proof using . drop_sp. intros Hf. unfold S_t2n_of, Sh4. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient app]. rewrite (objs_t2n_eq f Hf). reflexivity. Qed.
Lemma Sh4_swf f : ltac2:(tb__ "0|0|
S17aVf;U2A2S0S45S79S11aVf;A1A1S46A3F_;").
Proof using . drop_sp. intros Hf. destruct f as [|[|f]]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma S_t2n_swf f : ltac2:(tb__ "0|0|
S17aVf;U2A2S0S45S79S17fVf;A1A1S46A3F_;").
Proof using . drop_sp. intros Hf. destruct f as [|[|f]]; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma fshape4_le : (fshape4 <= 2)%nat. Proof using Hgd Hsc48 rho. unfold fshape4. destruct (st_free_meta_head t4); [destruct (sptr_eqb _ _)|]; lia. Qed.

Lemma reg_sv_Lnt z : ltac2:(tb__ "0|1|
S1S34Z1Vz;A2S34Vz;Z1fA2A2S0S5aS5eS156S151A1Vz;A2S45S5aL_;S58S3dVz;A1M0A1S59G0A1S61S19cP64S19eG0A1A2A1X45x2A3F_;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros Hz.
  pose proof (forall_range_dec (fun z => sv_eqb (reg_sv (L_nt NTE_U) z)
                 (if callee_saved (Z.to_nat z) then pre_reg (Z.to_nat z) else SVar (100 + Pos.of_nat (Z.to_nat z))%positive)) 1 31
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as H.
  apply sv_eqb_sound in H. exact H.
Qed.
Lemma reg_sv_Sh f z : ltac2:(tb__ "0|2|
S1S34Z0M0Vz;A2S34Vz;Z1fA2A2S0S5aS5eS11aVf;A1Vz;A2S45S5aL_;S39Vz;G0A2S5dG0A1M1S179S5aS3dVz;A1S18dG1A4X45x2A3F_;").
Proof using . drop_sp. intros Hz. unfold reg_sv, Sh4. cbn [ss_regs]. destruct (z =? 0); reflexivity. Qed.

Lemma pre_freg_tableN : ltac2:(tb__ "0|1|
S8S1S34Z0M0R1A2S34R1Z1fA2A2S3S9S9S1S0S5aS179S5aS3dR3A1S56S5dG0A1A4S61R1A1A3S1S199P3cR1A2S19aR1P5cA2A2A2Lvv;A2F_;Fz;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros z Hz.
  pose proof (forall_range_dec (fun z => match nth (Z.to_nat z) pre_fregs (SLit 0) with
                                         | SVar vv => (60 <=? vv)%positive && (vv <? 92)%positive | _ => false end)%bool 0 32
                ltac:(vm_compute; reflexivity) z ltac:(lia)) as XX. cbn beta in XX.
  destruct (nth (Z.to_nat z) pre_fregs (SLit 0)) as [|vv| | | | | |]; try discriminate. exists vv.
  apply andb_prop in XX as [X1 X2]. apply Pos.leb_le in X1. apply Pos.ltb_lt in X2. auto.
Qed.
Lemma regs_Sh4 f : ltac2:(tb__ "0|0|
S95S116S11aVf;A1VmsL;A3").
Proof using HMI HP12 Hdepth Hgd HrL10 HrL11 HrL110 HrL111 HrL28 HrL29 HrL38 HrL39 HrLlow Hres Hres64 Hsc48 HsmL Hsp Hu. try clear Hsp_high.
  pose proof HsmL as (_ & _ & _ & _ & _ & _ & Hr & _). cbn [fst snd cfg_ms cfg_model] in Hr.
  pose proof sp0_range4 as SPR. pose proof D0_range4 as DR. pose proof Hres64 as R64. pose proof R_all as RA. pose proof (ceiling_small L) as CS.
  intros r Hr0.
  assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).

  assert (SCR : forall k, k = bv_unsigned r -> reg_get (ms_regs msL) r = eval rhoN (SVar (Pos.of_nat (Z.to_nat (200 + k))))).
  { intros k ->. cbn [eval rhoN rw]. unfold rwN.
    replace (rw4v (Pos.of_nat (Z.to_nat (200 + bv_unsigned r)))) with (@None Z).
    2: { unfold rw4v. repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; apply Z.eqb_eq in e; clear - e UR; lia|] end. reflexivity. }
    replace ((200 <=? Z.pos (Pos.of_nat (Z.to_nat (200 + bv_unsigned r)))) && (Z.pos (Pos.of_nat (Z.to_nat (200 + bv_unsigned r))) <? 232))%bool with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.pos (Pos.of_nat (Z.to_nat (200 + bv_unsigned r))) - 200) with (bv_unsigned r) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (CS' : forall k, k = bv_unsigned r -> reg_get (ms_regs msL) r = eval rhoL (reg_sv (L_nt NTE_U) k)) by (intros k ->; apply Hr; exact Hr0).
  set (z := bv_unsigned r) in *.
  assert (Hz : exists n : nat, (n < 32)%nat /\ z = Z.of_nat n) by (exists (Z.to_nat z); lia).
  destruct Hz as (n & Hn & Ez). rewrite Ez in *.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [lia| .. | lia].
  - change (Z.of_nat 1) with 1%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 1) with (SLit 133844). rewrite (CS' 1 eq_refl). change (reg_sv (L_nt NTE_U) 1) with (SVar 11). cbn [eval]. rewrite HrL11. reflexivity.
  - change (Z.of_nat 2) with 2%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 2) with (SAlu ALU_ADD (SVar 10) (SLit (-96))). rewrite (CS' 2 eq_refl). change (reg_sv (L_nt NTE_U) 2) with (SVar 10).
    cbn [eval rhoN rw]. rewrite HrL10, (rwN_low 10) by lia. apply bv_eq. rewrite (u64_of_sum (sp0 - 96)) by lia.
    rewrite (zalu_sound 64 63 ALU_ADD) by (left; split; reflexivity). cbn [zalu]. change (Z.of_N 64) with 64. change (bv_unsigned (rw rho 10%positive)) with sp0.
    change (bv_unsigned (Z_to_bv 64 (-96))) with 18446744073709551520. replace (sp0 + 18446744073709551520) with (sp0 - 96 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - change (Z.of_nat 3) with 3%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 3) with (SVar 23). rewrite (CS' 3 eq_refl). change (reg_sv (L_nt NTE_U) 3) with (SVar 23). cbn [eval rhoN rw]. rewrite (HrLlow 23%positive) by inpos. rewrite (rwN_low 23) by reflexivity. reflexivity.
  - change (Z.of_nat 4) with 4%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 4) with (SVar 24). rewrite (CS' 4 eq_refl). change (reg_sv (L_nt NTE_U) 4) with (SVar 24). cbn [eval rhoN rw]. rewrite (HrLlow 24%positive) by inpos. rewrite (rwN_low 24) by reflexivity. reflexivity.
  - change (Z.of_nat 5) with 5%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 5) with (SVar 205). exact (SCR 5 eq_refl).
  - change (Z.of_nat 6) with 6%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 6) with (SVar 206). exact (SCR 6 eq_refl).
  - change (Z.of_nat 7) with 7%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 7) with (SVar 207). exact (SCR 7 eq_refl).
  - change (Z.of_nat 8) with 8%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 8) with (v 142). rewrite (CS' 8 eq_refl). change (reg_sv (L_nt NTE_U) 8) with (SVar 28). cbn [eval rhoN rw]. rewrite HrL28. rewrite (evN (v 142) eq_refl), zeNv, zeN_142. reflexivity.
  - change (Z.of_nat 9) with 9%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 9) with (SLit 369464). rewrite (CS' 9 eq_refl). change (reg_sv (L_nt NTE_U) 9) with (SVar 29). cbn [eval]. rewrite HrL29. reflexivity.
  - change (Z.of_nat 10) with 10%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 10) with (v 180). rewrite (CS' 10 eq_refl). change (reg_sv (L_nt NTE_U) 10) with (SVar 110). cbn [eval rhoN rw]. rewrite HrL110. rewrite (evN (v 180) eq_refl), zeNv, zeN_180. reflexivity.
  - change (Z.of_nat 11) with 11%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 11) with (v 181). rewrite (CS' 11 eq_refl). change (reg_sv (L_nt NTE_U) 11) with (SVar 111). cbn [eval rhoN rw]. rewrite HrL111. rewrite (evN (v 181) eq_refl), zeNv, zeN_181. reflexivity.
  - change (Z.of_nat 12) with 12%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 12) with (SVar 212). exact (SCR 12 eq_refl).
  - change (Z.of_nat 13) with 13%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 13) with (SVar 213). exact (SCR 13 eq_refl).
  - change (Z.of_nat 14) with 14%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 14) with (SVar 214). exact (SCR 14 eq_refl).
  - change (Z.of_nat 15) with 15%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 15) with (SVar 215). exact (SCR 15 eq_refl).
  - change (Z.of_nat 16) with 16%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 16) with (SVar 216). exact (SCR 16 eq_refl).
  - change (Z.of_nat 17) with 17%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 17) with (SVar 217). exact (SCR 17 eq_refl).
  - change (Z.of_nat 18) with 18%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 18) with (SLit 369616). rewrite (CS' 18 eq_refl). change (reg_sv (L_nt NTE_U) 18) with (SVar 38). cbn [eval]. rewrite HrL38. reflexivity.
  - change (Z.of_nat 19) with 19%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 19) with (v 12). rewrite (CS' 19 eq_refl). change (reg_sv (L_nt NTE_U) 19) with (SVar 39). cbn [eval rhoN rw]. rewrite HrL39. rewrite (evN (v 12) eq_refl), zeNv, zeN_12. reflexivity.
  - change (Z.of_nat 20) with 20%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 20) with (SVar 40). rewrite (CS' 20 eq_refl). change (reg_sv (L_nt NTE_U) 20) with (SVar 40). cbn [eval rhoN rw]. rewrite (HrLlow 40%positive) by inpos. rewrite (rwN_low 40) by reflexivity. reflexivity.
  - change (Z.of_nat 21) with 21%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 21) with (SVar 41). rewrite (CS' 21 eq_refl). change (reg_sv (L_nt NTE_U) 21) with (SVar 41). cbn [eval rhoN rw]. rewrite (HrLlow 41%positive) by inpos. rewrite (rwN_low 41) by reflexivity. reflexivity.
  - change (Z.of_nat 22) with 22%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 22) with (SVar 42). rewrite (CS' 22 eq_refl). change (reg_sv (L_nt NTE_U) 22) with (SVar 42). cbn [eval rhoN rw]. rewrite (HrLlow 42%positive) by inpos. rewrite (rwN_low 42) by reflexivity. reflexivity.
  - change (Z.of_nat 23) with 23%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 23) with (SVar 43). rewrite (CS' 23 eq_refl). change (reg_sv (L_nt NTE_U) 23) with (SVar 43). cbn [eval rhoN rw]. rewrite (HrLlow 43%positive) by inpos. rewrite (rwN_low 43) by reflexivity. reflexivity.
  - change (Z.of_nat 24) with 24%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 24) with (SVar 44). rewrite (CS' 24 eq_refl). change (reg_sv (L_nt NTE_U) 24) with (SVar 44). cbn [eval rhoN rw]. rewrite (HrLlow 44%positive) by inpos. rewrite (rwN_low 44) by reflexivity. reflexivity.
  - change (Z.of_nat 25) with 25%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 25) with (SVar 45). rewrite (CS' 25 eq_refl). change (reg_sv (L_nt NTE_U) 25) with (SVar 45). cbn [eval rhoN rw]. rewrite (HrLlow 45%positive) by inpos. rewrite (rwN_low 45) by reflexivity. reflexivity.
  - change (Z.of_nat 26) with 26%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 26) with (SVar 46). rewrite (CS' 26 eq_refl). change (reg_sv (L_nt NTE_U) 26) with (SVar 46). cbn [eval rhoN rw]. rewrite (HrLlow 46%positive) by inpos. rewrite (rwN_low 46) by reflexivity. reflexivity.
  - change (Z.of_nat 27) with 27%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 27) with (SVar 47). rewrite (CS' 27 eq_refl). change (reg_sv (L_nt NTE_U) 27) with (SVar 47). cbn [eval rhoN rw]. rewrite (HrLlow 47%positive) by inpos. rewrite (rwN_low 47) by reflexivity. reflexivity.
  - change (Z.of_nat 28) with 28%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 28) with (SVar 228). exact (SCR 28 eq_refl).
  - change (Z.of_nat 29) with 29%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 29) with (SVar 229). exact (SCR 29 eq_refl).
  - change (Z.of_nat 30) with 30%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 30) with (SVar 230). exact (SCR 30 eq_refl).
  - change (Z.of_nat 31) with 31%Z in SCR, CS' |- *. change (reg_sv (Sh4 f) 31) with (SVar 231). exact (SCR 31 eq_refl).
Qed.

Lemma pre_fact k p : ltac2:(tb__ "0|0|
S0S44S60A1S9fS60S50S60S43S60S201S43S60S202S159A1S4fS60A1A3A3S200S159A1A3Vk;A3S47S60Vp;A2A3S69Vrho;Vp;A2F_;").
Proof using Hsm_pre. drop_sp.
  intros Hk. pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractNT.Pre_nt] in HF0.
  apply (proj1 (Forall_forall _ _) HF0 p). eapply nth_error_In. exact Hk.
Qed.
Lemma holdN_P1 : SymState.holds rhoN (SPAlign 10%positive 4).
Proof using Hgd Hsc48 Hsm_pre Hsp. try clear Hsp_high. try clear Hdepth. pose proof (pre_fact 0 _ eq_refl) as H0. cbn [SymState.holds] in H0 |- *. cbn [rw rhoN]. rewrite (rwN_low 10) by lia. exact H0. Qed.
Lemma holdN_P3 : ltac2:(tb__ "0|0|
S69S116S67S1c3S5dN60A1S61PfA1A3A2").
Proof using Hgd Hsc48 Hsm_pre Hsp. try clear Hsp_high. try clear Hdepth. pose proof (pre_fact 2 _ eq_refl) as H0. cbn [SymState.holds eval] in H0 |- *. cbn [rw rhoN]. rewrite (rwN_low 15) by lia. exact H0. Qed.
Lemma holdN_P4 : ltac2:(tb__ "0|0|
S69S116S67S1c3S61PfA1S5dS3cS37Z2Z28A2A1A1A3A2").
Proof using Hgd Hsc48 Hsm_pre Hsp. try clear Hsp_high. try clear Hdepth. pose proof (pre_fact 3 _ eq_refl) as H0. cbn [SymState.holds eval] in H0 |- *. cbn [rw rhoN]. rewrite (rwN_low 15) by lia. exact H0. Qed.
Ltac zfact := match goal with |- SymState.holds _ ?p => apply (proj2 (holds_zholds rhoN p eq_refl)) end; cbn [zholds zeval zcond]; fold zrN; fold zlN; rewrite ?zeNv.
Lemma holdN_align12 : SymState.holds rhoN (SPAlign 12%positive 3).
Proof using HMI HP12 Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp Hu. try clear Hsp_high. pose proof R_all as RA. cbn [SymState.holds]. cbn [rw rhoN]. rewrite (rwN_low 12) by lia. rewrite HP12. fold zG. split; [lia|]. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG in RA |- *. change (2 ^ 3) with 8. tauto. Qed.
Lemma zeN_13 : zrN 13%positive = i. Proof using HP13 Hgd Hsc48 Hsp. unfold zrN, zr_of, rhoN. cbn [rw]. rewrite (rwN_low 13) by lia. exact HP13. Qed.
Lemma holdN_g1 : ltac2:(tb__ "0|0|
S69S116S7aS67S1c2S5dZ0A1SdfPcA1A3A1A2").
Proof using HMI HP12 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. pose proof g_zone as GZ. top_ranges. zfact. rewrite zeN_12. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq 0 zG)) by lia. discriminate. Qed.
Lemma holdN_g2 : ltac2:(tb__ "0|0|
S69S116S7aS67S1c2SdfPcA1S5dZ0A1A3A1A2").
Proof using HMI HP12 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. pose proof g_zone as GZ. top_ranges. zfact. rewrite zeN_12. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq zG 0)) by lia. discriminate. Qed.
Lemma holdN_sp : ltac2:(tb__ "0|0|
S69S116S85S5dZ1000A1S61PaA1A2A2").
Proof using Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth. pose proof sp0_range4 as SPR. zfact. rewrite zeN_10. rewrite (Z.mod_small sp0) by lia. change (4096 mod 2 ^ 64) with 4096. lia. Qed.
Lemma holdN_13 : ltac2:(tb__ "0|0|
S69S116S85SdfPdA1S5dZ1fA1A2A2").
Proof using HMI HP13 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. pose proof R_all as RA. zfact. rewrite zeN_13. change (31 mod 2 ^ 64) with 31. lia. Qed.
Lemma holdN_fm (fm : sptr) : ltac2:(tb__ "0|0|
S0S44ScA1S14Vt4;A1S47ScVfm;A2A3S69S116S7aS67S1c2SdfPa0A1S5dZ0A1A3A1A2F_;").
Proof using HMI4 HXz4 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hfh. pose proof (key_range4 _ fmQ4_key) as KR. pose proof (ceiling_small L) as CS. zfact. rewrite zeN_160.
  change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq (addr_of L fmQ4) 0)) by lia. discriminate.
Qed.
Lemma holdN_fmft : ltac2:(tb__ "0|0|
S0S48S11eU2A3S69S116S7aS67S1c2SdfPa0A1SdfPa1A1A3A1A2F_;").
Proof using HMI4 HXz4 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hf2. pose proof (ceiling_small L) as CS.
  destruct ring4_cases as [(E & _)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & _ & Nfm & Nhp & Kfm & Khp & _)]; [unfold fshape4 in Hf2; rewrite E in Hf2; discriminate|].
  assert (NE : ftQ4 <> fmQ4) by (unfold fshape4 in Hf2; rewrite E in Hf2; destruct (sptr_eqb ftQ4 fmQ4) eqn:Eb; [discriminate | apply sptr_eqb_neq in Eb; exact Eb]).
  zfact. rewrite zeN_160, zeN_161. unfold zFp4. rewrite EL. cbn [fst optrA]. rewrite Efm. rewrite Efm, Eft in NE.
  pose proof (keys_apart4 hp fm Khp Kfm NE). rewrite (proj2 (Z.eqb_neq (addr_of L fm) (addr_of L hp))) by lia. discriminate.
Qed.
Lemma facts_Sh4 : ltac2:(tb__ "0|0|
S177S60S69S116A1S18aS11eA1A3").
Proof using HMI HMI4 HP12 HP13 HXz4 Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsm_pre Hsp Hu. try clear Hsp_high.
  pose proof holdN_align12 as A12. pose proof holdN_g1 as G1. pose proof holdN_g2 as G2. pose proof holdN_sp as SP. pose proof holdN_13 as I13.
  pose proof holdN_P1 as P1. pose proof holdN_P3 as P3. pose proof holdN_P4 as P4.
  unfold fshape4 in *. destruct (st_free_meta_head t4) as [fm|] eqn:Hfh.
  - pose proof (holdN_fm fm Hfh) as FM. destruct (sptr_eqb ftQ4 fmQ4) eqn:Eb.
    + cbn [facts_t2]. repeat (constructor; [assumption|]). constructor.
    + pose proof (holdN_fmft ltac:(unfold fshape4; rewrite Hfh, Eb; reflexivity)) as FT. cbn [facts_t2]. repeat (constructor; [assumption|]). constructor.
  - cbn [facts_t2]. repeat (constructor; [assumption|]). constructor.
Qed.

Lemma smatch_Sh4 : ltac2:(tb__ "0|0|
S66S55S116S11aS11eA1S49S4aS12aA1S173Vtr;S174VmsL;Vmd;A2A4A4").
Proof using HMI HMI4 HP12 HP13 HXz4 Hdepth Hgd HrL10 HrL11 HrL110 HrL111 HrL15 HrL28 HrL29 HrL38 HrL39 HrLf HrLlow Hres Hres64 Hres_r Hsc48 HsmL Hsm_pre Hsp Hsp_high Hstk Hu.
  pose proof HsmL as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & (HallX & HpdX & HfrX) & HfaX).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact (Sh4_swf fshape4 fshape4_le)|].
  split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split; [exact (regs_Sh4 fshape4)|].
  split.
  {
    intros r. rewrite (Hf r). assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; lia).
    unfold freg_sv, Sh4. cbn [ss_fregs L_nt].
    destruct (pre_freg_tableN (bv_unsigned r) ltac:(lia)) as (vv & E1 & R1 & R2). rewrite E1. cbn [eval rhoN rw]. rewrite (HrLf vv) by lia. rewrite (rwN_low vv) by lia. reflexivity. }
  split; [exact Hc|]. split; [exact Hv|].
  split.
  { split; [constructor; [exact hold_stk4 | constructor]|]. split; [cbn; split; [constructor | exact I]|].
    intros a Ha. cbn [rm rhoN]. apply stk_frame4. intros R.
    apply Forall_cons_iff in Ha as [HaS _]. cbn zeta in HaS. unfold obj_range, obj_lo_of, obj_hi_of, o_stk_saved in HaS. cbn [ob_base ob_lo ob_hi fst snd] in HaS.
    rewrite evN_10, soffN_15, soff_lit_small in HaS by lia. pose proof D0_range4. lia. }
  exact facts_Sh4.
Qed.

End PhaseF.
End V.
End Mal_nt_V8.

Module Mal_nt_V9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition L_t2n (f : nat) : list leaf := ltac2:(tb__ "0|1|
S48S4aS111A1M0Lf;Vf;S186S48S48G0Ln;R1S187S48S188Ln0;X48x2Ln;X48x2").
Lemma run_t2n0 : ltac2:(tb__ "0|1|
S0S44S4aS111A1M0A1S112S55U12cS180S17fU0A1S46A5S47G0S186A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some L_t2n0)). Qed.
Lemma run_t2n1 : ltac2:(tb__ "0|1|
S0S44S4aS111A1M0A1S112S55U12cS180S17fU1A1S46A5S47G0S187A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some L_t2n1)). Qed.
Lemma run_t2n2 : ltac2:(tb__ "0|1|
S0S44S4aS111A1M0A1S112S55U12cS180S17fU2A1S46A5S47G0S188A2A3"). Proof. vm_cast_no_check (@eq_refl (option (list leaf)) (Some L_t2n2)). Qed.
Lemma run_t2n f : ltac2:(tb__ "0|1|
S17aVf;U2A2S0S44S4aS111A1M0A1S112S55U12cS180S17fVf;A1S46A5S47G0S20cVf;A1A2A3F_;").
Proof. intros Hf. destruct f as [|[|[|f]]]; [exact run_t2n0 | exact run_t2n1 | exact run_t2n2 | lia]. Qed.
Lemma L_t2n_len f : length (L_t2n f) = 1%nat. Proof. destruct f as [|[|f]]; reflexivity. Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S196Se1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;S13fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SefVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§2§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§2§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§2§ U.Mal_nt__G1.Mal_nt_I.HL).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PcA2A2Se0VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation Hres := (@U.Mal_nt__G1.Mal_nt_I.Hres s L X U g am i vm rd0 wok0 HMI Hu).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§3§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§3§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§3§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§3§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation frPar := (§3§ U.Mal_nt__G1.Mal_nt_I.frPar).
Local Abbreviation rho1 := (@U.Mal_nt__G1.Mal_nt_I.rho1 s L g am i rho gd rd0).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S34Z1000Sa2Q40S5cVrho;PaA2A2M0A2S0S8S3aG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S34S10aZ40Sa2Q40S5cVrho;PfA2A2A2M0N60A2S34S3cS37Z2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;Vrd0;S106S55VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sa0Q40A1S45F_;Vwok0;S107S55VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1Z60A2A2S0S44Sa0Q8A1M0A1VmV;Sa1Q40S35Z108ecR2A2A2A1S4eG0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Se4Se2Vrd0;Sa0Q40A1S46L_;A2Se5Se1A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Se2S106S55VmV;A2S107S55VmV;A2A2").
Local Abbreviation ctx_owned := (@U.Mal_nt__G1.Mal_nt_Ib.ctx_owned s L X U g i rho gd vm rd0 wok0 HMI HXz Hgd Hsp).
Local Abbreviation cellZ_optr := (@U.Mal_nt__G1.Mal_nt_Ib.cellZ_optr L).
Local Abbreviation O_fmh := (@U.Mal_nt__G1.Mal_nt_Ib.O_fmh).
Local Abbreviation free_cells := (@U.Mal_nt__G1.Mal_nt_Ib.free_cells).
Local Abbreviation O_freeK := (@U.Mal_nt__G1.Mal_nt_Ib.O_freeK).
Local Abbreviation AGq := (@U.Mal_nt__G1.Mal_nt_Ic.AGq L rho gd Hgd).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S152VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Notation "§4§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation g_zone := (§4§ U.Mal_nt__G2.Mal_nt_Z.g_zone).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S34Se3VL;A1S35S14dVrho;A1S14cVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S4aS12aA1S12bOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1e9S55VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
SddVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1eeS55VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
SddSddSddVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1f0S55VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSddSddR3VTR;R3R2A2F_;VTR;SdeS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1edS55VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
SddSddSddSddSdeR4R1A1M0R6R2A1F_;Fw;SdeG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1eaS55VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
SddSddSdeR3R1A1VTR;SdeS0SdeR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1ecS55VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
SddSddSddVTR;R3R1A2VTR;R3R2A2VTR;SdeS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1ebS55VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1cbVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sf1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;Vsr;A4").
Local Abbreviation Hzs_eq := (@U.Mal_nt__G2.Mal_nt_W.Hzs_eq s X sr Hzs).
Local Abbreviation Hur := (@U.Mal_nt__G2.Mal_nt_W.Hur s X g am Hu sr Hzs).
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrho;PdA2Sa1G0Vi;A2A3").
Local Abbreviation svl_eqb := (@U.Mal_nt__G2.Mal_nt_V3.svl_eqb).
Local Abbreviation svl_eqb_sound := (@U.Mal_nt__G2.Mal_nt_V3.svl_eqb_sound).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis HKc : ltac2:(tb__ "0|1|
S4aS12aA1M0S12bVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S12bR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S66S55Vrho;S155S151A1S49S4aS12aA1S173Vtr;S174Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S8S34Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S4bS44ScA1M0G0A2S49G0G0S18Vam;A1S13Vam;A1A4S49G0G0S4eScA1M1G1A4A3A1S2S0G0SeeVs;SfVam;A1A2S47ScVg;A2A3A1S2S0S8S16Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S8S35S167Vam;A1S1bVi;A1A2S1cS12Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Notation "§5§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation HnU3 := (§5§ U.Mal_nt__G3.Mal_nt_V4.HnU3).
Local Abbreviation HpU3 := (§5§ U.Mal_nt__G3.Mal_nt_V4.HpU3).
Local Abbreviation Hlinks3 := (§4§ U.Mal_nt__G3.Mal_nt_V4.Hlinks3).
Hypothesis Hml0 : am_maplen am = 0.
Local Notation "§6§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hml0) (at level 10, h__ global).
Local Abbreviation HuP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HuP).
Local Abbreviation HiP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HiP).
Local Abbreviation HfrP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HfrP).
Local Abbreviation HkP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HkP).
Local Abbreviation HmemP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HmemP).
Local Abbreviation HscP := (§6§ U.Mal_nt__G3.Mal_nt_V7.HscP).
Local Abbreviation HallN := (@U.Mal_nt__G3.Mal_nt_V7.HallN am i Hall).
Local Abbreviation Hsc48am := (@U.Mal_nt__G3.Mal_nt_V7.Hsc48am am Hsc48).
Local Abbreviation s3v := (§3§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation Hact3' := (@U.Mal_nt__G3.Mal_nt_V7.Hact3' s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48).
Local Abbreviation HactU3' := (§4§ U.Mal_nt__G3.Mal_nt_V7.HactU3').
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).
Local Abbreviation ntf_nested := (@U.Mal_nt__G3.Mal_nt_V7.ntf_nested s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd sr Hzs HIr HU HR2g Hall Hsc48 Hml0).
Local Abbreviation fneed_par := (@U.Mal_nt__G3.Mal_nt_V7.fneed_par s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp Hsc48 Hml0).
Local Abbreviation ub3v := (@U.Mal_nt__G3.Mal_nt_V7.ub3v s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HU HR2g Hall Hsc48 Hml0).
Section PhaseF.
Variables (rhoL : valuation) (msL : machine_state) (t4 : astate) (mv4 : word -> option byte) (rbase rlen : Z).
Hypothesis HsmL : ltac2:(tb__ "0|0|
S66S55VrhoL;S156S151A1S49S4aS12aA1S173Vtr;S174VmsL;Vmd;A2A4A4").
Hypothesis HMI4 : ltac2:(tb__ "0|0|
S196Se1S43ScVg;VX;A3S4eS4bScS8A2A1VU;S13fVt4;VL;A2S106S55Vmv4;A2S107S55Vmv4;A2Vvm;A8").
Hypothesis HZ4 : ltac2:(tb__ "0|0|
S152VL;S43ScVg;VX;A3Vmv4;S5fVrhoL;A1A4").
Hypothesis HXz4 : ltac2:(tb__ "0|0|
S158S43ScVg;VX;A3Vt4;A2").
Hypothesis Cr4 : ltac2:(tb__ "0|0|
S1f1S43ScVg;VX;A3S143Vs;Vg;Vam;A3Vt4;A3").
Hypothesis UB4 : ub_same s3v t4.
Hypothesis Hreach4 : reach_ok t4.
Hypothesis Hres : ltac2:(tb__ "0|1|
S4S1S0S8Vrlen;Z0M0A3S0S8Vrbase;G0A3A2S1S36G0Vrlen;A2S3S48S48S3SeSeS1S0S44SeA1Sf5Vt4;R2A2S47SeR1A2A3S1S0S22S1fR1A1S19A3S1S0S45S21R1A1S46A3S1S0S8S20R1A1S1dVrlen;A1A3S1S0S8Sf8VL;R2A2Vrbase;A3ScS15SefS43ScVg;VX;A3Vt4;R2R1A4S36G0S17R2A1A2S2S0S48S1eS1aR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2Lrg;A2Lk;A2A2A2").
Hypothesis Hres64 : ltac2:(tb__ "0|2|
S1S1S34Z0M0Vrbase;A2S36Vrbase;S37Z2Z40A2M1A2A2S1S34G0Vrlen;A2S36Vrlen;G1A2A2A2").
Hypothesis HrL10 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;PaA2Sa1G0S38S14dVrho;A1Z60A2A2A3").
Hypothesis HrL15 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrhoL;PfA2A2S3aS35S14cVrho;A1Z60A2S37Z2Z40A2A2A3").
Hypothesis HrL11 : rw rhoL 11%positive = Z_to_bv 64 0x20ad4.
Hypothesis HrL28 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P1cA2Sa1G0S166VL;Vam;A2A2A3").
Hypothesis HrL29 : rw rhoL 29%positive = Z_to_bv 64 0x5a338.
Hypothesis HrL38 : rw rhoL 38%positive = Z_to_bv 64 0x5a3d0.
Hypothesis HrL39 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P27A2Sa1G0S15dVL;Vg;A2A2A3").
Hypothesis HrLlow : ltac2:(tb__ "0|0|
S9S9aS9R1S43S9P17S43S9P18S43S9P28S43S9P29S43S9P2aS43S9P2bS43S9P2cS43S9P2dS43S9P2eS43S9P2fS4fS9A1A3A3A3A3A3A3A3A3A3A3A3S0Sa0Q40A1S5cVrhoL;R2A2S5cVrho;R2A2A3F_;Fj;").
Hypothesis HrLf : ltac2:(tb__ "0|0|
S9S1S199P3cR1A2S19aR1P5cA2A2S0Sa0Q40A1S5cVrhoL;R2A2S5cVrho;R2A2A3F_;Fj;").
Hypothesis HrL110 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P6eA2Sa1G0Vrbase;A2A3").
Hypothesis HrL111 : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrhoL;P6fA2Sa1G0Vrlen;A2A3").
Local Abbreviation o_stk_top := (@U.Mal_nt__G5.Mal_nt_V8.o_stk_top).
Hypothesis Hstk : ltac2:(tb__ "0|0|
S64S55VrhoW;S17cVmsL;S5fVrhoL;A1A2S134A4").
Hypothesis Hkept4 : ltac2:(tb__ "0|2|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2S2S140Se1S13fVs;VL;A2R2A3A1S2S140Se1S13fVt4;VL;A2R3A3A1S2S1feSe1R4A2A1S2S1fdSe1R5A2A1S2S1S34S38S14dVrho;A1M0Z60A2R6A2S36R6G0A2A2A1S0S44Sa0Q8A1A1S5fVrhoL;Sa1Q40R7A2M1A2S5fVrho;G1A2A3F_;F_;F_;F_;F_;F_;Fa;").
Hypothesis Hcanary4 : ltac2:(tb__ "0|0|
S1e8S55Se1S5fVrho;A1S5fVrhoL;A1A4").
Hypothesis HK4 : K tr md.
Variables (t4r : astate) (r4 : option (nat * Z)).
Hypothesis Hz4 : ltac2:(tb__ "0|0|
S1cbS43ScVg;VX;A3Vt4r;Vt4;A3").
Hypothesis HI4r : ltac2:(tb__ "0|0|
Sf1S43ScVg;VX;A3S4eS4bScS8A2A1VU;Vt4r;A4").
Hypothesis Hres_r : ltac2:(tb__ "0|4|
S4S1S0S44S4bS48S8A2M0A1M1Vr4;S4eG0A1A3S1S0S8Vrlen;Z0M2A3S0S8Vrbase;G2A3A2A2S3S48S48S3SeSeS1S0G1Vr4;S47G0S49S48S8R2S20R1A1M3A4A2A3S1S36G2Vrlen;A2S1S0S44SeA1Sf5Vt4r;R2A2S47SeR1A2A3S1S0S22S1fR1A1S19A3S1S0S45S21R1A1S46A3S1S0S8G3S1dVrlen;A1A3S1S0S8Sf8VL;R2A2Vrbase;A3ScS15SefS43ScVg;VX;A3Vt4r;R2R1A4S36G2S17R2A1A2S2S0S48S1eS1aR3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2A2A2Lrg;A2Lk;A2A2").
Hypothesis Heq4 : ltac2:(tb__ "0|2|
S48S17aS1f2SfS162Vs;Vg;Vam;A3A1A1R1A2S0S27S10S4bS44S4bS48S8A2A1M0S10A2M1A2S28R2S161Vs;Vg;Vam;A3S163Vs;Vg;Vam;A3S145Vs;Vg;Vam;Vsr;A4A4S25S10G1S49G0S10Vr4;Vt4r;A4A3A3F_;FF;").
Hypothesis Hxk4 : ltac2:(tb__ "0|0|
ScS9aScR1S43ScVg;VX;A3A3S0S44SdA1SebVt4r;R2A2SebS145Vs;Vg;Vam;Vsr;A4R2A2A3F_;Fx;").
Local Notation "§7§ h__" := (h__ L X U g vm t4 mv4 HMI4) (at level 10, h__ global).
Local Abbreviation HI4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.HI4).
Local Notation "§8§ h__" := (h__ X g t4 HXz4) (at level 10, h__ global).
Local Abbreviation HXr4 := (§8§ U.Mal_nt__G5.Mal_nt_V8.HXr4).
Local Abbreviation HL4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.HL4).
Local Abbreviation HV4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.HV4).
Local Abbreviation HLG4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.HLG4).
Local Abbreviation Hctx4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.Hctx4).
Local Abbreviation ND4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.ND4).
Local Abbreviation Mg4 := (§8§ U.Mal_nt__G5.Mal_nt_V8.Mg4).
Local Abbreviation Kg4 := (§8§ U.Mal_nt__G5.Mal_nt_V8.Kg4).
Local Notation "§9§ h__" := (h__ L X U g am rho gd vm Hgd Hsc48 t4 mv4 HMI4) (at level 10, h__ global).
Local Abbreviation key_range4 := (§9§ U.Mal_nt__G5.Mal_nt_V8.key_range4).
Local Abbreviation keys_apart4 := (§9§ U.Mal_nt__G5.Mal_nt_V8.keys_apart4).
Local Abbreviation key_zone4 := (§9§ U.Mal_nt__G5.Mal_nt_V8.key_zone4).
Local Notation "§10§ h__" := (h__ g t4) (at level 10, h__ global).
Local Abbreviation fmQ4 := (§10§ U.Mal_nt__G5.Mal_nt_V8.fmQ4).
Local Abbreviation fmL4 := (§10§ U.Mal_nt__G5.Mal_nt_V8.fmL4).
Local Abbreviation ftQ4 := (§10§ U.Mal_nt__G5.Mal_nt_V8.ftQ4).
Local Abbreviation ftL4 := (§10§ U.Mal_nt__G5.Mal_nt_V8.ftL4).
Local Abbreviation zF4 := (@U.Mal_nt__G5.Mal_nt_V8.zF4 L t4).
Local Notation "§11§ h__" := (h__ L g t4) (at level 10, h__ global).
Local Abbreviation zFp4 := (§11§ U.Mal_nt__G5.Mal_nt_V8.zFp4).
Local Abbreviation zFn4 := (§11§ U.Mal_nt__G5.Mal_nt_V8.zFn4).
Local Abbreviation zTTp4 := (§11§ U.Mal_nt__G5.Mal_nt_V8.zTTp4).
Local Abbreviation zTTn4 := (§11§ U.Mal_nt__G5.Mal_nt_V8.zTTn4).
Local Abbreviation fshape4 := (§10§ U.Mal_nt__G5.Mal_nt_V8.fshape4).
Local Notation "§12§ h__" := (h__ L X U g vm t4 mv4 HMI4 HXz4) (at level 10, h__ global).
Local Abbreviation ring4_cases := (§12§ U.Mal_nt__G5.Mal_nt_V8.ring4_cases).
Local Abbreviation zFp4_range := (@U.Mal_nt__G5.Mal_nt_V8.zFp4_range L X U g am rho gd vm Hgd Hsc48 t4 mv4 HMI4 HXz4).
Local Notation "§13§ h__" := (h__ L g am rho gd rhoL msL t4 rbase rlen) (at level 10, h__ global).
Local Abbreviation rhoN := (§13§ U.Mal_nt__G5.Mal_nt_V8.rhoN).
Local Abbreviation zrN := (§13§ U.Mal_nt__G5.Mal_nt_V8.zrN).
Local Abbreviation zlN := (§13§ U.Mal_nt__G5.Mal_nt_V8.zlN).
Local Abbreviation rwN_low := (@U.Mal_nt__G5.Mal_nt_V8.rwN_low L g am rho gd Hgd Hsp Hsc48 msL t4 rbase rlen).
Local Abbreviation fmQ4_key := (§12§ U.Mal_nt__G5.Mal_nt_V8.fmQ4_key).
Local Notation "§14§ h__" := (h__ L X U g am rho gd vm Hgd Hsp Hsc48 rhoL msL t4 mv4 rbase rlen HMI4 HXz4) (at level 10, h__ global).
Local Abbreviation zeN_160 := (§14§ U.Mal_nt__G5.Mal_nt_V8.zeN_160).
Local Abbreviation zeN_161 := (§14§ U.Mal_nt__G5.Mal_nt_V8.zeN_161).
Local Abbreviation zeN_162 := (§14§ U.Mal_nt__G5.Mal_nt_V8.zeN_162).
Local Abbreviation zeN_163 := (§14§ U.Mal_nt__G5.Mal_nt_V8.zeN_163).
Local Abbreviation zeN_164 := (§14§ U.Mal_nt__G5.Mal_nt_V8.zeN_164).
Local Abbreviation zeN_180 := (@U.Mal_nt__G5.Mal_nt_V8.zeN_180 L g am rho gd Hgd Hsc48 rhoL msL t4 rbase rlen Hres64).
Local Abbreviation zeN_181 := (@U.Mal_nt__G5.Mal_nt_V8.zeN_181 L X g am rho gd Hgd Hsc48 rhoL msL t4 rbase rlen Hres Hres64).
Local Abbreviation zeN_12 := (@U.Mal_nt__G5.Mal_nt_V8.zeN_12 L g am rho gd Hgd HP12 Hsp Hsc48 rhoL msL t4 rbase rlen).
Local Abbreviation evNu := (§13§ U.Mal_nt__G5.Mal_nt_V8.evNu).
Local Abbreviation zeNv := (§13§ U.Mal_nt__G5.Mal_nt_V8.zeNv).
Let bv4 : byteview := ltac2:(tb__ "0|0|
Se2S106S55Vmv4;A2S107S55Vmv4;A2A2").
Local Abbreviation hold_fmh4 := (@U.Mal_nt__G5.Mal_nt_V8.hold_fmh4 L X U g am rho gd vm Hgd Hsp Hdepth tr md Hsc48 rhoL msL t4 mv4 rbase rlen HsmL HMI4 Hres Hres64 t4r r4 Hres_r).
Local Abbreviation hold_freeK4 := (@U.Mal_nt__G5.Mal_nt_V8.hold_freeK4 L X U g am rho gd vm Hgd Hsp tr md Hsc48 rhoL msL t4 mv4 rbase rlen HsmL HMI4).
Local Abbreviation O_graw := (@U.Mal_nt__G5.Mal_nt_V8.O_graw).
Local Abbreviation hold_graw4 := (@U.Mal_nt__G5.Mal_nt_V8.hold_graw4 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp tr md Hsc48 rhoL msL t4 mv4 rbase rlen HsmL HMI4 HZ4 HXz4).
Local Abbreviation hold_guard4 := (@U.Mal_nt__G5.Mal_nt_V8.hold_guard4 L X U g am rho gd vm rd0 Hgd Hsp mV Erd Hgd_holds mW HZ tr md EmW Hsc48 rhoL msL t4 mv4 rbase rlen HsmL HMI4 Hcanary4).
Local Abbreviation HZ4_at := (@U.Mal_nt__G5.Mal_nt_V8.HZ4_at L X g am rho gd Hgd Hsc48 rhoL mv4 HZ4).
Local Abbreviation hold_real4 := (@U.Mal_nt__G5.Mal_nt_V8.hold_real4 L X g am rho gd Hgd Hsp Hsc48 rhoL msL t4 mv4 rbase rlen HZ4).
Local Abbreviation XS_key4 := (§7§ U.Mal_nt__G5.Mal_nt_V8.XS_key4).
Local Abbreviation XS_free := (§8§ U.Mal_nt__G5.Mal_nt_V8.XS_free).
Local Abbreviation sp0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.sp0_range4 am rho gd Hgd Hsp Hsc48).
Local Abbreviation D0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.D0_range4 am rho gd Hgd Hdepth Hsc48).
Local Notation "§15§ h__" := (h__ L g am rho gd Hgd Hsp Hsc48 rhoL msL t4 rbase rlen) (at level 10, h__ global).
Local Abbreviation evN_10 := (§15§ U.Mal_nt__G5.Mal_nt_V8.evN_10).
Local Abbreviation soffN_15 := (§15§ U.Mal_nt__G5.Mal_nt_V8.soffN_15).
Local Abbreviation N4 := (@U.Mal_nt__G5.Mal_nt_V8.N4).
Local Abbreviation Sh4 := (@U.Mal_nt__G5.Mal_nt_V8.Sh4).
Local Abbreviation S_t2n_eq := (@U.Mal_nt__G5.Mal_nt_V8.S_t2n_eq).
Local Abbreviation S_t2n_swf := (@U.Mal_nt__G5.Mal_nt_V8.S_t2n_swf).
Local Abbreviation fshape4_le := (@U.Mal_nt__G5.Mal_nt_V8.fshape4_le g am rho gd Hgd Hsc48 t4).
Local Notation "§16§ h__" := (h__ am rho gd Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation reg_sv_Lnt := (§16§ U.Mal_nt__G5.Mal_nt_V8.reg_sv_Lnt).
Local Abbreviation pre_freg_tableN := (§16§ U.Mal_nt__G5.Mal_nt_V8.pre_freg_tableN).
Local Abbreviation smatch_Sh4 := (@U.Mal_nt__G5.Mal_nt_V8.smatch_Sh4 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 HP13 Hsp Hdepth ms mW Hsp_high tr md Hsm_pre Hsc48 rhoL msL t4 mv4 rbase rlen HsmL HMI4 HXz4 Hres Hres64 HrL10 HrL15 HrL11 HrL28 HrL29 HrL38 HrL39 HrLlow HrLf HrL110 HrL111 Hstk t4r r4 Hres_r).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Ltac flia := first [ let H := fresh "FL" in pose proof I as H; clear - H; top_ranges; solve [lia] | lia ].

Ltac zfact := match goal with |- SymState.holds _ ?p => apply (proj2 (holds_zholds rhoN p eq_refl)) end; cbn [zholds zeval zcond]; fold zrN; fold zlN; rewrite ?zeNv.
Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).

Lemma rng_graw : ltac2:(tb__ "0|1|
S0S4bS8S8A2S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS137A2S49S8S8S15dVL;Vg;A2M0S35G0Z28A2A4A3").
Proof using HP12 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  unfold obj_range, obj_lo_of, obj_hi_of, O_graw. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by flia.
  rewrite (evNu (v 12) eq_refl), zeNv, zeN_12. f_equal; flia.
Qed.
Lemma rng_guard : ltac2:(tb__ "0|1|
S0S4bS8S8A2S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS181A2S49S8S8Z5a338M0S35G0Z8A2A4A3").
Proof using . drop_sp. unfold obj_range, obj_lo_of, obj_hi_of, O_guard_. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by flia. rewrite u64 by flia. f_equal; flia. Qed.
Lemma rng_fmh x : ltac2:(tb__ "0|1|
S0S4bS8S8A2S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS1cdVx;A1A2S49S8S8S35Z5a3d0M0Z10A2S35G0Z18A2A4A3").
Proof using . drop_sp. unfold obj_range, obj_lo_of, obj_hi_of, O_fmh, U.Mal_nt__G1.Mal_nt_Ib.O_fmh. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by flia. rewrite u64 by flia. f_equal; flia. Qed.
Lemma rng_freeK bv five pv nv : ltac2:(tb__ "0|1|
S0S45S109Vbv;A1S46A3S0S4bS8S8A2S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS1ccVbv;Vfive;Vpv;Vnv;A4A2S49S8S8S108S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaVbv;A3M0S35G0Z28A2A4A3F_;").
Proof using . drop_sp.
  intros Sb. unfold obj_range, obj_lo_of, obj_hi_of, O_freeK, U.Mal_nt__G1.Mal_nt_Ib.O_freeK, carved. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by flia.
  rewrite (evNu bv Sb). f_equal; flia.
Qed.
Lemma rng_stk4 : ltac2:(tb__ "0|1|
S0S4bS8S8A2S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS17eA2S49S8S8S35S14dVrho;A1M0S14cVrho;A1A2G0A4A3").
Proof using Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  unfold obj_range, obj_lo_of, obj_hi_of, o_stk_saved. cbn [ob_base ob_lo ob_hi]. rewrite evN_10, soffN_15, soff_lit_small by flia. f_equal; flia.
Qed.

Lemma fshape4_cases : ltac2:(tb__ "0|d|
S4S1S0S48S131Vg;Vt4;A2M0U0A3S1S0S44ScA1M1S14Vt4;A1M2S4eScA1A3S1S0ScS133Vg;Vt4;A2M3Vg;A3S0S8S13bVL;Vt4;A2M4Z0A3A2A2A2S3ScScS3ScScS3ScScS3ScScS3ScScS1S0G1G2S47ScR5A2A3S1S0ScG3R5A3S1S0S44SdA1M5SebVt4;R5A2S47SdS11S47ScR4A2M6S47ScR3A2M7A2A2A3S1S0S4bG1G1A2M8S139Vg;Vt4;A2S49G1G1G6G7A4A3S1S0ScS135Vg;Vt4;A2R4A3S1S0G5SebVt4;R4A2S47SdS11S47ScR2A2M9S47ScR1A2MaA2A2A3S1S0G8S13aVg;Vt4;A2S49G1G1G9GaA4A3S1S2S0ScR5Vg;A3A1S1S2S0ScR4Vg;A3A1S1S9aScR5SedVt4;A1MbA3S1S9aScR4GbA3S1S9aScR3GbA3S1S9aScR2GbA3S1S9aScR1GbA3S1S0S8G4Se0VL;R5A2A3S1S0S8S136VL;Vg;Vt4;A3Se0VL;R4A2A3S1S0S8S13cVL;Vg;Vt4;A3Se0VL;R3A2A3S1S0S8S13eVL;Vg;Vt4;A3Se0VL;R2A2A3S1S0S8S13dVL;Vg;Vt4;A3Se0VL;R1A2A3S4S1S0S48G0U1A3S0ScR4R5A3McA2S1S0S48G0U2A3S2GcA1A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2Lfm;A2A2").
Proof using HMI4 HXz4. drop_sp.
  destruct ring4_cases as [(E & Efm & EL & Eft & ELt)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2)].
  - left. unfold fshape4, zF4. rewrite E. cbn [optrA]. auto.
  - right. exists fm, hp, nx, pr2, nx2.
    assert (SH : (fshape4 = 1%nat /\ hp = fm) \/ (fshape4 = 2%nat /\ hp <> fm)).
    { unfold fshape4. rewrite E. rewrite Eft, Efm. destruct (sptr_eqb hp fm) eqn:Eb; [left; split; [reflexivity | apply sptr_eqb_eq; exact Eb] | right; split; [reflexivity | apply sptr_eqb_neq in Eb; exact Eb]]. }
    unfold zF4, zFp4, zFn4, zTTp4, zTTn4. rewrite E, EL, ELt. cbn [fst snd optrA]. repeat (split; [assumption || reflexivity|]). exact SH.
Qed.

Lemma XS_apart q pr nx : ltac2:(tb__ "0|5|
S9aScVq;SedVt4;A1A3S0S44SdA1SebVt4;Vq;A2S47SdS11Vpr;Vnx;A2A2A3S2S0S4bS44ScA1M0G0A2S49G0G0Vpr;Vnx;A4S49G0G0S4eScA1M1G1A4A3A1ScS9aScR1S43ScVg;VX;A3A3S4S34S35Se0VL;Vq;A2M2Z28M3A2Se0VL;R2A2M4A2S34S35G4G3A2G2A2A2F_;Fx;F_;F_;F_;").
Proof using HMI4 HXz4 Hgd Hsc48 rho. drop_sp.
  intros Kq Mq NE x Hx. apply (keys_apart4 q x Kq (XS_key4 x Hx)). intros ->. rewrite (XS_free x Hx) in Mq. injection Mq as <- <-. exact (NE eq_refl).
Qed.

Lemma N4_holds : ltac2:(tb__ "0|0|
S177S5bS64S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS17cVmsL;S5fVrhoL;A1A2A3S132S131Vg;Vt4;A2A1A3").
Proof using EmW Erd HMI HMI4 HP12 HXz4 HZ HZ4 Hcanary4 Hdepth Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmL Hsp Hu. try clear Hsp_high.
  pose proof hold_graw4 as HG. pose proof hold_guard4 as HGU. pose proof (ceiling_small L) as CS.
  destruct fshape4_cases as [(EF & E & Efm & EzF)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2 & EzF & EzFp & EzFn & EzTp & EzTn & SH)].
  - rewrite EF. cbn [N4]. constructor; [exact HG|]. constructor; [exact HGU|]. constructor; [|constructor].
    apply (hold_real4 _ _ _ (rng_fmh (SLit 0))).
    + intros x Hx. pose proof (key_zone4 x (XS_key4 x Hx)). flia.
    + apply hold_fmh4; [reflexivity|]. rewrite EzF. reflexivity.
  - assert (Hfmh : obj_holds segsU rhoN (with_mem msL (rm rhoL)) (O_fmh (v 160))).
    { apply (hold_real4 _ _ _ (rng_fmh (v 160))).
      + intros x Hx. pose proof (key_zone4 x (XS_key4 x Hx)). flia.
      + apply hold_fmh4; [reflexivity|]. rewrite zeNv, zeN_160, Efm, EzF. reflexivity. }
    assert (Hfm : forall pvv, zeval zrN zlN pvv = addr_of L hp -> zsupported pvv = true ->
              obj_holds segsU rhoN (with_mem msL (rm rhoL)) (O_freeK (v 160) false pvv (v 162))).
    { intros pvv Epv Spv. apply (hold_real4 _ _ _ (rng_freeK (v 160) false pvv (v 162) eq_refl)).
      + rewrite zeNv, zeN_160, Efm. apply (XS_apart fm _ _ Kfm Mfm). intros EE. discriminate EE.
      + apply (hold_freeK4 fm (Some hp) (Some nx) (v 160) false pvv (v 162) Mfm Kfm);
          [intros p Hp; injection Hp as <-; exact Khp | intros p Hp; injection Hp as <-; exact Knx | reflexivity | exact Spv | reflexivity
          | rewrite zeNv, zeN_160, Efm; reflexivity | rewrite Epv; reflexivity | rewrite zeNv, zeN_162, EzFn; reflexivity]. }
    destruct SH as [[EF Ehp]|[EF Nhf]]; rewrite EF; cbn [N4].
    + constructor; [exact HG|]. constructor; [exact HGU|]. constructor; [exact Hfmh|]. constructor; [|constructor].
      apply Hfm; [|reflexivity]. rewrite zeNv, zeN_160, Efm, Ehp. reflexivity.
    + constructor; [exact HG|]. constructor; [exact HGU|]. constructor; [exact Hfmh|]. constructor; [apply Hfm; [rewrite zeNv, zeN_161, EzFp; reflexivity | reflexivity]|].
      constructor; [|constructor].
      apply (hold_real4 _ _ _ (rng_freeK (v 161) false (v 163) (v 164) eq_refl)).
      * rewrite zeNv, zeN_161, EzFp. apply (XS_apart hp _ _ Khp Mhp). intros EE. discriminate EE.
      * apply (hold_freeK4 hp (Some pr2) (Some nx2) (v 161) false (v 163) (v 164) Mhp Khp);
          [intros p Hp; injection Hp as <-; exact Kpr2 | intros p Hp; injection Hp as <-; exact Knx2 | reflexivity | reflexivity | reflexivity
          | rewrite zeNv, zeN_161, EzFp; reflexivity | rewrite zeNv, zeN_163, EzTp; reflexivity | rewrite zeNv, zeN_164, EzTn; reflexivity].
Qed.

Lemma rd_sep a b c d : ltac2:(tb__ "0|0|
S4S34Vb;Vc;A2S34Vd;Va;A2A2S87S49S8S8Va;Vb;A4S49S8S8Vc;Vd;A4A2F_;").
Proof using Hgd Hsc48 rho. drop_sp. intros H. unfold SymState.ranges_disjoint. cbn [fst snd]. flia. Qed.
Lemma sep_g_guard : ltac2:(tb__ "0|2|
S4S34S35S15dVL;Vg;A2M0Z28A2Z5a338M1A2S34S35G1Z8A2G0A2A2").
Proof using HMI Hgd Hsc48 Hu rho. drop_sp. pose proof g_zone as (_ & _ & GZ & _). flia. Qed.
Lemma sep_g_ctx : ltac2:(tb__ "0|2|
S4S34S35S15dVL;Vg;A2M0Z28A2S35Z5a3d0M1Z10A2A2S34S35G1Z18A2G0A2A2").
Proof using HMI Hgd Hsc48 Hu rho. drop_sp. pose proof g_zone as (_ & _ & _ & GZ). flia. Qed.
Lemma sep_key_guard q : ltac2:(tb__ "0|2|
S9aScVq;SedVt4;A1A3S4S34S35Se0VL;Vq;A2M0Z28A2Z5a338M1A2S34S35G1Z8A2G0A2A2F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp. intros Kq. pose proof (key_zone4 q Kq) as (_ & _ & KZ & _). flia. Qed.
Lemma sep_key_ctx q : ltac2:(tb__ "0|2|
S9aScVq;SedVt4;A1A3S4S34S35Se0VL;Vq;A2M0Z28A2S35Z5a3d0M1Z10A2A2S34S35G1Z18A2G0A2A2F_;").
Proof using HMI4 Hgd Hsc48 rho. drop_sp. intros Kq. pose proof (key_zone4 q Kq) as (_ & _ & _ & KZ). flia. Qed.
Lemma key_below q : ltac2:(tb__ "0|0|
S9aScVq;SedVt4;A1A3S34S35Se0VL;Vq;A2Z28A2S35S14dVrho;A1S14cVrho;A1A2A2F_;").
Proof using HMI4 Hgd Hsc48 Hsp Hsp_high. try clear Hdepth. intros Kq. pose proof (key_range4 q Kq) as [_ KR]. pose proof Hsp_high. flia. Qed.
Lemma g_below : ltac2:(tb__ "0|0|
S34S35S15dVL;Vg;A2Z28A2S35S14dVrho;A1S14cVrho;A1A2A2").
Proof using HMI Hgd Hsc48 Hsp Hsp_high Hu. try clear Hdepth. pose proof g_zone as (_ & GZ & _). pose proof Hsp_high. flia. Qed.
Lemma statics_below : ltac2:(tb__ "0|0|
S34S35Z5a3d0Z18A2S35S14dVrho;A1S14cVrho;A1A2A2").
Proof using Hgd Hsc48 Hsp_high. try clear Hdepth. try clear Hsp. pose proof Hsp_high. pose proof (ceiling_small L). top_ranges. flia. Qed.

Ltac rd_solve := first [ assumption
                       | match goal with H : ?d <= ?a \/ ?b <= ?c |- ?b <= ?c \/ ?d <= ?a => destruct H as [H|H]; [right; exact H | left; exact H] end
                       | (left; cbv; discriminate) | (right; cbv; discriminate) ].
Ltac pw_split := repeat first [apply Forall_cons | apply Forall_nil | exact I | match goal with |- _ /\ _ => split end].
Ltac rng_rw := cbn beta; rewrite ?rng_stk4, ?rng_graw, ?rng_guard, ?rng_fmh, ?(rng_freeK (v 160) false (v 160) (v 162) eq_refl),
  ?(rng_freeK (v 160) false (v 161) (v 162) eq_refl), ?(rng_freeK (v 161) false (v 163) (v 164) eq_refl), ?zeNv, ?zeN_160, ?zeN_161.

Lemma N4_vs_stk : ltac2:(tb__ "0|2|
S177S5bS5bS177S5bS5bS87S6cS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaM0R1A2S6cG0R2A2A2Lo';S6bS138S131Vg;Vt4;A2M1A1A1A3Lo;S132G1A1A3").
Proof using HMI HMI4 HP12 HXz4 Hgd Hsc48 Hsp Hsp_high Hu. try clear Hdepth.
  change (ss_objs (Sh4 fshape4)) with [o_stk_saved].
  pose proof g_below as GB. pose proof statics_below as SB.
  destruct fshape4_cases as [(EF & E & Efm & EzF)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2 & EzF & EzFp & EzFn & EzTp & EzTn & SH)].
  - rewrite EF. cbn [N4]. pw_split; rng_rw; apply rd_sep; right; flia.
  - pose proof (key_below fm Kfm) as B1. pose proof (key_below hp Khp) as B2.
    destruct SH as [[EF Ehp]|[EF Nhf]]; rewrite EF; cbn [N4]; pw_split; rng_rw; rewrite ?Efm, ?EzFp; apply rd_sep; right; flia.
Qed.

Lemma N4_pw : ltac2:(tb__ "0|0|
S94S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS132S131Vg;Vt4;A2A1A2").
Proof using HMI HMI4 HP12 HXz4 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  pose proof sep_g_guard as S1. pose proof sep_g_ctx as S2.
  destruct fshape4_cases as [(EF & E & Efm & EzF)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2 & EzF & EzFp & EzFn & EzTp & EzTn & SH)].
  - rewrite EF. cbn [N4 pairwise_disjoint]. pw_split; rng_rw; apply rd_sep; rd_solve.
  - pose proof (keys_apart4 g fm Kg4 Kfm ltac:(intros EE; exact (Nfm (eq_sym EE)))) as A1.
    pose proof (keys_apart4 g hp Kg4 Khp ltac:(intros EE; exact (Nhp (eq_sym EE)))) as A2.
    pose proof (sep_key_guard fm Kfm) as G1. pose proof (sep_key_guard hp Khp) as G2.
    pose proof (sep_key_ctx fm Kfm) as C1. pose proof (sep_key_ctx hp Khp) as C2.
    destruct SH as [[EF Ehp]|[EF Nhf]]; [|pose proof (keys_apart4 fm hp Kfm Khp ltac:(intros EE; exact (Nhf (eq_sym EE)))) as A3];
      rewrite EF; cbn [N4 pairwise_disjoint]; pw_split; rng_rw; rewrite ?Efm, ?EzFp; apply rd_sep; rd_solve.
Qed.

Theorem instantiateF : ltac2:(tb__ "0|0|
S66S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS17fS131Vg;Vt4;A2A1S49S4aS12aA1S173Vtr;S174VmsL;Vmd;A2A4A4").
Proof using EmW Erd HMI HMI4 HP12 HP13 HXz4 HZ HZ4 Hcanary4 Hdepth Hgd Hgd_holds HrL10 HrL11 HrL110 HrL111 HrL15 HrL28 HrL29 HrL38 HrL39 HrLf HrLlow Hres Hres64 Hres_r Hsc48 HsmL Hsm_pre Hsp Hsp_high Hstk Hu.
  rewrite (S_t2n_eq fshape4 fshape4_le).
  apply smatch_extend_objs; [exact smatch_Sh4 | | change (rm rhoN) with (rm rhoL); exact N4_holds | exact N4_vs_stk | exact N4_pw].
  rewrite <- (S_t2n_eq fshape4 fshape4_le). exact (S_t2n_swf fshape4 fshape4_le).
Qed.

Inductive fkey4 := K4g | K4m | K4t.
Definition fbase4 (k : fkey4) : sv := ltac2:(tb__ "0|0|
Sc0S5aLk;Vk;SdfPcA1SdfPa0A1SdfPa1A1Xc0x3").
Definition fptr4 (k : fkey4) : sptr := ltac2:(tb__ "0|0|
Sc0ScLk;Vk;Vg;S133Vg;Vt4;A2S135Vg;Vt4;A2Xc0x3").
Definition flo4 (k : fkey4) : Z := ltac2:(tb__ "0|0|
Sc0S8Lk;Vk;S15dVL;Vg;A2Se0VL;S133Vg;Vt4;A2A2S136VL;Vg;Vt4;A3Xc0x3").
Definition fcond4 (k : fkey4) : Prop := ltac2:(tb__ "0|1|
Sc0OLk;Vk;S6S2S0S44ScA1S14Vt4;A1S4eScA1A3A1M0G0Xc0x3").

Inductive odF := FD_guard | FD_fmh (x : sv) | FD_free (k : fkey4) (five : bool) (pv nv : sv).
Definition obj_ofF (d : odF) : sobj := ltac2:(tb__ "0|0|
Sb9S5bLd;Vd;S181S5aS1cdR1A1Lx;Sc0S45S5aS5aS1ccSd3R4A1R3R2R1A4Lnv;Lpv;Lfive;Lk;Xb9x3").
Definition dloF (d : odF) : Z := ltac2:(tb__ "0|0|
Sb9S8Ld;Vd;Z5a338S5aS35Z5a3d0Z10A2Lx;Sc0S45S5aS5aSc5R4A1Lnv;Lpv;Lfive;Lk;Xb9x3").
Definition dszF (d : odF) : Z := ltac2:(tb__ "0|1|
Sb9S8Ld;Vd;Z8M0S5aG0Lx;Sc0S45S5aS5aZ28Lnv;Lpv;Lfive;Lk;Xb9x3").
Definition dhiF (d : odF) : Z := ltac2:(tb__ "0|0|
S35SbbVd;A1SdbVd;A1A2").
Definition dcellsF (d : odF) : list (Z * nat * sv) := ltac2:(tb__ "0|4|
Sb9S4aS4bS4bS8S48A2M0S5aA2M1A1Ld;Vd;S43G1S49G0S5aS49S8S48Z0U8A4M2SdfP8fA1A4S4fG1A1M3A3S5aS43G1S49G0S5aG2R1A4G3A3Lx;Sc0S45S5aS5aS1ceR3R2R1A3Lnv;Lpv;Lfive;Lk;Xb9x3").
Definition dromF (d : odF) : option positive := None.
Definition od_svsF (d : odF) : list sv := ltac2:(tb__ "0|2|
S178S4bS4bS8S48A2M0S5aA2M1S5aG1S53G0S5aR1A3Lc;Sc1Vd;A1A4").
Definition ds_checkbF (d : odF) : bool := forallb sv_sem (od_svsF d).
Definition DSF (d : odF) : Prop := ds_checkbF d = true.

Lemma ze_fbase4 k : ltac2:(tb__ "0|0|
S0S8S108S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaSd3Vk;A1A3Sc5Vk;A1A3").
Proof using HMI4 HP12 HXz4 Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth. destruct k; cbn [fbase4 flo4]; rewrite zeNv; [exact zeN_12 | exact zeN_160 | exact zeN_161]. Qed.
Lemma flo4_range k : ltac2:(tb__ "0|1|
S1S34Z0Sc5Vk;A1M0A2S34S35G0Z28A2Se3VL;A1A2A2").
Proof using HMI HMI4 HXz4 Hgd Hsc48 Hu rho. drop_sp.
  destruct k; cbn [flo4].
  - pose proof g_zone. flia.
  - pose proof (key_range4 _ fmQ4_key). flia.
  - exact zFp4_range.
Qed.
Lemma fptr4_facts k : ltac2:(tb__ "0|2|
Sd4Vk;A1S1S9aScSd5Vk;A1M0SedVt4;A1A3S1S0S8Sc5Vk;A1Se0VL;G0A2A3S3S44ScA1M1G1S3G1G1S0S44SdA1SebVt4;G0A2S47SdS11R2R1A2A2A3Lnx;A2Lpr;A2A2A2F_;").
Proof using HMI4 HXz4. drop_sp.
  destruct k; cbn [fcond4 fptr4 flo4]; intros HC.
  - split; [exact Kg4|]. split; [reflexivity|]. exists None, None. exact Mg4.
  - split; [exact fmQ4_key|]. split; [reflexivity|].
    destruct fshape4_cases as [(_ & E & _)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & _)]; [exfalso; exact (HC E)|]. rewrite Efm. exists (Some hp), (Some nx). exact Mfm.
  - destruct fshape4_cases as [(_ & E & _)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2 & EzF & EzFp & _)]; [exfalso; exact (HC E)|].
    rewrite Eft, EzFp. split; [exact Khp|]. split; [reflexivity|]. exists (Some pr2), (Some nx2). exact Mhp.
Qed.
Lemma sv_sem_ofF d off w e : ltac2:(tb__ "0|1|
SbeVd;A1S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48Voff;Vw;A4Ve;A4Sc1Vd;A1A3S1S0S45S1beS171Ve;A2S46A3S0S45S109Ve;A1S46A3A2F_;F_;").
Proof using . drop_sp.
  intros Hd Hin. unfold DSF, ds_checkbF, od_svsF in Hd. rewrite forallb_forall in Hd.
  specialize (Hd e ltac:(apply in_map_iff; exists (off, w, e); auto)). unfold sv_sem, U.Mal_nt__G1.Mal_nt_D.sv_sem in Hd. apply andb_prop in Hd. exact Hd.
Qed.

Lemma HzrN : ltac2:(tb__ "0|0|
S9S0S8S10fS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaR1A2S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;R1AbA3Fj;"). Proof using . intros; reflexivity. Qed.
Lemma HzlN : ltac2:(tb__ "0|0|
S9S0S4aS8A1S10dS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaR1A2S12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;R1AbA3Fl;"). Proof using . intros; reflexivity. Qed.
Definition EVN := EVu rhoN zrN zlN HzrN HzlN.
Lemma EmN : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;S5fS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaA1S5fVrhoL;A1A3"). Proof using . reflexivity. Qed.

Lemma rngDF d rhoX : ltac2:(tb__ "0|0|
SbeVd;A1S170S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaVrhoX;A2S0S4bS8S8A2S6cVrhoX;SbdVd;A1A2S49S8S8SbbVd;A1SbcVd;A1A4A3F_;F_;").
Proof using HMI HMI4 HP12 HXz4 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hd Hag. unfold dhiF. pose proof (ceiling_small L) as CS.
  destruct d; cbn [obj_ofF dloF dszF]; unfold O_guard_, O_fmh, U.Mal_nt__G1.Mal_nt_Ib.O_fmh, O_freeK, U.Mal_nt__G1.Mal_nt_Ib.O_freeK, carved, obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi];
    rewrite ?soff_lit_small by flia.
  - cbn [eval]. rewrite u64 by flia. f_equal; flia.
  - cbn [eval]. rewrite u64 by flia. f_equal; flia.
  - pose proof (flo4_range k). rewrite (EVN rhoX (fbase4 k) Hag ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity)), ze_fbase4. f_equal; flia.
Qed.
Lemma range64DF d : ltac2:(tb__ "0|0|
SbeVd;A1S1S34Z0SbbVd;A1A2S36SbcVd;A1S37Z2Z3fA2A2A2F_;").
Proof using HMI HMI4 HXz4 Hgd Hsc48 Hsp_high Hu. try clear Hdepth. try clear Hsp. intros _. unfold dhiF. pose proof (ceiling_small L). destruct d; cbn [dloF dszF]; try (pose proof (flo4_range k)); top_ranges; flia. Qed.

Ltac in_list := cbn; repeat (first [left; reflexivity | right]).
Lemma cellsDF d off w e : ltac2:(tb__ "0|2|
SbeVd;A1S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48Voff;Vw;A4Ve;A4Sc1Vd;A1A3S3S68S68S1S9aS68R1S73SbdVd;A1M1A1A3S1S0S5aS8bR1A1Ve;A3S1S0S48S3dS8cR1A1A1Vw;A3S62S170S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaR1A2S0S8S35Sa2Q40S65R2S7cG1A1A2A2S7eR2S7fR3A1A2A2S35SbbVd;A1Voff;A2A3F_;FrhoX;A2A2A2Lc;A2F_;F_;").
Proof using HMI HMI4 HP12 HXz4 Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hd Hin. pose proof (ceiling_small L) as CS.
  assert (GEN : forall (cbase : Z) (cells : list cell) (base : sv) (bz tgt : Z),
            In (mkCell (SLit (cbase + off)) (Z.of_nat w) e) cells ->
            (forall rhoX, agrees rhoN rhoX -> bv_unsigned (eval rhoX base) = bz) ->
            - 2 ^ 62 <= cbase + off < 2 ^ 62 -> tgt = bz + cbase + off ->
            exists c, In c cells /\ c_val c = e /\ Z.to_nat (c_width c) = w /\
              forall rhoX, agrees rhoN rhoX -> bv_unsigned (eval rhoX base) + soff rhoX (c_off c) = tgt).
  { intros cbase cells base bz tgt Hc Hb Hr ->. exists (mkCell (SLit (cbase + off)) (Z.of_nat w) e). split; [exact Hc|]. split; [reflexivity|]. split; [cbn; flia|].
    intros rhoX Hag. cbn [c_off]. rewrite soff_lit_small by flia. rewrite (Hb rhoX Hag). flia. }
  destruct d; try destruct five; cbn in Hin;
    repeat match type of Hin with
         | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]
         | False => destruct Hin
         end; cbn [obj_ofF ob_cells ob_base O_guard_ O_fmh U.Mal_nt__G1.Mal_nt_Ib.O_fmh O_freeK U.Mal_nt__G1.Mal_nt_Ib.O_freeK carved lit_cells map free_cells U.Mal_nt__G1.Mal_nt_Ib.free_cells]; unfold dloF.
  1: eapply (GEN 0); [in_list | intros rhoX Hag; cbn [eval]; apply u64; flia | flia | flia].
  1: eapply (GEN 16); [in_list | intros rhoX Hag; cbn [eval]; apply u64; flia | flia | flia].
  all: pose proof (flo4_range k);
       eapply (GEN 0); [in_list | intros rhoX Hag; rewrite (EVN rhoX (fbase4 k) Hag ltac:(destruct k; reflexivity) ltac:(destruct k; reflexivity)); apply ze_fbase4 | flia | cbn [flo4]; flia].
Qed.
Lemma cellsInDF d off w e : ltac2:(tb__ "0|1|
SbeVd;A1S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48Voff;Vw;A4Ve;A4Sc1Vd;A1A3S1S34Z0Voff;A2S1S34S35Voff;S3bVw;A1A2S38SbcVd;A1SbbVd;A1A2A2S17aVw;U8A2A2A2F_;F_;").
Proof using . drop_sp.
  intros _ Hin. unfold dhiF. destruct d; try destruct five; cbn in Hin;
    repeat match type of Hin with
         | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-|]
         | False => destruct Hin
         end; cbn [dloF dszF]; flia.
Qed.
Lemma semDF d off w e : ltac2:(tb__ "0|1|
SbeVd;A1S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48Voff;Vw;A4Ve;A4Sc1Vd;A1A3S1S0S45S1beS171Ve;A2S46A3S0S45S109Ve;A1S46A3A2F_;F_;").
Proof using . drop_sp. exact (sv_sem_ofF d off w e). Qed.
Lemma coverDF d x : ltac2:(tb__ "0|3|
SbeVd;A1S0S44S9A1Sc3Vd;A1S4eS9A1A3S1S34SbbVd;A1M0Vx;A2S36Vx;SbcVd;A1A2A2S3S8S8S3S48S48S3S5aS5aS1S9aS4bS4bS8S48A2M1S5aA2S49G1S5aS49S8S48R3R2A4R1A4Sc1Vd;A1A3S1S34R3S38Vx;G0A2M2A2S36G2S35R3S3bR2A1A2A2A2A2Le;A2Lw;A2Loff;A2F_;F_;F_;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros _ _ R. unfold dhiF in R.
  destruct d; cbn [dloF dszF dcellsF] in R |- *.
  - exists 0, 8%nat, (v 143). split; [left; reflexivity | flia].
  - exists 0, 8%nat, x0. split; [left; reflexivity | flia].
  - unfold free_cells, U.Mal_nt__G1.Mal_nt_Ib.free_cells. destruct five.
    + destruct (Z_lt_dec (x - flo4 k) 8); [exists 0, 8%nat, pv; split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 16); [exists 8, 8%nat, nv; split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 24); [exists 16, 8%nat, (SLit 0); split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 32); [exists 24, 8%nat, (SLit 0); split; [in_list | flia]|].
      exists 32, 8%nat, (SLit 0); split; [in_list | flia].
    + destruct (Z_lt_dec (x - flo4 k) 8); [exists 0, 8%nat, pv; split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 16); [exists 8, 8%nat, nv; split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 24); [exists 16, 8%nat, (SLit 0); split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 28); [exists 24, 4%nat, (SLit 0); split; [in_list | flia]|].
      destruct (Z_lt_dec (x - flo4 k) 32); [exists 28, 4%nat, (SLit 0); split; [in_list | flia]|].
      exists 32, 8%nat, (SLit 0); split; [in_list | flia].
Qed.
Lemma dunkDF d : ltac2:(tb__ "0|0|
SbeVd;A1S0S44S9A1Sc3Vd;A1S4eS9A1A3S0S92S7dSbdVd;A1A1S71A3F_;F_;").
Proof using . drop_sp. intros _ _. destruct d; reflexivity. Qed.
Lemma romDF d l x : ltac2:(tb__ "0|2|
SbeVd;A1S0S44S9A1Sc3Vd;A1S47S9Vl;A2A3S1S34SbbVd;A1Vx;A2S36Vx;SbcVd;A1A2A2S1S0S45S97S55Sa1Q40Vx;A2M0A2S46A3S0S44Sa0Q8A1M1A1S5fVrhoL;G0A2S4eG1A1A3A2F_;F_;F_;").
Proof using . drop_sp. intros _ E. discriminate E. Qed.

Definition od_okF_at (t : astate) (d : odF) : Prop := ltac2:(tb__ "0|5|
Sb9OLd;Vd;S6S5aS0S8S108S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaM0S12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaM1R1A3S165VL;S14Vt;A1A2A3Lx;Sc0S45S5aS5aS1Sd4R4A1S3S44ScA1M2G2S3G2G2S1S0S44SdA1SebVt;Sd5R6A1A2S47SdS11R2R1A2A2A3S1S2S0G2R2S4eScA1A3A1S1ScS0G2R3S47ScR1A2M3A3S9aScR2SedVt4;A1A3M4F_;Fp;S1ScS0G2R2G3A3G4F_;Fp;S1S0S8S108G0G1R4A3S165VL;R2A2A3S0S8S108G0G1R3A3S165VL;R1A2A3A2A2A2A2A2Lnx;A2Lpr;A2A2Lnv;Lpv;Lfive;Lk;Xb9x3").
Definition od_okF (d : odF) : Prop := ltac2:(tb__ "0|0|
S1SbeVd;A1ScdVt4;Vd;A2A2").

Lemma od_okF_nz t d : ltac2:(tb__ "0|3|
ScS9aScR1VX;A3M0S0S44SdA1SebVt;R2A2S47SdS11S4eScA1M1G1A2A2A3F_;Fx;ScdVt;Vd;A2ScG0S4S34SbcVd;A1Se0VL;R2A2M2A2S34S35G2Z28A2SbbVd;A1A2A2F_;Fx;F_;F_;").
Proof using HMI4 HXz4 Hgd Hsc48. drop_sp.
  intros HXt Hok x Hx. unfold dhiF. pose proof (XS_key4 x ltac:(right; exact Hx)) as Kx.
  destruct d; cbn [dloF dszF]; cbn [od_okF_at] in Hok.
  - pose proof (key_zone4 x Kx). flia.
  - pose proof (key_zone4 x Kx). flia.
  - destruct Hok as (HC & pr & nx & M & NP & _). destruct (fptr4_facts k HC) as (Kk & -> & _).
    apply (keys_apart4 (fptr4 k) x Kk Kx). intros E. rewrite E, (HXt x Hx) in M. injection M as <- <-. exact (NP eq_refl).
Qed.
Lemma od_okF_nzg d : ltac2:(tb__ "0|1|
Sc6Vd;A1ScS9aScR1S43ScVg;VX;A3A3S4S34SbcVd;A1Se0VL;R2A2M0A2S34S35G0Z28A2SbbVd;A1A2A2F_;Fx;F_;").
Proof using HMI4 HXz4 Hgd Hsc48. drop_sp.
  intros [_ Hok] x Hx. unfold dhiF. pose proof (XS_key4 x Hx) as Kx.
  destruct d; cbn [dloF dszF]; cbn [od_okF_at] in Hok.
  - pose proof (key_zone4 x Kx). flia.
  - pose proof (key_zone4 x Kx). flia.
  - destruct Hok as (HC & pr & nx & M & NP & _). destruct (fptr4_facts k HC) as (Kk & -> & _).
    apply (keys_apart4 (fptr4 k) x Kk Kx). intros E. rewrite E, (XS_free x Hx) in M. injection M as <- <-. exact (NP eq_refl).
Qed.

Lemma od_holdF d : ltac2:(tb__ "0|0|
Sc6Vd;A1S64S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS17cVmsL;S5fVrhoL;A1A2SbdVd;A1A4F_;").
Proof using EmW Erd HMI HMI4 HP12 HXz4 HZ HZ4 Hcanary4 Hdepth Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmL Hsp Hu. try clear Hsp_high.
  intros Hok. pose proof (od_okF_nzg d Hok) as NZ. destruct Hok as [Hd Hok].
  destruct d; cbn [obj_ofF]; cbn [od_okF_at] in Hok.
  - exact hold_guard4.
  - apply (hold_real4 _ _ _ (rngDF (FD_fmh x) rhoN Hd (agrees_refl rhoN)) NZ).
    apply hold_fmh4; [exact (proj2 (sv_sem_ofF (FD_fmh x) 0 8 x Hd ltac:(left; reflexivity))) | exact Hok].
  - destruct Hok as (HC & pr & nx & M & NP & Kpr & Knx & Epv & Env). destruct (fptr4_facts k HC) as (Kk & Ek & _).
    apply (hold_real4 _ _ _ (rngDF (FD_free k five pv nv) rhoN Hd (agrees_refl rhoN)) NZ).
    apply (hold_freeK4 (fptr4 k) pr nx (fbase4 k) five pv nv M Kk Kpr Knx ltac:(destruct k; reflexivity)).
    + exact (proj2 (sv_sem_ofF (FD_free k five pv nv) 0 8 pv Hd ltac:(destruct five; in_list))).
    + exact (proj2 (sv_sem_ofF (FD_free k five pv nv) 8 8 nv Hd ltac:(destruct five; in_list))).
    + rewrite ze_fbase4. exact Ek.
    + exact Epv.
    + exact Env.
Qed.

Definition s5 : astate := fgn_s5 g t4.
Lemma s5_eq : ltac2:(tb__ "0|0|
S0S10SbaS208Vt4;Vg;A2A3"). Proof using . reflexivity. Qed.
Ltac fgn_arg := first [ exact HuP | exact HiP | exact HfrP | exact HkP | exact HmemP | exact HscP
                      | exact HI | exact Hu | exact HU | exact HR2g | exact HallN | exact Hsc48am | exact Hml0 | exact Hlinks3 | exact HnU3 | exact Hact3' | exact HactU3'
                      | exact HI4 | exact HXz4 | exact Cr4 | exact UB4 ].
Lemma FIN5 : ltac2:(tb__ "0|1|
S1Sf1VX;S4eS4bScS8A2A1VU;SbaA4S1S1f1VX;Vs;SbaA3S1S210Vs;SbaA2S1ScS9aScR1VX;A3S0S44SdA1SebSbaR2A2S47SdS11S4eScA1M0G0A2A2A3F_;Fx;S1S209Vt4;SbaA2S1S0S4aSeA1S23SbaA1S23Vt4;A1A3ScS15S5SefVX;SbaR2R1A4SefS43ScVg;VX;A3Vt4;R2R1A4A2Fa;Fq;A2A2A2A2A2A2").
Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hgd Hml0 Hsc48 Hu UB4 rho. drop_sp. unfold s5. eapply (fgn_finish X U s g am i) with (frP := frPar); fgn_arg. Qed.
Lemma HI5 : ltac2:(tb__ "0|0|
Sf1VX;S4eS4bScS8A2A1VU;SbaA4"). Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hgd Hml0 Hsc48 Hu UB4 rho. exact (proj1 FIN5). Qed.
Lemma HXz5 : xzomb X s5. Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hgd Hml0 Hsc48 Hu UB4 rho. exact (proj1 (proj2 (proj2 (proj2 FIN5)))). Qed.
Lemma HXr5 : xraw X s5. Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hgd Hml0 Hsc48 Hu UB4 rho. exact (xzomb_xraw X s5 HXz5). Qed.
Lemma Hreach5 : reach_ok s5. Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hgd Hml0 Hreach4 Hsc48 Hu UB4 rho. exact (reach_ok_kept t4 s5 (proj1 (proj2 (proj2 (proj2 (proj2 FIN5))))) Hreach4). Qed.

Section ReabF.
Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agrees rhoN rhoF.
Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC : list odF).
Definition oStkF4 : sobj := ltac2:(tb__ "0|0|
S77S61PaA1S61PfA1S5dZ0A1Vstkc;S71A5").
Definition NRELF : list sobj := map obj_ofF dsF.
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S4aS5bA1S6bVSF;A1S43S5bS1b0VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S45S1a1VobjsF;S1b6A2S46A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S66S55VrhoF;VSF;S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4A4").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S0S45S9bSb9SccVdsF;A3S46A3").
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
Sb9S9aSb9R1VdsF;A3S4Sc6R2A1S9aSb9R2VdsC;A3A2F_;Fd;").
Variable locs : list loc.
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S1d0Vt4;SbaVlocs;A3").
Definition od_chgF (d : odF) : Prop := match d with FD_guard => False | _ => True end.
Hypothesis HdsC : ltac2:(tb__ "0|0|
Sb9S9aSb9R1VdsC;A3S1S9aSb9R2VdsF;A3S1ScdSbaR2A2S1bbR2A1A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|1|
SeaS9aSeaR1Vlocs;A3S3Sb9Sb9S1S9aSb9R1VdsC;A3S1S34SbbR1A1SecVL;R3A2M0A2S36G0SbcR1A1A2A2A2Ld;A2F_;Fl;").
Hypothesis HdsC_g : ltac2:(tb__ "0|0|
S3S45S45S3S5aS5aS3S5aS5aS9aSb9SbfSc2R3R2R1A4VdsC;A3Lnv;A2Lpv;A2Lfive;A2").

Lemma HdsF5 d : ltac2:(tb__ "0|0|
S9aSb9Vd;VdsF;A3SbeVd;A1F_;").
Proof using HdsF_DS. drop_sp. intros Hd. exact (proj1 (forallb_forall _ _) HdsF_DS d Hd). Qed.
Lemma Hent_holdF d : ltac2:(tb__ "0|0|
S9aSb9Vd;VdsF;A3Sc6Vd;A1S64S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS17cVmsL;S5fVrhoL;A1A2SbdVd;A1A4F_;F_;").
Proof using EmW Erd HMI HMI4 HP12 HXz4 HZ HZ4 Hcanary4 Hdepth Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmL Hsp Hu. try clear Hsp_high. intros _ Hok. exact (od_holdF d Hok). Qed.
Lemma HdsC_sub5 d : ltac2:(tb__ "0|0|
S9aSb9Vd;VdsC;A3S1S9aSb9Vd;VdsF;A3S0S44S9A1Sc3Vd;A1S4eS9A1A3A2F_;").
Proof using HdsC. drop_sp. intros Hd. split; [exact (proj1 (HdsC d Hd)) | reflexivity]. Qed.
Lemma HromL4 : rom_ok segsU msL. Proof using HsmL. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))). Qed.

Let m' : word -> option byte := ltac2:(tb__ "0|0|
S1a2Sb9SbdVmsF;VrhoF;VdsF;A5").
Let touched : Z -> Prop := ltac2:(tb__ "0|0|
S1a3Sb9SbbSbcVdsC;A4").
Let bv1 : byteview := ltac2:(tb__ "0|0|
Se2S106S55Vm';A2S107S55Vm';A2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
Se2S106S55Vm';A2Sa0Q40A1S46L_;A2").

Lemma V1F : ltac2:(tb__ "0|3|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2S2Vtouched;R2A1A1S1S0S44S8A1M0Vbv1;R3A1Se2S106S55S5fVrhoL;A1M1A2M2S107S55G1A2R3A3A3S0G0Vrv1;R3A1Se2G2Sa0Q40A1S46L_;R3A3A3A2F_;F_;Fx;").
Proof using EmW Erd HMI HMI4 HP12 HSF_match HSF_objs HXz4 HZ HZ4 HagF Hcanary4 Hdepth HdsF_DS HdsF_ent Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmF HsmL Hsp Hsp_high Hu m'.
  exact (V1 segsU rhoN zrN zlN HzrN HzlN odF obj_ofF dloF dhiF dcellsF dromF DSF (rm rhoL) EmN rngDF range64DF cellsDF cellsInDF semDF coverDF dunkDF romDF
           msL HromL4 tr md msF rhoF HagF SF oStkF4 objsF dsF dsC HSF_objs HSF_match HsmF HdsF5 od_okF HdsF_ent Hent_holdF).
Qed.
Lemma VMF : ltac2:(tb__ "0|0|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2Vtouched;R2A1S2S0S44S8A1Vbv1;R3A1S4eS8A1A3A1F_;F_;Fx;").
Proof using HMI HMI4 HP12 HSF_match HSF_objs HXz4 HagF HdsC HdsF_DS Hgd Hsc48 HsmF Hsp Hu m'. try clear Hsp_high. try clear Hdepth.
  intros x Hx T. exact (VM segsU rhoN odF obj_ofF dloF dhiF dromF DSF rngDF dunkDF tr md msF rhoF HagF SF oStkF4 objsF dsF dsC HSF_objs HSF_match HsmF HdsF5 HdsC_sub5 x Hx T).
Qed.
Definition cell_from_odF : ltac2:(tb__ "0|3|
Sb9S8S48S5aSe9S8S9aSb9R6VdsC;A3S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48R6R5A4R4A4Sc1R7A1A3S0S8SecVL;Sf2R4A1A2S35SbbR8A1R7A2A3S0S48Sf3R5A1R7A3S0S44S8A1S1d1VL;R6A2S47S8R5A2A3S0S8S3aR6S37Z2S3eZ8S3bR9A1A2A2M1A2S3aS108S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaR8A3G1A2A3Sf7VL;Se2S106S55S1a2Sb9SbdVmsF;VrhoF;VdsF;A5M2A2S107S55G2A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S1a6S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaScbScaSb9SbdSbbSbcSc1Sc3SbeSc7Sd7Sd0Sd1Sd8Sd2Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S1b0VobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;S1b1S1b5VL;A23").
Definition cell_from_od_zeroF : ltac2:(tb__ "0|3|
Sb9S8S48S5aS48Se9S9aSb9R6VdsC;A3S9aS4bS4bS8S48A2M0S5aA2S49G0S5aS49S8S48R6R5A4R4A4Sc1R7A1A3S0S8SecVL;Sf2R3A1A2S35S35SbbR8A1R7A2S3bR4A1A2A3S17aS20dR5Sf3R4A1A2R7A2S0S44S8A1S1d1VL;R5A2S47S8Z0M1A2A3S0S8S108S130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaR8A3G1A3Sf7VL;Se2S106S55S1a2Sb9SbdVmsF;VrhoF;VdsF;A5M2A2S107S55G2A2A2R7A3F_;F_;F_;F_;F_;F_;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S1a7S55S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS130VL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS12fVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaScbScaSb9SbdSbbSbcSc1Sc3SbeSc7Sd7Sd0Sd1Sd8Sd2Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S1b0VobjsF;VdsF;VdsC;VHSF_objs;VHSF_match;VHsmF;S1b1S1b5VL;A23").
Definition m'_inF : ltac2:(tb__ "0|1|
Sb9S8S9aSb9R2VdsF;A3S1S34SbbR3A1R2A2S36R2SbcR3A1A2A2S1S34Z0R3A2S36R3S37Z2Z40A2A2A2S0S44Sa0Q8A1A1S1a2Sb9SbdVmsF;VrhoF;VdsF;Sa1Q40R4A2M0A6S1e6VmsF;G0A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|0|
S1a9S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaSb9SbdSbbSbcSbeSc7VmsF;VrhoF;VHagF;VdsF;S1b1Ac").
Definition m'_outF : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2Sb9S9aSb9R1VdsF;A3S2S1S34SbbR2A1R4A2S36R4SbcR2A1A2A2A1F_;Fd;S0S44Sa0Q8A1A1S1a2Sb9SbdVmsF;VrhoF;VdsF;Sa1Q40R3A2M0A6S5fVrhoL;G0A2A3F_;F_;Fx;") := ltac2:(tb__ "0|0|
S1aaS12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaSb9SbdSbbSbcSbeS5fVrhoL;A1Sd9Sc7VmsF;VrhoF;VHagF;VdsF;S1b1Ae").
Definition touched_decF : ltac2:(tb__ "0|1|
S8S1fbS1a3Sb9SbbSbcVdsC;R1A5M0S2G0A1A2Fx;") := ltac2:(tb__ "0|0|
S1acSb9SbbSbcVdsC;A4").

Lemma D5_fp : ltac2:(tb__ "0|0|
S0S4aS4bSeaS8A2A1SfaSbaA1SfaVt4;A1A3"). Proof using Hdelta. exact (proj1 Hdelta). Qed.
Lemma D5_ub : ltac2:(tb__ "0|0|
S0S4aS4bScS8A2A1SfdSbaA1SfdVt4;A1A3"). Proof using Hdelta. exact (proj1 (proj2 Hdelta)). Qed.
Lemma D5_init : ltac2:(tb__ "0|0|
S0S45S2dSbaA1S2dVt4;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 Hdelta))). Qed.
Lemma D5_regions : ltac2:(tb__ "0|0|
S0S4aSeA1S23SbaA1S23Vt4;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hdelta))))). Qed.
Lemma D5_brk : ltac2:(tb__ "0|0|
S0S32S2cSbaA1S2cVt4;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))). Qed.
Lemma D5_keys : ltac2:(tb__ "0|0|
S0S4aScA1SedSbaA1SedVt4;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))). Qed.
Lemma D5_cells : ltac2:(tb__ "0|0|
Se9S9aSe9R1S50Se9Sf0SbaA1S194SbaA1A3A3S4S9aSe9R2S50Se9Sf0Vt4;A1S194Vt4;A1A3A3S9aSeaSf2R2A1Vlocs;A3A2F_;Fc;").
Proof using Hdelta. drop_sp. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))))). Qed.
Lemma bounded5 : bounded s5.
Proof using HMI4 Hdelta. drop_sp.
  pose proof (mig_bounded HMI4) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4.
  destruct Hdelta as (_ & _ & _ & A4 & A5 & _ & _ & A8 & A9 & A10 & A11 & _).
  unfold bounded. unfold usage_of in *. rewrite A8, A9, A4, A10, A11, A5. auto.
Qed.
Lemma region_of5 k : ltac2:(tb__ "0|0|
S0S44SeA1Sf5SbaVk;A2Sf5Vt4;Vk;A2A3").
Proof using Hdelta. drop_sp. unfold region_of. rewrite D5_regions. reflexivity. Qed.
Lemma HL5 : layout_ok L s5.
Proof using HMI4 Hdelta. drop_sp.
  pose proof HL4 as (A & B & C' & D). split; [exact A|]. split; [|rewrite D5_fp; split; [exact C' | exact D]].
  intros k rg Hr Hl. rewrite region_of5 in Hr. exact (B k rg Hr Hl).
Qed.
Lemma Hvm5 : ltac2:(tb__ "0|0|
Se6VL;SbaVvm;A3").
Proof using HMI4 Hdelta. drop_sp.
  pose proof HV4 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). unfold vm_ok.
  split; [intros r rg Hr; rewrite region_of5 in Hr; exact (V1 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of5 in Hr; exact (V2 r rg Hr)|].
  split; [rewrite D5_brk; exact V3|].
  split; [rewrite D5_fp; exact V4|].
  split; [intros r rg off Hr; rewrite region_of5 in Hr; exact (V5 r rg off Hr)|].
  split; [intros r1 r2 rg1 rg2 Hne H1 H2; rewrite region_of5 in H1, H2; exact (V6 r1 r2 rg1 rg2 Hne H1 H2)|].
  split; [intros r rg Hr; rewrite region_of5 in Hr; exact (V7 r rg Hr)|].
  split; [intros r rg Hr; rewrite region_of5 in Hr; exact (V8 r rg Hr)|].
  split; [intros r rg q n0 Hr Hk Hl Hin Hne; rewrite region_of5 in Hr; rewrite D5_fp in Hin; exact (V9 r rg q n0 Hr Hk Hl Hin Hne)|].
  split; [intros rb p k rgk Hb Hr Hk Hl; rewrite region_of5 in Hr; rewrite D5_brk in Hb; exact (V10 rb p k rgk Hb Hr Hk Hl)|].
  exact V11.
Qed.

Lemma fp_entry_below5 rg : ltac2:(tb__ "0|1|
S9aS4bSeaS8A2Vrg;SfaSbaA1A3S34Z0S53SeaS8Vrg;A3M0A2S34S35SecVL;S52SeaS8Vrg;A3A2G0A2Se3VL;A1A2F_;F_;").
Proof using HMI4 Hdelta. drop_sp.
  intros Hin Hn. destruct rg as [[o|p] n]; cbn [fst snd] in *.
  - unfold footprint in Hin. destruct Hin as [E|Hin].
    + injection E as <- <-. cbn [loc_addr]. rewrite Hctx4. top_ranges. unfold CTX_SIZE. flia.
    + exfalso. apply in_app_iff in Hin as [Hin|Hin].
      * apply in_map_iff in Hin as (a & E & _). discriminate E.
      * apply in_flat_map in Hin as (k & _ & Hin). destruct (region_of s5 k) as [rg|]; [|destruct Hin].
        destruct (rg_kind rg); try destruct Hin. destruct (rg_live rg); [|destruct Hin]. destruct Hin as [E|[]]. discriminate E.
  - exact (proj1 (proj2 (footprint_mem_range C_U L s5 vm p n Hvm5 HLG4 Hin Hn))).
Qed.
Lemma cell_below_ceiling5 c k : ltac2:(tb__ "0|0|
S9aSe9Vc;S50Se9Sf0SbaA1S194SbaA1A3A3S17bVk;Sf3Vc;A1A2S36S35SecVL;Sf2Vc;A1A2S3bVk;A1A2Se3VL;A1A2F_;F_;").
Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hdelta Hgd Hml0 Hsc48 Hsp Hu UB4 touched. try clear Hsp_high. try clear Hdepth.
  intros Hc Hk. destruct (cell_in_footprintI X None U s5 L HI5 HXr5 c Hc) as (rg & Hrg & [I1 I2]).
  unfold crange, cell_range in I1, I2. cbn [fst snd] in I1, I2.
  pose proof (fp_entry_below5 rg Hrg ltac:(flia)). flia.
Qed.
Lemma owned_below_ceiling5 x : ltac2:(tb__ "0|0|
Sf4VL;SbaVx;A3S36Vx;Se3VL;A1A2F_;").
Proof using HMI4 Hdelta Hgd Hsc48 Hsp touched. try clear Hsp_high. try clear Hdepth. intros [(rg & Hrg & Hx) _]. pose proof (fp_entry_below5 rg Hrg ltac:(flia)). flia. Qed.

Definition stk4 (x : Z) : Prop := ltac2:(tb__ "0|1|
S1S34S38S14dVrho;A1M0Z60A2Vx;A2S36Vx;G0A2A2").
Definition stkb4 (x : Z) : bool := ltac2:(tb__ "0|1|
S4cS3fS38S14dVrho;A1M0Z60A2Vx;A2S40Vx;G0A2A2").
Lemma stkb4_spec x : ltac2:(tb__ "0|0|
S5S0S45S1baVx;A1S46A3S1afVx;A1A2").
Proof using Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp i touched. try clear Hsp_high. unfold stkb4, stk4. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma stk4_high x : ltac2:(tb__ "0|0|
S1afVx;A1S1S34Se3VL;A1Vx;A2S36Vx;S37Z2Z40A2A2A2F_;").
Proof using Hdepth Hgd Hsc48 Hsp Hsp_high touched. unfold stk4. intros R. pose proof Hsp_high. pose proof D0_range4. pose proof sp0_range4. flia. Qed.
Definition touchedV5 (x : Z) : Prop := ltac2:(tb__ "0|0|
S4Vtouched;Vx;A1S1afVx;A1A2").
Lemma touchedV5_dec x : ltac2:(tb__ "0|1|
S1fbS1b2Vx;A1M0S2G0A1A2").
Proof using Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp i. try clear Hsp_high.
  unfold touchedV5, stk4. destruct (touched_decF x) as [T|T]; [left; left; exact T|].
  destruct (Z_le_dec (sp0 - 96) x); [destruct (Z_lt_dec x sp0); [left; right; flia|]|]; right; intros [H|H]; try tauto; flia.
Qed.

Lemma dsF_nz5 d x : ltac2:(tb__ "0|0|
S9aSb9Vd;VdsF;A3S1S34SbbVd;A1Vx;A2S36Vx;SbcVd;A1A2A2S2S154VL;VX;Vx;A3A1F_;F_;").
Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall HdsC HdsF_ent Hgd Hml0 Hsc48 Hsp Hu UB4 touched. try clear Hsp_high. try clear Hdepth.
  intros Hd R (q & Hq & Rq). unfold META_SIZE in Rq.
  destruct (HdsF_ent d Hd) as [Hok | HdC].
  - pose proof (od_okF_nzg d Hok q ltac:(right; exact Hq)). flia.
  - destruct (HdsC d HdC) as (_ & Hok' & _). pose proof (od_okF_nz s5 d HXz5 Hok' q Hq). flia.
Qed.
Lemma touched_nz5 x : ltac2:(tb__ "0|0|
Vtouched;Vx;A1S2S154VL;VX;Vx;A3A1F_;").
Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall HdsC HdsF_ent Hgd Hml0 Hsc48 Hsp Hu UB4. try clear Hsp_high. try clear Hdepth. intros (d & HdC & R). exact (dsF_nz5 d x (proj1 (HdsC d HdC)) R). Qed.
Lemma dhiF_below d : ltac2:(tb__ "0|0|
S34SbcVd;A1Se3VL;A1A2").
Proof using HMI HMI4 HXz4 Hgd Hsc48 Hsp_high Hu touched. try clear Hdepth. try clear Hsp. unfold dhiF. pose proof (ceiling_small L). destruct d; cbn [dloF dszF]; try (pose proof (flo4_range k)); top_ranges; flia. Qed.
Lemma touched_nstk5 x : ltac2:(tb__ "0|0|
Vtouched;Vx;A1S2S1afVx;A1A1F_;").
Proof using HMI HMI4 HXz4 Hdepth Hgd Hsc48 Hsp Hsp_high Hu dsC. intros (d & HdC & R) S. pose proof (dhiF_below d). pose proof (stk4_high x S). flia. Qed.
Lemma stk4_nz x : ltac2:(tb__ "0|0|
S1afVx;A1S2S154VL;VX;Vx;A3A1F_;").
Proof using HMI4 Hdepth Hgd Hsc48 Hsp Hsp_high touched. intros S (q & Hq & Rq). pose proof (key_range4 q (XS_key4 q ltac:(right; exact Hq))). pose proof (stk4_high x S). unfold META_SIZE in *. flia. Qed.
Lemma gslot_touched5 x : ltac2:(tb__ "0|1|
S1S34S15dVL;Vg;A2M0Vx;A2S36Vx;S35G0Z28A2A2A2Vtouched;Vx;A1F_;").
Proof using HdsC_g Hgd Hsc48 rho t4. drop_sp. intros R. destruct HdsC_g as (five & pv & nv & HdC). exists (FD_free K4g five pv nv). split; [exact HdC|]. unfold dhiF. cbn [dloF dszF flo4]. flia. Qed.

Lemma untouched_ngX x : ltac2:(tb__ "0|1|
S2Vtouched;Vx;A1A1S2S154VL;VX;Vx;A3A1ScS9aScR1S43ScVg;VX;A3A3S2S1S34Se0VL;R2A2M0Vx;A2S36Vx;S35G0Z28A2A2A2A1F_;Fq;F_;F_;").
Proof using HdsC_g Hgd Hsc48 rho t4. drop_sp.
  intros NT NZ q [<-|Hq] R; [exact (NT (gslot_touched5 x R))|]. apply NZ. exists q. unfold META_SIZE. auto.
Qed.

Definition m'' : word -> option byte := ltac2:(tb__ "0|1|
Sa0Q40M0A1S45S44Sa0Q8A1A1L_;S1baSa2G0R1A2A1S5fVrho;R1A2Vm';R1A1X45x2La;").

Definition m5v : word -> option byte := ltac2:(tb__ "0|1|
Sa0Q40M0A1S45S44Sa0Q8A1A1L_;S15bVL;VX;Sa2G0R1A2A3Vmv4;R1A1S1adR1A1X45x2La;").
Let bv1v : byteview := ltac2:(tb__ "0|0|
Se2S106S55S1aeA2S107S55S1aeA2A2").
Let rv1v : byteview := ltac2:(tb__ "0|0|
Se2S106S55S1aeA2Sa0Q40A1S46L_;A2").
Let rv4 : byteview := ltac2:(tb__ "0|0|
Se2S106S55Vmv4;A2Sa0Q40A1S46L_;A2").

Lemma m''_stk a : ltac2:(tb__ "0|0|
S1afSa2Q40Va;A2A1S0S44Sa0Q8A1A1S1adVa;A1S5fVrho;Va;A2A3F_;").
Proof using Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp i touched. try clear Hsp_high. intros H. unfold m''. rewrite (proj2 (stkb4_spec _) H). reflexivity. Qed.
Lemma m''_nstk a : ltac2:(tb__ "0|0|
S2S1afSa2Q40Va;A2A1A1S0S44Sa0Q8A1A1S1adVa;A1Vm';Va;A1A3F_;").
Proof using Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp i touched. try clear Hsp_high. intros H. unfold m''. destruct (stkb4 (bv_unsigned a)) eqn:E; [exfalso; exact (H (proj1 (stkb4_spec _) E)) | reflexivity]. Qed.
Lemma m5v_nz a : ltac2:(tb__ "0|0|
S2S154VL;VX;Sa2Q40Va;A2A3A1S0S44Sa0Q8A1A1S1aeVa;A1S1adVa;A1A3F_;").
Proof using . drop_sp. intros H. unfold m5v. rewrite (proj2 (zslotb_false L X _) H). reflexivity. Qed.
Lemma m5v_z a : ltac2:(tb__ "0|0|
S154VL;VX;Sa2Q40Va;A2A3S0S44Sa0Q8A1A1S1aeVa;A1Vmv4;Va;A1A3F_;").
Proof using . drop_sp. intros H. unfold m5v. rewrite (proj2 (zslotb_spec L X _) H). reflexivity. Qed.
Lemma views_at5 (m1 m2 : word -> option byte) x : ltac2:(tb__ "0|6|
S0S44Sa0Q8A1A1Vm1;Sa1Q40M0Vx;A2M1A1Vm2;G1A1A3S1S0S44S8A1M2Se2S106S55Vm1;A2M3S107S55Vm1;A2Vx;A3Se2S106S55Vm2;A2M4S107S55Vm2;A2Vx;A3A3S0G2Se2G3Sa0G0A1S46L_;M5Vx;A3Se2G4G5Vx;A3A3A2F_;").
Proof using . drop_sp. intros E. unfold byteview_of, Glue.rd_of, Glue.wok_of. rewrite E. auto. Qed.
Lemma m5_zslot x : ltac2:(tb__ "0|1|
S1S34Z0Vx;A2S36Vx;S37Z2Z40A2A2A2S154VL;VX;Vx;A3S0S44Sa0Q8A1A1Vm';Sa1Q40Vx;A2M0A1S5fVrhoL;G0A2A3F_;F_;").
Proof using Cr4 HMI HMI4 HP12 HR2g HU HXz4 HagF Hall HdsC HdsF_DS HdsF_ent Hgd Hml0 Hsc48 Hsp Hu UB4 msF touched. try clear Hsp_high. try clear Hdepth. intros Hx Z0. apply (m'_outF x Hx). intros d Hd R. exact (dsF_nz5 d x Hd R Z0). Qed.

Theorem V1v5 : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2S2S1b2R2A1A1S1S0S44S8A1M0Vbv1v;R3A1Vbv4;R3A1A3S0G0Vrv1v;R3A1Vrv4;R3A1A3A2F_;F_;Fx;").
Proof using EmW Erd HMI HMI4 HP12 HSF_match HSF_objs HXz4 HZ HZ4 HagF Hcanary4 Hdepth HdsC_g HdsF_DS HdsF_ent Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmF HsmL Hsp Hsp_high Hu bv1 rv1.
  intros x Hx NT. unfold bv1v, rv1v, bv4, rv4. unfold touchedV5 in NT.
  assert (NTr : ~ touched x) by tauto. assert (NS : ~ stk4 x) by tauto.
  destruct (zslotb L X x) eqn:Ez.
  - apply views_at5. apply m5v_z. rewrite u64_of_sum by flia. exact (proj1 (zslotb_spec L X x) Ez).
  - pose proof (proj1 (zslotb_false L X x) Ez) as NZ.
    destruct (views_at5 m5v m' x ltac:(rewrite (m5v_nz (Z_to_bv 64 x)); rewrite ?u64_of_sum by flia; [apply m''_nstk; rewrite u64_of_sum by flia; exact NS | exact NZ])) as [A1 A2]. rewrite A1, A2.
    destruct (V1F x Hx NTr) as [B1 B2]. unfold bv1, rv1 in B1, B2. rewrite B1, B2.
    apply views_at5. symmetry. apply HZ4_at. intros q Hq R. rewrite u64_of_sum in R by flia. exact (untouched_ngX x NTr NZ q Hq R).
Qed.
Theorem VMv5 : ltac2:(tb__ "0|0|
S8S1S34Z0R1A2S36R1S37Z2Z40A2A2A2S1b2R2A1Sf4VL;SbaR3A3S2S0S44S8A1Vbv1v;R4A1S4eS8A1A3A1F_;F_;F_;Fx;").
Proof using Cr4 HMI HMI4 HP12 HR2g HSF_match HSF_objs HU HXz4 HagF Hall Hdelta Hdepth HdsC HdsF_DS HdsF_ent Hgd Hml0 Hres Hres64 Hres_r Hsc48 HsmF Hsp Hsp_high Hu UB4 bv1.
  intros x Hx [T|S] OW; [|exfalso; pose proof (owned_below_ceiling5 x OW); pose proof (stk4_high x S); flia].
  unfold bv1v.
  rewrite (proj1 (views_at5 m5v m' x ltac:(rewrite (m5v_nz (Z_to_bv 64 x)); rewrite ?u64_of_sum by flia; [apply m''_nstk; rewrite u64_of_sum by flia; exact (touched_nstk5 x T) | exact (touched_nz5 x T)]))).
  exact (VMF x Hx T).
Qed.
Lemma magree_post5 : ltac2:(tb__ "0|0|
S152VL;VX;S1aeS1adA4").
Proof using Cr4 HMI HMI4 HP12 HR2g HU HXz4 HZ4 HagF Hall Hdepth HdsC HdsF_DS HdsF_ent Hgd Hml0 Hres Hres64 Hres_r Hsc48 Hsp Hsp_high Hu UB4 touched.
  split; [intros a Ha; exact (m5v_nz a Ha)|].
  intros a. destruct (zslotb L X (bv_unsigned a)) eqn:Ez; [|rewrite (m5v_nz a (proj1 (zslotb_false L X _) Ez)); tauto].
  pose proof (proj1 (zslotb_spec L X _) Ez) as Z0. rewrite (m5v_z a Z0).
  rewrite <- (Z_to_bv_bv_unsigned 64 a). pose proof (urange a) as Ua.
  rewrite (m''_nstk (Z_to_bv 64 (bv_unsigned a))) by (rewrite u64_of_sum by flia; intros S; exact (stk4_nz _ S Z0)).
  rewrite (m5_zslot (bv_unsigned a) ltac:(flia) Z0). exact (proj2 HZ4 (Z_to_bv 64 (bv_unsigned a))).
Qed.

Definition meets5 (c : mcell) : Prop := ltac2:(tb__ "0|0|
S3S48S48S1S17bR1Sf3Vc;A1A2S1b2S35SecVL;Sf2Vc;A1A2S3bR1A1A2A1A2Lk;A2").
Definition meetsR5 (c : mcell) : Prop := ltac2:(tb__ "0|0|
S3S48S48S1S17bR1Sf3Vc;A1A2Vtouched;S35SecVL;Sf2Vc;A1A2S3bR1A1A2A1A2Lk;A2").
Lemma meets_real5 c : ltac2:(tb__ "0|0|
S9aSe9Vc;S50Se9Sf0SbaA1S194SbaA1A3A3S1b3Vc;A1S1b7Vc;A1F_;F_;").
Proof using Cr4 HMI HMI4 HR2g HU HXz4 Hall Hdelta Hdepth Hgd Hml0 Hsc48 Hsp Hsp_high Hu UB4.
  intros Hc (k & Hk & [T|S]); [exists k; auto|]. exfalso. pose proof (cell_below_ceiling5 c k Hc Hk). pose proof (stk4_high _ S). flia.
Qed.

Theorem OLD5 : ltac2:(tb__ "0|0|
Se9S9aSe9R1S50Se9Sf0SbaA1S194SbaA1A3A3S2S1b3R2A1A1S9aSe9R3S50Se9Sf0Vt4;A1S194Vt4;A1A3A3F_;F_;Fc;").
Proof using Hdelta Hlocs. drop_sp.
  intros c Hc NM. destruct (D5_cells c Hc) as [Hold | Hloc]; [exact Hold|]. exfalso.
  destruct (Hlocs _ Hloc) as (d & HdC & R). apply NM. exists 0%nat. split.
  - exact (cell_w_posI s5 c Hc).
  - left. exists d. rewrite Z.add_0_r. auto.
Qed.

Theorem VIN5 : ltac2:(tb__ "0|0|
Se9S9aSe9R1S50Se9Sf0SbaA1S194SbaA1A3A3S1b7R2A1Sf7VL;Vbv1;R3A3F_;F_;Fc;").
Proof using Cr4 HMI HMI4 HP12 HR2g HSF_match HSF_objs HU HXz4 HagF Hall Hdelta HdsC HdsF_DS Hgd Hml0 Hsc48 HsmF Hsp Hsp_high Hu UB4 m'. try clear Hdepth.
  intros c Hc (k & Hk & d & HdC & Rk). destruct (HdsC d HdC) as (Hd & Hok' & Hchg). pose proof Hctx4 as HCX.
  pose proof D5_keys as DK.
  assert (AGq : forall q dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros q dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; flia).
  destruct d as [|x|fk five pv nv]; [destruct Hchg| |]; cbn [od_okF_at] in Hok'; unfold dhiF in Rk; cbn [dloF dszF] in Rk.
  -
    assert (CM : cmeets L c (ly_ctx L + CTX_free_meta_head) 8) by (exists k; split; [exact Hk|]; rewrite HCX; unfold CTX_free_meta_head; flia).
    pose proof (ctx_fmh_cell X None U s5 L HI5 HXr5 HL5 c Hc CM) as ->.
    eapply (cell_from_odF (FD_fmh x) 0 8 x _ (optrA L (st_free_meta_head s5))); [exact HdC | left; reflexivity | | reflexivity | apply cellZ_optr | rewrite Hok'; reflexivity].
    cbn [mc_loc loc_addr dloF]. rewrite HCX. unfold CTX_free_meta_head. flia.
  -
    destruct Hok' as (Hfc & pr & nx & M' & _ & _ & _ & E1 & E2).
    destruct (fptr4_facts fk Hfc) as (Kk & EK & _). rewrite EK in Rk.
    assert (CM : cmeets L c (addr_of L (fptr4 fk)) META_SIZE) by (exists k; split; [exact Hk|]; unfold META_SIZE; flia).
    pose proof (meta_zone X None U s5 L HI5 HXr5 HL5 (fptr4 fk) c ltac:(rewrite DK; exact Kk) Hc CM) as IN.
    rewrite M' in IN. cbn [meta_slot_cells] in IN.
    unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in IN.
    assert (INC : forall off w e, In (off, w, e) (if five then [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, SLit 0); (24, 8%nat, SLit 0); (32, 8%nat, SLit 0)]
                                                 else [(0, 8%nat, pv); (8, 8%nat, nv); (16, 8%nat, SLit 0); (24, 4%nat, SLit 0); (28, 4%nat, SLit 0); (32, 8%nat, SLit 0)]) ->
                   In (off, w, e) (dcellsF (FD_free fk five pv nv))) by (intros; assumption).
    destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + eapply (cell_from_odF (FD_free fk five pv nv) 0 8 pv _ (optrA L pr)); [exact HdC | apply INC; destruct five; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E1; reflexivity].
    + eapply (cell_from_odF (FD_free fk five pv nv) 8 8 nv _ (optrA L nx)); [exact HdC | apply INC; destruct five; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; reflexivity | reflexivity | apply cellZ_optr | rewrite E2; reflexivity].
    + eapply (cell_from_od_zeroF (FD_free fk five pv nv) 16 8 (SLit 0) 0); [exact HdC | apply INC; destruct five; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
    + destruct five.
      * eapply (cell_from_od_zeroF (FD_free fk true pv nv) 24 8 (SLit 0) 0); [exact HdC | apply INC; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
      * eapply (cell_from_od_zeroF (FD_free fk false pv nv) 24 4 (SLit 0) 0); [exact HdC | apply INC; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
    + destruct five.
      * eapply (cell_from_od_zeroF (FD_free fk true pv nv) 24 8 (SLit 0) 4); [exact HdC | apply INC; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
      * eapply (cell_from_od_zeroF (FD_free fk false pv nv) 28 4 (SLit 0) 0); [exact HdC | apply INC; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
    + eapply (cell_from_od_zeroF (FD_free fk five pv nv) 32 8 (SLit 0) 0); [exact HdC | apply INC; destruct five; inlist | cbn [mc_loc dloF]; rewrite AGq, <- EK; cbn; flia | cbn; flia | reflexivity | reflexivity].
Qed.

Lemma init_true4 : st_init_done t4 = true.
Proof using HMI4 HXz4. drop_sp.
  destruct (st_init_done t4) eqn:E; [reflexivity|]. exfalso.
  pose proof (proj1 HI4) as CX. unfold ctx_ok in CX.
  destruct CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). destruct (Hf E) as (M & _).
  pose proof Kg4 as KK. unfold keys in KK. rewrite M in KK. destruct KK.
Qed.
Lemma msc_inside5 q x c : ltac2:(tb__ "0|2|
S9aSe9Vc;S103Vq;Vx;A2A3S1S34Se0VL;Vq;A2M0SecVL;Sf2Vc;A1A2M1A2S34S35G1S3bSf3Vc;A1A1A2S35G0Z28A2A2A2F_;").
Proof using . drop_sp.
  assert (AGq : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; flia).
  intros Hin.
  destruct x as [[pr nx| |a0]|]; cbn [meta_slot_cells] in Hin;
    (destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_loc mc_w]; rewrite AGq;
     unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia).
Qed.
Theorem VINv5 : ltac2:(tb__ "0|0|
Se9S9aSe9R1S50Se9Sf0SbaA1S194SbaA1A3A3S1b3R2A1Sf7VL;Vbv1v;R3A3F_;F_;Fc;").
Proof using Cr4 HMI HMI4 HP12 HR2g HSF_match HSF_objs HU HXz4 HagF Hall Hdelta Hdepth HdsC HdsF_DS HdsF_ent Hgd Hml0 Hres Hres64 Hres_r Hsc48 HsmF Hsp Hsp_high Hu UB4 bv1.
  intros c Hc Hm. pose proof (meets_real5 c Hc Hm) as HmR. pose proof (VIN5 c Hc HmR) as H. destruct HmR as (k0 & Hk0 & T0).
  pose proof (cell_spanI X None U s5 L HI5 HXr5 HL5 c Hc) as SP.
  assert (NZ : forall k, (k < mc_w c)%nat -> ~ in_zslots L X (loc_addr L (mc_loc c) + Z.of_nat k)).
  { intros k Hk (q & Hq & Rq). pose proof D5_keys as DK.
    assert (Kq : In q (keys s5)) by (rewrite DK; exact (XS_key4 q ltac:(right; exact Hq))).
    pose proof (meta_zone X None U s5 L HI5 HXr5 HL5 q c Kq Hc ltac:(exists k; split; [exact Hk | exact Rq])) as IN.
    pose proof (msc_inside5 q (MT s5 q) c IN) as [I1 I2].
    apply (touched_nz5 _ T0). exists q. split; [exact Hq|]. unfold META_SIZE. flia. }
  assert (NS : forall k, (k < mc_w c)%nat -> ~ stk4 (loc_addr L (mc_loc c) + Z.of_nat k)).
  { intros k Hk S. pose proof (cell_below_ceiling5 c k Hc Hk). pose proof (stk4_high _ S). flia. }
  assert (E : forall k, (k < mc_w c)%nat -> bv1v (loc_addr L (mc_loc c) + Z.of_nat k) = bv1 (loc_addr L (mc_loc c) + Z.of_nat k)).
  { intros k Hk. unfold bv1v, bv1. apply views_at5. rewrite m5v_nz by (rewrite u64_of_sum by flia; exact (NZ k Hk)). apply m''_nstk. rewrite u64_of_sum by flia. exact (NS k Hk). }
  unfold cell_holds in *. cbn zeta in *.
  destruct (mc_val c); try (intros k Hk; rewrite (E k Hk); exact (H k Hk)).
  destruct H as (b & Hb & Hm5). exists b. split; [|exact Hm5].
  rewrite <- Hb. rewrite <- (Z.add_0_r (loc_addr L (mc_loc c))). change 0 with (Z.of_nat 0). apply E.
  exact (cell_w_posI s5 c Hc).
Qed.

Theorem minvI5 : ltac2:(tb__ "0|0|
S196Se1VX;S4eS4bScS8A2A1VU;S13fSbaVL;A2S106S55S1aeA2S107S55S1aeA2Vvm;A8").
Proof using Cr4 EmW Erd HMI HMI4 HP12 HR2g HSF_match HSF_objs HU HXz4 HZ HZ4 HagF Hall Hcanary4 Hdelta Hdepth HdsC HdsC_g HdsF_DS HdsF_ent Hgd Hgd_holds Hlocs Hml0 Hres Hres64 Hres_r Hsc48 HsmF HsmL Hsp Hsp_high Hu UB4 touched.
  unfold MInvI.
  refine (minv_postG C_U (Inv (g :: X) None U) (Inv X None U) t4 s5 L (Glue.rd_of segsU mv4) (Glue.rd_of segsU m5v) (Glue.wok_of segsU mv4) (Glue.wok_of segsU m5v) vm
            HMI4 HI5 bounded5 HL5 D5_fp D5_ub Hvm5 touchedV5 touchedV5_dec V1v5 VINv5 VMv5 OLD5 _ _ _ statics_in_image_U _ _ _).
  - intros c Hc. exact (cell_spanI X None U s5 L HI5 HXr5 HL5 c Hc).
  - intros x Hx. exact (owned_spanI s5 L HL5 x Hx).
  - intros c Hc. exact (cell_w_posI s5 c Hc).
  -
    intros x [(d & HdC & R)|S] Himg; [|exfalso; pose proof (stk4_high x S); pose proof (ceiling_small L); cbn [mc_img_lo mc_img_hi C_U] in Himg; top_ranges; flia].
    destruct (HdsC d HdC) as (Hd & Hok' & Hchg). pose proof Hctx4 as HCX.
    unfold dhiF in R.
    destruct d as [|x0|fk five pv nv]; [destruct Hchg| |]; cbn [dloF dszF] in R; cbn [od_okF_at] in Hok';
      unfold mc_errno; cbn [mc_img_lo mc_img_hi mc_ctx mc_tp C_U] in *.
    + left. unfold CTX_SIZE. flia.
    + exfalso. destruct Hok' as (Hfc & _). destruct (fptr4_facts fk Hfc) as (Kk & EK & _). pose proof (key_zone4 _ Kk) as ZK. rewrite EK in R. flia.
  - intros x Hx. unfold mc_errno in Hx. cbn [mc_ctx mc_tp mc_libc mc_replaced mc_lock mc_size_classes mc_small_cnt_tab mc_med_cnt_tab mc_ctz_tab mc_chk_guard_got mc_chk_guard C_U] in *.
    unfold CTX_SIZE in Hx. flia.
  - intros Hf. exfalso. rewrite D5_init, init_true4 in Hf. discriminate.
Qed.

Hypothesis HSF_pc : ss_pc SF = 0x20c1c.
Hypothesis HSF_cs : ltac2:(tb__ "0|0|
S8S1S34Z1R1A2S34R1Z1fA2A2S0S45S58S3dR2A1A1S46A3S0S5aS5eVSF;R3A2S59S3dR3A1A1A3F_;F_;Fz;").
Hypothesis HSF_fregs : ltac2:(tb__ "0|0|
S0S4aS5aA1S6eVSF;A1S56A3").
Hypothesis HSF_fcsr : ltac2:(tb__ "0|0|
S0S70S6dVSF;A1S76A3").
Hypothesis HSF_resv : ss_resv SF = None.
Hypothesis HSF_a0 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;ZaA2SdfPb4A1A3").
Hypothesis HSF_a1 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;ZbA2SdfPb5A1A3").

Definition rw' (j : positive) : word := ltac2:(tb__ "0|2|
S45Sa0Q40A1L_;S4cS3fZ64M0SaVj;A1M1A2S40G1Z84A2A2S65VrhoF;S5eVSF;S38G1G0A2A2A2S5cVrho;Vj;A2X45x2").
Definition rho' : valuation := ltac2:(tb__ "0|0|
S86S1b9S96Vrho;A1S1adA3").

Lemma rw'_low j : ltac2:(tb__ "0|0|
S19aVj;P64A2S0Sa0Q40A1S1b9Vj;A1S5cVrho;Vj;A2A3F_;").
Proof using Hgd Hsc48 touched. drop_sp.
  intros Hj. unfold rw'. replace ((100 <=? Z.pos j) && (Z.pos j <? 132))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; flia). reflexivity.
Qed.
Lemma agree_vals_rho' : ltac2:(tb__ "0|0|
S1c0S57Vrho;S1b8A3").
Proof using Hgd Hsc48 touched. drop_sp. split; [|reflexivity]. intros j Hj. cbn [rw rho']. symmetry. apply rw'_low. exact Hj. Qed.
Lemma rwF_low4 j : ltac2:(tb__ "0|0|
S19aVj;P64A2S0Sa0Q40A1S5cVrhoF;Vj;A2S5cVrho;Vj;A2A3F_;").
Proof using HagF Hgd Hsc48 Hsp touched. try clear Hsp_high. try clear Hdepth.
  intros Hj. rewrite (rw_agrees rhoN rhoF j HagF) by (unfold below200; apply Pos.ltb_lt; flia).
  cbn [rw rhoN]. apply rwN_low. exact Hj.
Qed.
Lemma pre_reg_lt z : ltac2:(tb__ "0|1|
S1S34Z1Vz;A2S34Vz;Z1fA2A2S0S45S58S3dVz;A1M0A1S46A3S3S9S9S1S0S5aS59G0A1S61R1A1A3S19aR1P64A2A2Lvv;A2F_;F_;").
Proof using Hgd Hsc48 rho touched. drop_sp.
  intros Hr Hcs.
  pose proof (forall_range_dec (fun z => negb (callee_saved (Z.to_nat z)) || match pre_reg (Z.to_nat z) with SVar vv => (vv <? 100)%positive | _ => false end)%bool 1 31
                ltac:(vm_compute; reflexivity) z ltac:(flia)) as XX.
  cbn beta in XX. rewrite Hcs in XX. cbn [negb orb] in XX.
  destruct (pre_reg (Z.to_nat z)) as [|vv| | | | | |]; try discriminate.
  exists vv. split; [reflexivity|]. apply Pos.ltb_lt in XX. exact XX.
Qed.
Lemma freg_sv_L4 z : ltac2:(tb__ "0|2|
S1S34Z0M0Vz;A2S34Vz;Z1fA2A2S3S9S9S1S0S5aS8eS156S151A1Vz;A2S61R1A1M1A3S1S0S5aS179S5aS3dVz;A1S56S5dG0A1A4G1A3S1S199P3cR1A2S19aR1P64A2A2A2A2Lvv;A2F_;").
Proof using Hgd Hsc48 rho touched. drop_sp.
  intros Hz. destruct (pre_freg_tableN z Hz) as (vv & E & R1 & R2). exists vv.
  unfold freg_sv. change (ss_fregs (L_nt NTE_U)) with pre_fregs. rewrite E. split; [reflexivity|]. split; [reflexivity|]. flia.
Qed.

Lemma HOF_stk : ltac2:(tb__ "0|0|
S64S55VrhoF;VmsF;S1b0A4").
Proof using HSF_objs HsmF. drop_sp.
  pose proof HsmF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HallF & _ & _) & _). cbn [fst snd cfg_ms] in HallF.
  rewrite HSF_objs in HallF. apply Forall_cons_iff in HallF as [H0 _]. exact H0.
Qed.
Lemma HfrF a : ltac2:(tb__ "0|0|
S93VrhoF;S43S5bS1b0S1b6A3Va;A3S0S44Sa0Q8A1A1S1e6VmsF;Va;A2S5fVrhoL;Va;A2A3F_;").
Proof using HSF_match HSF_objs HagF HsmF. drop_sp.
  exact (WalkReab.HfrF segsU rhoN odF obj_ofF (rm rhoL) EmN tr md msF rhoF HagF SF oStkF4 objsF dsF HSF_objs HSF_match HsmF a).
Qed.

Theorem smatch_ok : ltac2:(tb__ "0|0|
S66S55S1b8S156S151A1S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4A4").
Proof using HSF_cs HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HagF Hdepth Hgd Hres Hres64 Hres_r Hsc48 HsmF Hsm_pre Hsp i touched. try clear Hsp_high.
  pose proof HsmF as (Hswf & Hpc & Hpend & Hhalt & HromX & HroX & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  pose proof sp0_range4 as SPR. pose proof D0_range4 as DR.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [vm_compute; reflexivity|].
  split; [rewrite Hpc, HSF_pc; reflexivity|].
  split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact HromX|]. split; [exact HroX|].
  split.
  {   intros r Hr0. rewrite (Hr r Hr0).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; flia).
    rewrite reg_sv_Lnt by flia.
    destruct (callee_saved (Z.to_nat (bv_unsigned r))) eqn:CS.
    - destruct (pre_reg_lt (bv_unsigned r) ltac:(flia) CS) as (vv & E & Hv100).
      rewrite (HSF_cs (bv_unsigned r) ltac:(flia) CS), E.
      cbn [eval rho' rw]. rewrite rw'_low by exact Hv100. apply rwF_low4. exact Hv100.
    - cbn [eval rho' rw]. unfold rw'.
        replace ((100 <=? Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r)))) && (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) <? 132))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; flia).
        replace (Z.pos (100 + Pos.of_nat (Z.to_nat (bv_unsigned r))) - 100) with (bv_unsigned r) by flia.
        reflexivity. }
  split.
  {   intros r. rewrite (Hf r).
    assert (UR : 0 <= bv_unsigned r < 32) by (pose proof (urange_n 5 r) as U0; cbn in U0; flia).
    destruct (freg_sv_L4 (bv_unsigned r) ltac:(flia)) as (vv & E1 & E2 & Hvv). rewrite E1.
    unfold freg_sv. rewrite HSF_fregs, E2.
    cbn [eval rho' rw]. rewrite rw'_low by flia. apply rwF_low4. flia. }
  split; [rewrite HSF_fcsr in Hc; exact Hc|].
  split; [unfold resv_match in *; rewrite HSF_resv in Hv; exact Hv|].
  split.
  {
    pose proof HOF_stk as HOS.
    assert (EB : eval rho' (SVar 10) = eval rhoF (SVar 10)) by (cbn [eval rho' rw]; rewrite rw'_low by flia; symmetry; apply rwF_low4; flia).
    assert (EL : soff rho' (SVar V_DEPTH) = soff rhoF (SVar 15)) by (unfold soff, V_DEPTH; cbn [eval rho' rw]; rewrite rw'_low by flia; rewrite (rwF_low4 15) by flia; reflexivity).
    assert (E10 : bv_unsigned (eval rhoF (SVar 10)) = sp0) by (cbn [eval]; rewrite (rwF_low4 10) by flia; reflexivity).
    assert (E15 : soff rhoF (SVar 15) = D0) by (unfold soff; cbn [eval]; rewrite (rwF_low4 15) by flia; rewrite bv_signed_toS by (cbn; flia); reflexivity).
    split; [|split].
    - constructor; [|constructor].
      apply obj_holds_drop_cells in HOS.
      destruct HOS as (B1 & B2 & B3 & B4 & B5). unfold stack_win, obj_holds, obj_lo_of, obj_hi_of in *.
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt oStkF4] in *.
      rewrite EB, EL. split; [exact B1|]. split; [exact B2|]. split; [constructor|]. split; [|exact I].
      intros z Hz Hnc. apply B4; [exact Hz|]. intros Cv. inversion Cv.
    - cbn. split; [constructor | exact I].
    - intros a Ha. cbn [rm rho']. apply Forall_cons_iff in Ha as [HaS _].
      cbn zeta in HaS. unfold obj_range, obj_lo_of, obj_hi_of, stack_win in HaS. cbn [ob_base ob_lo ob_hi fst snd] in HaS.
      rewrite EB, EL, E10, E15, soff_lit_small in HaS by flia.
      rewrite m''_nstk by (unfold stk4; flia).
      destruct (in_ranges_dec rhoF NRELF a) as [IN|OUT].
      + unfold m', WalkReab.m'. rewrite (release_in _ _ _ _ IN). reflexivity.
      + unfold m', WalkReab.m'. rewrite (release_out _ _ _ _ OUT).
        rewrite (proj2 (proj2 HagF)). change (rm rhoN) with (rm rhoL). apply HfrF. constructor.
        * cbn zeta. unfold obj_range, obj_lo_of, obj_hi_of, oStkF4. cbn [ob_base ob_lo ob_hi fst snd]. rewrite E10, E15, soff_lit_small by flia. exact HaS.
        * apply Forall_forall. intros o Ho. cbn zeta. intros R. apply OUT. exists o. auto. }

  unfold L_nt. cbn [ss_facts].
  assert (AGR : forall f, sprop_below NF f = true -> SymState.holds rho f -> SymState.holds rho' f).
  { intros f Hb Hh. exact (proj1 (holds_agree_vals NF rho rho' f agree_vals_rho' Hb) Hh). }
  pose proof Hsm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF0). cbn [ss_facts ContractNT.Pre_nt] in HF0.
  cbn [app]. repeat (constructor; [apply AGR; [reflexivity|]; apply (proj1 (Forall_forall _ _) HF0); inlist|]). constructor.
Qed.

Lemma owned54 a : ltac2:(tb__ "0|0|
S5Sf4VL;Vt4;Va;A3Sf4VL;SbaVa;A3A2").
Proof using Hdelta Hdepth Hgd Hres Hres64 Hres_r Hsc48 Hsp i touched. try clear Hsp_high. unfold alloc_owned, in_footprint, in_user_block. rewrite D5_fp, D5_ub. tauto. Qed.
Lemma KEYOWN4 q a : ltac2:(tb__ "0|1|
S9aScVq;SedVt4;A1A3S1S34Se0VL;Vq;A2M0Va;A2S36Va;S35G0Z28A2A2A2Sf4VL;Vt4;Va;A3F_;F_;").
Proof using HMI4 HXz4 Hgd Hsc48 Hsp touched. try clear Hsp_high. try clear Hdepth.
  intros Hq Hx.
  assert (C6 : forall off (w : nat) vv, In (MCell (LMem (padd q off)) w vv) (meta_slot_cells q (MT t4 q)) ->
             addr_of L q + off <= a < addr_of L q + off + Z.of_nat w -> alloc_owned L t4 a).
  { intros off w vv Hin Hx'.
    pose proof (image_cell_owned (g :: X) None U t4 L HI4 HXr4 HL4 _ (meta_cells_in_imageI (g :: X) None U t4 HI4 q _ Hq Hin) (Z.to_nat (a - (addr_of L q + off))) ltac:(cbn [mc_w]; flia)) as OW.
    cbn [mc_loc] in OW. replace (loc_addr L (LMem (padd q off)) + Z.of_nat (Z.to_nat (a - (addr_of L q + off)))) with a in OW; [exact OW|].
    unfold addr_of, loc_addr. destruct q; cbn [padd]. unfold addr_of in Hx'. cbn in Hx'. flia. }
  assert (SLOTS : forall x, exists v0 v1 v2 v3 v4 v5, meta_slot_cells q x =
            [MCell (LMem (padd q 0)) 8 v0; MCell (LMem (padd q 8)) 8 v1; MCell (LMem (padd q 16)) 8 v2;
             MCell (LMem (padd q 24)) 4 v3; MCell (LMem (padd q 28)) 4 v4; MCell (LMem (padd q 32)) 8 v5]).
  { intros [[pr nx| |a0]|]; cbn; do 6 eexists; reflexivity. }
  destruct (SLOTS (MT t4 q)) as (v0 & v1 & v2 & v3 & v4 & v5 & ES). rewrite ES in C6.
  destruct (Z_lt_dec a (addr_of L q + 8)); [eapply (C6 0 8%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia]|].
  destruct (Z_lt_dec a (addr_of L q + 16)); [eapply (C6 8 8%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia]|].
  destruct (Z_lt_dec a (addr_of L q + 24)); [eapply (C6 16 8%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia]|].
  destruct (Z_lt_dec a (addr_of L q + 28)); [eapply (C6 24 4%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia]|].
  destruct (Z_lt_dec a (addr_of L q + 32)); [eapply (C6 28 4%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia]|].
  eapply (C6 32 8%nat); [inlist | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; flia].
Qed.
Lemma ctx_owned4 off : ltac2:(tb__ "0|0|
S1S34Z0Voff;A2S36Voff;SfeA2A2Sf4VL;Vt4;S35S101VL;A1Voff;A2A3F_;").
Proof using HMI HMI4 HR2g HU HXz Hall Hgd Hml0 Hsc48 Hsp Hu UB4 touched. try clear Hsp_high. try clear Hdepth.
  intros Ho. pose proof (ctx_owned off Ho) as [_ NU]. split.
  - exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. flia.
  - intros (b & Hb & R). apply NU. exists b. split; [|exact R].
    rewrite <- (ub_same_user_blocks s t4 (proj1 (inv_keys HI)) ND4 (ub_same_trans _ _ _ ub3v UB4)). exact Hb.
Qed.

Theorem kept : ltac2:(tb__ "0|0|
S204Se1S13fVs;VL;A2S13fSbaVL;A2S5fVrho;A1S1adA5").
Proof using HMI HMI4 HP12 HR2g HU HXz HXz4 HagF Hall Hdelta Hdepth HdsC HdsF_DS HdsF_ent Hgd Hkept4 Hml0 Hres Hres64 Hres_r Hsc48 Hsp Hu UB4 touched. try clear Hsp_high.
  intros a Ha NO NO' NE NS.
  destruct (stkb4 a) eqn:Sa; [unfold m''; rewrite u64_of_sum by flia; rewrite Sa; reflexivity|].
  assert (NSK : ~ stk4 a) by (intros S; rewrite (proj2 (stkb4_spec a) S) in Sa; discriminate).
  rewrite m''_nstk by (rewrite u64_of_sum by flia; exact NSK). unfold m'.
  assert (OWN : alloc_owned L t4 a -> False) by (intros H; apply NO'; unfold ma_owned, owned; cbn [ma_s ma_L]; left; exact (proj1 (owned54 a) H)).
  destruct (in_ranges_dec rhoF NRELF (Z_to_bv 64 a)) as [IN|OUT].
  2:{ rewrite (m'_outF a Ha) by (intros d Hd R; apply OUT; exists (obj_ofF d); split; [apply in_map; exact Hd|]; rewrite (rngDF d rhoF (HdsF5 d Hd) HagF); cbn [fst snd]; rewrite u64_of_sum by flia; exact R).
      apply Hkept4; [exact Ha | exact NO | | exact NE | exact NS | exact NSK].
      unfold ma_owned, owned. cbn [ma_s ma_L]. intros [H|H]; [exact (OWN H)|]. apply NO'. unfold ma_owned, owned. cbn [ma_s ma_L]. right. exact H. }
  exfalso.
  unfold in_ranges in IN. destruct IN as (o & Ho & R). unfold NRELF in Ho. apply in_map_iff in Ho as (d & <- & Hd).
  rewrite (rngDF d rhoF (HdsF5 d Hd) HagF) in R. rewrite u64_of_sum in R by flia. cbn [fst snd] in R. unfold dhiF in R.
  pose proof Hctx4 as HCX.
  destruct d as [|x|fk five pv nv]; cbn [dloF dszF] in R.
  - apply NS. unfold alloc_static. cbn. right; right. flia.
  - apply OWN. replace a with (ly_ctx L + (a - ly_ctx L)) by flia. apply ctx_owned4. rewrite HCX. unfold CTX_SIZE. flia.
  - assert (Hfc : fcond4 fk).
    { destruct (HdsF_ent _ Hd) as [[_ Hok]|HdC]; [|destruct (HdsC _ HdC) as (_ & Hok & _)]; cbn [od_okF_at] in Hok; exact (proj1 Hok). }
    destruct (fptr4_facts fk Hfc) as (Kk & EK & _). apply OWN. apply (KEYOWN4 (fptr4 fk) a Kk). rewrite EK in R. flia.
Qed.

Lemma canary_untouched x : ltac2:(tb__ "0|3|
S4S1S34Z28d50M0Vx;A2S36Vx;S35G0Z8M1A2A2A2S1S34Z5a338M2Vx;A2S36Vx;S35G2G1A2A2A2A2S2Vtouched;Vx;A1A1F_;").
Proof using HMI4 HXz4 HdsC Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros Hx (d & HdC & R). destruct (HdsC d HdC) as (Hd & Hok' & Hchg). pose proof Hctx4 as HCX.
  unfold dhiF in R.
  destruct d as [|x0|fk five pv nv]; [destruct Hchg| |]; cbn [dloF dszF] in R; cbn [od_okF_at] in Hok'.
  - flia.
  - destruct Hok' as (Hfc & _). destruct (fptr4_facts fk Hfc) as (Kk & EK & _). pose proof (key_zone4 _ Kk) as ZK. rewrite EK in R. flia.
Qed.
Theorem canary : ltac2:(tb__ "0|0|
S1e8S55Se1S5fVrho;A1S1adA4").
Proof using EmW Erd HMI HMI4 HP12 HSF_match HSF_objs HXz4 HZ HZ4 HagF Hcanary4 Hdepth HdsC HdsF_DS HdsF_ent Hgd Hgd_holds Hres Hres64 Hres_r Hsc48 HsmF HsmL Hsp Hsp_high Hu touched.
  intros a Ha. cbn [mc_chk_guard_got mc_chk_guard C_U] in Ha.
  assert (Ra : 0 <= a < 2 ^ 64) by flia.
  rewrite <- (Hcanary4 a Ha).
  assert (NSK : ~ stk4 a) by (intros S; pose proof (stk4_high a S); pose proof (ceiling_small L); top_ranges; flia).
  destruct (V1F a Ra (canary_untouched a Ha)) as [_ E]. unfold rv1, byteview_of in E.
  replace ((0 <=? a) && (a <? 2 ^ 64) && true)%bool with true in E
    by (symmetry; rewrite andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; flia).
  change (Glue.rd_of segsU m'' (Z_to_bv 64 a) = Glue.rd_of segsU (rm rhoL) (Z_to_bv 64 a)).
  unfold Glue.rd_of. rewrite m''_nstk by (rewrite u64_of_sum by flia; exact NSK). fold (Glue.rd_of segsU m' (Z_to_bv 64 a)). fold (Glue.rd_of segsU (rm rhoL) (Z_to_bv 64 a)).
  destruct (Glue.rd_of segsU m' (Z_to_bv 64 a)) as [b1|]; destruct (Glue.rd_of segsU (rm rhoL) (Z_to_bv 64 a)) as [b0|]; try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

Lemma Hz4_eq : ltac2:(tb__ "0|0|
S0S10Vt4;S1f4S43ScVg;VX;A3Vt4r;A2A3"). Proof using Hz4. exact Hz4. Qed.
Definition s5r : astate := fin_real g t4r.
Lemma gX4 : ltac2:(tb__ "0|0|
S0S45S102Vg;VX;A2S4dA3"). Proof using Hu. exact (proj2 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma s5_real : ltac2:(tb__ "0|0|
S0S10SbaS1f4VX;S1b4A2A3").
Proof using HI4r Hu Hz4. drop_sp. unfold s5, s5r, fgn_s5. rewrite (fin_real_zomb X U g t4r HI4r gX4), <- Hz4_eq. reflexivity. Qed.
Lemma ntf_level F : ltac2:(tb__ "0|2|
S17aS1f2S15eVam;A1A1VF;A2S0S27S10S4bS44S4bS48S8A2A1M0S10A2M1A2S28VF;Vg;Vi;Vsr;A4S25S10G1S49G0S10Vr4;S1b4A4A3A3F_;").
Proof using HI4r HIr HMI HR2g HU Hall Heq4 Hgd Hml0 Hsc48 Hsp Hu Hzs touched. try clear Hsp_high. try clear Hdepth.
  intros HF. pose proof (fneed_pos sc) as P. destruct F as [|F']; [flia|].
  exact (ntf_nested F' r4 t4r s5r (Heq4 F' (fneed_par F' HF)) (free_meta_real X U g t4r HI4r)).
Qed.
Lemma nf_level : ltac2:(tb__ "0|0|
S1f3VX;VU;Vsr;S49S44S4bS48S8A2A1S10Vr4;S1b4A4A4").
Proof using HI4r HIr HMI HR2g HU Hall Heq4 Hgd Hml0 Hsc48 Hsp Hu Hzs touched. try clear Hsp_high. try clear Hdepth.
  pose proof (nontrivial_free_spec NEST_FUEL X U sr g i am (nf_post X U sr) HIr Hur HU
                ltac:(intros H1 H2; apply (HR2g H1); rewrite Hzs_eq, active_hd_zomb; exact H2) (fneed_le _ (proj1 Hsc48am)) (fun r Hr => Hr)) as T.
  unfold NEST_FUEL in T. rewrite (ntf_level 64%nat (fneed_le _ (proj1 Hsc48am))) in T. exact T.
Qed.

Theorem post_okF : ltac2:(tb__ "0|0|
S1bcS55S57Vrho;S153S55Se1S151VX;VU;S13fVsr;VL;A2VKc;A7S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4A5").
Proof using Cr4 EmW Erd Evm HI4r HIr HK4 HKc HMI HMI4 HP12 HP13 HR2g HSF_a0 HSF_a1 HSF_cs HSF_fcsr HSF_fregs HSF_match HSF_objs HSF_pc HSF_resv HU HXz HXz4 HZ HZ4 HagF Hall Hcanary4 Hdelta Hdepth HdsC HdsC_g HdsF_DS HdsF_ent Heq4 Hgd Hgd_holds Hkept4 Hlocs Hml0 Hreach4 Hres Hres64 Hres_r Hsc48 HsmF HsmL Hsm_pre Hsp Hsp_high Hu Hxk4 Hz4 Hzs UB4 bv1 bv1v bv4 rv1 rv1v rv4 touched.
  destruct (HKc _ _ HK4) as (HKc' & _ & _).
  pose proof FIN5 as (_ & Hcorr & Hub & _ & _ & Erg & EU).
  pose proof nf_level as (HI5r & Hcorr_r & Hub_r & _). cbn [fst snd] in HI5r, Hcorr_r, Hub_r.
  exists (L_nt NTE_U), (JL_nt segsU C_U X U (mkMA sr L) Kc), rho'.
  split; [left; reflexivity|].
  split; [exact agree_vals_rho'|].
  split; [exact smatch_ok|].
  cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
  unfold JL_nt, zv. cbn [ma_s ma_L].
  exists (mkMA s5r L), m5v, r4. cbn [ma_s ma_L]. rewrite <- s5_real, <- Hzs_eq.
  split. { rewrite <- Evm. exact minvI5. }
  split; [cbn [rm rho']; exact magree_post5|].
  split; [reflexivity|].
  split; [rewrite <- (st_init_done_zomb X s5r), <- s5_real, D5_init; exact init_true4|].
  split; [exact HI5r|].
  split. { intros x Hx. unfold s5r. rewrite (fin_real_X X U g t4r HI4r gX4 x Hx), (Hxk4 x ltac:(right; exact Hx)). unfold s3r. exact (s3r_XW X sr s g am Hzs Hu HR2g Hlinks3 HnU3 HpU3 Hact3' HactU3' gPar amPar iPar HuP x Hx). }
  split; [exact Hcorr_r|]. split; [exact Hub_r|]. split; [exact Hreach5|].
  split.
  { cbn [rw rho']. unfold rw', V_RES, V_RES1. cbn -[eval reg_sv]. change (111 - 100) with 11. change (110 - 100) with 10. rewrite HSF_a0, HSF_a1.
    rewrite (EV rhoN zrN zlN HzrN HzlN rhoF (v 180) HagF eq_refl eq_refl), (EV rhoN zrN zlN HzrN HzlN rhoF (v 181) HagF eq_refl eq_refl), !zeNv, zeN_180, zeN_181.
    pose proof Hres64 as R64. rewrite !u64_of_sum by flia.
    destruct Hres_r as [H0|(k & rg & Hr4 & Hlen & R1 & R2 & R3 & R4 & R5 & Hno)]; [left; exact H0|].
    right. exists k, rg. split; [exact Hr4|]. split; [exact Hlen|].
    rewrite <- (region_of_zomb X s5r k), <- s5_real, region_of5, Hz4_eq, region_of_zomb.
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    intros q a Hq. apply (Hno q a). apply (proj1 (usedX_zomb (g :: X) t4r q a)). rewrite <- Hz4_eq. apply (proj1 (EU q a)).
    rewrite s5_real. apply (proj2 (usedX_zomb X s5r q a)). exact Hq. }
  split.
  { intros g0 am0 F Hg0 Hu0 HF. rewrite HP12 in Hg0.
    assert (Hu0' : usedX X s g0 am0) by (rewrite Hzs_eq; apply (proj2 (usedX_zomb X sr g0 am0)); exact Hu0).
    destruct (used_at_addr X (Some (g, i)) U s L HI HL g am g0 am0 Hu Hu0' Hg0) as [-> ->].
    rewrite HP13. exact (ntf_level F HF). }
  split; [cbn [rm rho']; exact kept|]. split; [cbn [rm rho']; exact canary | exact HKc'].
Qed.
End ReabF.

Definition regs_okbF (SF : sstate) : bool := ltac2:(tb__ "0|1|
S4cS4cS9bS8S8S54S51S58S3dR1A1M0A1A1S63S5eVSF;R1A2S59G0A1A2A2Lz;S105Z1Z1fA2A3S63S5eVSF;ZaA2SdfPb4A1A2A2S63S5eVSF;ZbA2SdfPb5A1A2A2").
Lemma regs_okbF_sound SF : ltac2:(tb__ "0|0|
S0S45SceVSF;A1S46A3S1S8S1S34Z1R1A2S34R1Z1fA2A2S0S45S58S3dR2A1A1S46A3S0S5aS5eVSF;R3A2S59S3dR3A1A1A3F_;F_;Fz;S1S0S5aS5eVSF;ZaA2SdfPb4A1A3S0S5aS5eVSF;ZbA2SdfPb5A1A3A2A2F_;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros H. unfold regs_okbF in H. apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply sv_eqb_sound in H10. apply sv_eqb_sound in H11. split; [|auto].
  intros z Hz Hcs. rewrite forallb_forall in H. specialize (H z ltac:(apply zseq_In; flia)). rewrite Hcs in H. cbn [negb orb] in H.
  apply sv_eqb_sound in H. exact H.
Qed.
Definition leaf_okbF (SF : sstate) (ds : list odF) : bool := ltac2:(tb__ "0|2|
S4cS4cS4cS4cS4cS4cS4cS1a1S9cS5bS6bVSF;A1M0A2S178Sb9S5bSbdVds;A4A2S9bSb9SccVds;A3A2S39S74VSF;A1Z20c1cA2A2SceVSF;A1A2S1d5S6eVSF;A1S56A2A2S70S45Lx;S6dVSF;A1S46S5aS4dLv;X70x2A2S44S5aA1S45Lx;S75VSF;A1S5aS4dLs0;S46X44x2A2S4aS5bA1M1S45Lx;G0S4dS5bG1S4cS4cS4cS63S7cR2A1S61PaA1A2S63S81R2A1S61PfA1A2A2S63S80R2A1S5dZ0A1A2A2S1fcS7dR2A1S71A2A2Ll;Lo;X4ax2A2").
Lemma leaf_okbF_sound SF ds : ltac2:(tb__ "0|2|
S0S45Sd6VSF;Vds;A2S46A3S1S0S4aS5bA1S6bVSF;A1M0S43S5bSdcS73S9eS5bS181G0A3A1A1S9cS5bG0A2M1A3A3S1S0S45S1a1G1S178Sb9S5bSbdVds;A4A2S46A3S1S0S45S9bSb9SccVds;A3S46A3S1S0S8S74VSF;A1Z20c1cA3S1S0S45SceVSF;A1S46A3S1S0S4aS5aA1S6eVSF;A1S56A3S1S0S70S6dVSF;A1S76A3S0S44S5aA1S75VSF;A1S4eS5aA1A3A2A2A2A2A2A2A2F_;").
Proof using EmW Erd Evm Ewok HIr HMI HMI4 HP13 HP13w HZ Hall Hgd_holds Hstk. drop_sp.
  intros H. unfold leaf_okbF in H.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (ss_objs SF) as [|o t] eqn:Eo; [discriminate|].
  apply andb_prop in H8 as [H8 Hd]. apply andb_prop in H8 as [H8 Hh]. apply andb_prop in H8 as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  split. { cbn [hd tl]. unfold oStkF4. destruct o as [b lo hi cs df]; cbn in Hb, Hl, Hh, Hd |- *. subst. destruct df; try discriminate. reflexivity. }
  split; [exact H1|]. split; [exact H2|]. split; [apply Z.eqb_eq; exact H3|]. split; [exact H4|].
  split; [apply svl_eqb_sound; exact H5|].
  split; [destruct (ss_fcsr SF); try discriminate; reflexivity|].
  destruct (ss_resv SF); [discriminate | reflexivity].
Qed.

Definition dsF_of (f : nat) : list odF := ltac2:(tb__ "0|5|
S48S4aSb9A1M0Lf;Vf;S43Sb9SbfSc2S46SdfPcA1M1G1A4S43Sb9Sc9S43Sb9Sc8G1A1S4fSb9A1M2A3A3A3S48S48G0Ln;R1S43Sb9SbfSc2S46SdfPa0A1M3G3A4S43Sb9Sc9S43Sb9Sc8G3A1M4S43Sb9SbfSc4S4dG1G1A4G2A3A3A3A3S48S43Sb9SbfSc2S46SdfPa1A1G3A4S43Sb9Sc9S43Sb9G4S43Sb9SbfSc4S4dG1SdfPa2A1A4S43Sb9SbfScfS4dSdfPa3A1G1A4G2A3A3A3A3A3Ln0;X48x2Ln;X48x2").
Definition dsC_of (f : nat) : list odF := ltac2:(tb__ "0|4|
S48S4aSb9A1M0Lf;Vf;S43Sb9SbfSc2S46SdfPcA1M1G1A4S43Sb9Sc8G1A1S4fSb9A1M2A3A3S48S48G0Ln;R1S43Sb9SbfSc2S46SdfPa0A1M3G3A4S43Sb9SbfSc4S4dG1G1A4G2A3A3S48S43Sb9SbfSc2S46SdfPa1A1G3A4S43Sb9SbfSc4S4dG1SdfPa2A1A4S43Sb9SbfScfS4dSdfPa3A1G1A4G2A3A3A3Ln0;X48x2Ln;X48x2").
Lemma L_okbF f : ltac2:(tb__ "0|0|
S17aVf;U2A2S0S45Sd6S192S20cVf;A1U0S17fVf;A1A3SdaVf;A1A2S46A3F_;").
Proof using Hgd Hsc48 rho. drop_sp. intros Hf. destruct f as [|[|[|f]]]; [vm_cast_no_check (@eq_refl bool true) .. | flia]. Qed.

Lemma AGg5 dd : ltac2:(tb__ "0|0|
S0S8SecVL;SfbS2aVg;Vdd;A2A1A2S35S15dVL;Vg;A2Vdd;A2A3").
Proof using Cr4 HI4r HIr HMI HMI4 HP12 HR2g HXz4 HZ4 Heq4 HrL39 Hres Hres_r Hstk Hu Hxk4 Hz4 UB4. drop_sp. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, addr_of, loc_addr. destruct g; cbn [padd]; flia. Qed.
Lemma meta_locs_in4 q l : ltac2:(tb__ "0|2|
S9aSeaVl;S1cfVq;A1A3S1S34Se0VL;Vq;A2M0SecVL;Vl;A2M1A2S36G1S35G0Z28A2A2A2F_;").
Proof using . drop_sp.
  assert (AGq : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; flia).
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AGq; flia.
Qed.

Theorem phaseF : ltac2:(tb__ "0|0|
VTR;S175S55VK;S17fS131Vg;Vt4;A2A1S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaA4S1bcS55S57Vrho;S153S55Se1S151VX;VU;S13fVsr;VL;A2VKc;A7A4A2").
Proof using Cr4 EmW Erd Evm Ewok HI4r HIr HK4 HKc HMI HMI4 HP12 HP13 HP13w HR2g HU HXz HXz4 HZ HZ4 Hall Hcanary4 Hdepth Heq4 Hgd Hgd_holds Hkept4 Hml0 Hreach4 Hres Hres64 Hres_r Hsc48 HsmL Hsm_pre Hsp Hsp_high Hstk Hu Hxk4 Hz4 Hzs TR_run UB4 bv4.
  pose proof fshape4_le as HF.
  apply (TR_run rhoN CUTS0 300 (S_t2n_of fshape4) (L_t2n fshape4) _ rhoN
           ltac:(destruct fshape4 as [|[|ff]]; reflexivity) ltac:(destruct fshape4 as [|[|ff]]; unfold Pos.le; cbv; discriminate) (run_t2n fshape4 HF) (agrees_refl rhoN)).
  intros Lf rhoF [tr' [msF md']] Hin HagF HSP. pose proof HSP as [HsmF HK']. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmF, HK'.
  destruct (HKc _ _ HK') as (HKc' & -> & ->).
  assert (ELf : Lf = nth 0 (L_t2n fshape4) (mkLeaf (S_t2n_of fshape4) RsFuel)).
  { pose proof (L_t2n_len fshape4) as LEN. destruct (L_t2n fshape4) as [|a [|]]; try discriminate. destruct Hin as [<-|[]]. reflexivity. }
  assert (ESF : lf_state Lf = lfs (L_t2n fshape4) 0 (S_t2n_of fshape4)) by (rewrite ELf; reflexivity).
  rewrite ESF in HsmF.
  destruct (leaf_okbF_sound _ _ (L_okbF fshape4 HF)) as (Ho & Hm & Hds & Hpc & Hrg & Hfr & Hfc & Hrs).
  destruct (regs_okbF_sound _ Hrg) as (Hcs & Ha0 & Ha1).
  pose proof (ceiling_small L) as CS. pose proof Hctx4 as HCX.
  destruct fshape4_cases as [(EF & E & Efm & EzF)|(fm & hp & nx & pr2 & nx2 & E & Efm & Mfm & EL & Eft & Mhp & ELt & Nfm & Nhp & Kfm & Khp & Knx & Kpr2 & Knx2 & EzF & EzFp & EzFn & EzTp & EzTn & SH)].
  -
    rewrite EF in *. cbn [dsF_of] in Hm, Hds.
    refine (post_okF msF rhoF HagF _ _ _ (dsF_of 0) (dsC_of 0) Ho Hm HsmF Hds _ (meta_locs g ++ [LCtx CTX_free_meta_head]) _ _ _ _ Hpc Hcs Hfr Hfc Hrs Ha0 Ha1).
    + intros d Hd. cbn [dsF_of] in Hd. destruct Hd as [<-|[<-|[<-|[]]]]; [right; inlist | left | right; inlist].
      split; [reflexivity | exact I].
    + rewrite s5_eq. exact (delta_fq_empty t4 g ND4 Mg4 E).
    + intros d Hd. cbn [dsC_of] in Hd. destruct Hd as [<-|[<-|[]]]; (split; [inlist|]); (split; [|exact I]); cbn [od_okF_at fcond4 fptr4].
      * split; [exact I|]. exists (Some g), (Some g). rewrite s5_eq, (MT_fq_empty_g t4 g E). split; [reflexivity|]. split; [discriminate|].
        split; [intros p Hp; injection Hp as <-; exact Kg4|]. split; [intros p Hp; injection Hp as <-; exact Kg4|]. rewrite zeNv, zeN_12. split; reflexivity.
      * rewrite s5_eq, (head_fq_empty t4 g E). rewrite zeNv, zeN_12. reflexivity.
    + intros l Hl. apply in_app_iff in Hl as [Hl|[<-|[]]].
      * exists (FD_free K4g true (v 12) (v 12)). split; [inlist|]. pose proof (meta_locs_in4 g l Hl). unfold dhiF; cbn [dloF dszF flo4]. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG. flia.
      * exists (FD_fmh (v 12)). split; [inlist|]. unfold dhiF; cbn [dloF dszF loc_addr]. rewrite HCX. unfold CTX_free_meta_head. flia.
    + exists true, (v 12), (v 12). inlist.
  - destruct SH as [[EF Ehp]|[EF Nhf]]; rewrite EF in *; cbn [dsF_of] in Hm, Hds.
    +
      rewrite Ehp in Eft, Mfm, EL, Mhp, Nhp, Khp, EzFp. clear Ehp.
      refine (post_okF msF rhoF HagF _ _ _ (dsF_of 1) (dsC_of 1) Ho Hm HsmF Hds _ ((meta_locs g ++ meta_locs fm) ++ meta_locs fm) _ _ _ _ Hpc Hcs Hfr Hfc Hrs Ha0 Ha1).
      * intros d Hd. cbn [dsF_of] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; [right; inlist | left | left | right; inlist].
        -- split; [reflexivity | exact I].
        -- split; [reflexivity|]. cbn [od_okF_at]. rewrite zeNv, zeN_160, Efm. unfold zF4 in EzF. rewrite E. cbn [optrA]. reflexivity.
      * rewrite s5_eq. exact (delta_fq_ring t4 g ND4 Mg4 fm fm nx pr2 nx2 E Mfm Mhp Nfm Nfm).
      * intros d Hd. cbn [dsC_of] in Hd. destruct Hd as [<-|[<-|[]]]; (split; [inlist|]); (split; [|exact I]); cbn [od_okF_at fcond4 fptr4].
        -- split; [exact I|]. exists (Some fm), (Some fm). rewrite s5_eq, (MT_fq_g t4 g fm fm nx pr2 nx2 E Mfm Mhp Nfm Nfm). split; [reflexivity|]. split; [discriminate|].
           split; [intros p Hp; injection Hp as <-; exact Kfm|]. split; [intros p Hp; injection Hp as <-; exact Kfm|]. rewrite !zeNv, zeN_160, Efm. split; reflexivity.
        -- split; [rewrite E; discriminate|]. exists (Some g), (Some g). rewrite Efm, s5_eq, (MT_fq_fm t4 g fm fm nx pr2 nx2 E Mfm Mhp Nfm Nfm).
           unfold fq_next'. rewrite sptr_eqb_refl. split; [reflexivity|]. split; [discriminate|].
           split; [intros p Hp; injection Hp as <-; exact Kg4|]. split; [intros p Hp; injection Hp as <-; exact Kg4|]. rewrite !zeNv, zeN_12. split; reflexivity.
      * intros l Hl. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|].
        -- exists (FD_free K4g true (v 160) (v 160)). split; [inlist|]. pose proof (meta_locs_in4 g l Hl). unfold dhiF; cbn [dloF dszF flo4]. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG. flia.
        -- exists (FD_free K4m false (v 12) (v 12)). split; [inlist|]. pose proof (meta_locs_in4 fm l Hl). unfold dhiF; cbn [dloF dszF flo4]. rewrite Efm. flia.
        -- exists (FD_free K4m false (v 12) (v 12)). split; [inlist|]. pose proof (meta_locs_in4 fm l Hl). unfold dhiF; cbn [dloF dszF flo4]. rewrite Efm. flia.
      * exists true, (v 160), (v 160). inlist.
    +
      refine (post_okF msF rhoF HagF _ _ _ (dsF_of 2) (dsC_of 2) Ho Hm HsmF Hds _ ((meta_locs g ++ meta_locs hp) ++ meta_locs fm) _ _ _ _ Hpc Hcs Hfr Hfc Hrs Ha0 Ha1).
      * intros d Hd. cbn [dsF_of] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [right; inlist | left | left | right; inlist | right; inlist].
        -- split; [reflexivity | exact I].
        -- split; [reflexivity|]. cbn [od_okF_at]. rewrite zeNv, zeN_160, Efm. unfold zF4 in EzF. rewrite E. cbn [optrA]. reflexivity.
      * rewrite s5_eq. exact (delta_fq_ring t4 g ND4 Mg4 fm hp nx pr2 nx2 E Mfm Mhp Nfm Nhp).
      * intros d Hd. cbn [dsC_of] in Hd. destruct Hd as [<-|[<-|[<-|[]]]]; (split; [inlist|]); (split; [|exact I]); cbn [od_okF_at fcond4 fptr4].
        -- split; [exact I|]. exists (Some hp), (Some fm). rewrite s5_eq, (MT_fq_g t4 g fm hp nx pr2 nx2 E Mfm Mhp Nfm Nhp). split; [reflexivity|]. split; [discriminate|].
           split; [intros p Hp; injection Hp as <-; exact Khp|]. split; [intros p Hp; injection Hp as <-; exact Kfm|]. rewrite !zeNv, zeN_161, zeN_160, Efm, EzFp. split; reflexivity.
        -- split; [rewrite E; discriminate|]. exists (Some g), (Some nx). rewrite Efm, s5_eq, (MT_fq_fm t4 g fm hp nx pr2 nx2 E Mfm Mhp Nfm Nhp).
           unfold fq_next'. rewrite (proj2 (sptr_eqb_neq fm hp) ltac:(intros EE; exact (Nhf (eq_sym EE)))). split; [reflexivity|]. split; [discriminate|].
           split; [intros p Hp; injection Hp as <-; exact Kg4|]. split; [intros p Hp; injection Hp as <-; exact Knx|]. rewrite !zeNv, zeN_12, zeN_162, EzFn. split; reflexivity.
        -- split; [rewrite E; discriminate|]. exists (Some pr2), (Some g). rewrite Eft, s5_eq, (MT_fq_hp t4 g fm hp nx pr2 nx2 E Mfm Mhp Nfm Nhp Nhf).
           split; [reflexivity|]. split; [discriminate|].
           split; [intros p Hp; injection Hp as <-; exact Kpr2|]. split; [intros p Hp; injection Hp as <-; exact Kg4|]. rewrite !zeNv, zeN_163, zeN_12, EzTp. split; reflexivity.
      * intros l Hl. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]|].
        -- exists (FD_free K4g true (v 161) (v 160)). split; [inlist|]. pose proof (meta_locs_in4 g l Hl). unfold dhiF; cbn [dloF dszF flo4]. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG. flia.
        -- exists (FD_free K4t false (v 163) (v 12)). split; [inlist|]. pose proof (meta_locs_in4 hp l Hl). unfold dhiF; cbn [dloF dszF flo4]. rewrite EzFp. flia.
        -- exists (FD_free K4m false (v 12) (v 162)). split; [inlist|]. pose proof (meta_locs_in4 fm l Hl). unfold dhiF; cbn [dloF dszF flo4]. rewrite Efm. flia.
      * exists true, (v 161), (v 160). inlist.
Qed.

Theorem phaseF_here : ltac2:(tb__ "0|0|
S175S55VK;S17fS131Vg;Vt4;A2A1S12eVL;Vg;Vam;Vrho;Vgd;VrhoL;VmsL;Vt4;Vrbase;Vrlen;AaS49S4aS12aA1S173Vtr;S174VmsL;Vmd;A2A4A5").
Proof using EmW Erd HK4 HMI HMI4 HP12 HP13 HXz4 HZ HZ4 Hcanary4 Hdepth Hgd Hgd_holds HrL10 HrL11 HrL110 HrL111 HrL15 HrL28 HrL29 HrL38 HrL39 HrLf HrLlow Hres Hres64 Hres_r Hsc48 HsmL Hsm_pre Hsp Hsp_high Hstk Hu. split; [exact instantiateF | exact HK4]. Qed.

End PhaseF.
End V.
End Mal_nt_V9.

Module Mal_nt_V10.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition J_nt_preT (t : nat) (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|a|
S62S4aS12aA1S12bSa2Q40M0S5cR3PcA2A2S8Sa2G0S5cR4PdA2A2S8S3ScScS3S15S15S3Sa0G0A1S44Sa0Q8A1A1F_;M1G1S1S0S8Se0S142VA;A1M2R3A2R5A3S1S196Se1VX;S47S4bScS8A2S49ScS8R3R4A4A2M3VU;S15cVX;VA;A2M4S1ffS55R1A2S206S55R1A2S12cR6A1A8S1S152G2VX;R1S5fR8A1A4S1Sf1VX;G3VU;S141VA;A1M5A4S1SefVX;G5R3R2A4S1S8S34Z0M6VU;R1A1A2Fc;S1S2S0S4bS44ScA1M7G7A2S49G7G7S18R2A1S13R2A1A4S49G7G7S4eScA1M8G8A4A3A1S2S0G7SeeG5SfR3A1A2S47ScR4A2A3A1S2S0S8S16R4A1G6A3A1F_;F_;S1S34S10aZ40Sa2G0S5cR8S203A2A2A2S3cS157S19fSfR2A1A1M9A1A1A2S1S1a0S141G4A1A1S1VKc;R7R6A2S1S205VA;R8A2S17bG9Vt;A2A2A2A2A2A2A2A2A2A2A2A2Lmv;A2Lam;A2Lg;A2Ti;Tga;Lmd;Ltr;Lrho;").
Lemma J_nt_preT_intro t X U A Kc rho tr md (g : sptr) (am : ameta) : ltac2:(tb__ "0|0|
S15aS55Se1VX;VU;VA;VKc;Vrho;Vtr;Vmd;A9ScS15S0S8Se0S142VA;A1R2A2Sa2Q40S5cVrho;PcA2A2A3SefVX;S141VA;A1R3R2A4S17bS19fSfR3A1A1Vt;A2F_;F_;Fam';Fg';S1faVt;VX;VU;VA;VKc;Vrho;Vtr;Vmd;A8F_;F_;").
Proof.
  intros (g0 & am0 & mv & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) HT.
  exists g0, am0, mv. repeat (split; [assumption|]). exact (HT g0 am0 H1 H5).
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S196Se1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;S13fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
SefVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§17§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§17§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation Hctx := (§17§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PcA2A2Se0VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation Hres := (@U.Mal_nt__G1.Mal_nt_I.Hres s L X U g am i vm rd0 wok0 HMI Hu).
Local Abbreviation R_all := (@U.Mal_nt__G1.Mal_nt_I.R_all s L X U g am i gd vm rd0 wok0 HMI Hu Hgd).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation Hctx_ok := (§17§ U.Mal_nt__G1.Mal_nt_I.Hctx_ok).
Local Notation "§18§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§18§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§18§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§18§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Notation "§19§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§19§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation rw1_low := (@U.Mal_nt__G1.Mal_nt_I.rw1_low s L g am i rho gd rd0 Hgd).
Local Abbreviation zr1 := (§19§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§19§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§19§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§19§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Notation "§20§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation ze142 := (§20§ U.Mal_nt__G1.Mal_nt_I.ze142).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S34Z1000Sa2Q40S5cVrho;PaA2A2M0A2S0S8S3aG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S34S10aZ40Sa2Q40S5cVrho;PfA2A2A2M0N60A2S34S3cS37Z2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;Vrd0;S106S55VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sa0Q40A1S45F_;Vwok0;S107S55VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1Z60A2A2S0S44Sa0Q8A1M0A1VmV;Sa1Q40S35Z108ecR2A2A2A1S4eG0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Se4Se2Vrd0;Sa0Q40A1S46L_;A2Se5Se1A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Se2S106S55VmV;A2S107S55VmV;A2A2").
Local Notation "§21§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation klo := (§21§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§21§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§21§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S152VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§19§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§19§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation g_zone := (§20§ U.Mal_nt__G2.Mal_nt_Z.g_zone).
Local Abbreviation k_zone := (§20§ U.Mal_nt__G2.Mal_nt_Z.k_zone).
Local Abbreviation f_zone := (§20§ U.Mal_nt__G2.Mal_nt_Z.f_zone).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S34Se3VL;A1S35S14dVrho;A1S14cVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S4aS12aA1S12bOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1e9S55VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
SddVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1eeS55VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
SddSddSddVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1f0S55VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSddSddR3VTR;R3R2A2F_;VTR;SdeS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1edS55VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
SddSddSddSddSdeR4R1A1M0R6R2A1F_;Fw;SdeG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1eaS55VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
SddSddSdeR3R1A1VTR;SdeS0SdeR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1ecS55VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
SddSddSddVTR;R3R1A2VTR;R3R2A2VTR;SdeS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1ebS55VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1cbVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sf1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrho;PdA2Sa1G0Vi;A2A3").
Local Abbreviation cx3 := (@U.Mal_nt__G3.Mal_nt_V4.cx3).
Local Abbreviation flds_upd := (@U.Mal_nt__G3.Mal_nt_V4.flds_upd).
Local Abbreviation flds_s1 := (§18§ U.Mal_nt__G3.Mal_nt_V4.flds_s1).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;VmW;S5fVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S12dVvm;S12cVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S4aS12aA1M0S12bVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S12bR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S66S55Vrho;S155S151A1S49S4aS12aA1S173Vtr;S174Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S8S34Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S4bS44ScA1M0G0A2S49G0G0S18Vam;A1S13Vam;A1A4S49G0G0S4eScA1M1G1A4A3A1S2S0G0SeeVs;SfVam;A1A2S47ScVg;A2A3A1S2S0S8S16Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S8S35S167Vam;A1S1bVi;A1A2S1cS12Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation l1_locs := (§18§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation usage_ge := (@U.Mal_nt__G3.Mal_nt_V4.usage_ge s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp HU Hsc48).
Hypothesis Hml0 : am_maplen am = 0.
Local Abbreviation amPar' := (§18§ U.Mal_nt__G3.Mal_nt_V7.amPar').
Local Abbreviation s3v := (§18§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Notation "§22§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HU HR2g Hall Hsc48 Hml0) (at level 10, h__ global).
Local Abbreviation N3_call := (§22§ U.Mal_nt__G3.Mal_nt_V7.N3_call).
Local Abbreviation HI3v := (§22§ U.Mal_nt__G3.Mal_nt_V7.HI3v).
Local Abbreviation HXz3v := (@U.Mal_nt__G3.Mal_nt_V7.HXz3v s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HU HR2g Hall Hsc48 Hml0).
Local Abbreviation HuP3v := (§22§ U.Mal_nt__G3.Mal_nt_V7.HuP3v).
Local Abbreviation reach3v := (@U.Mal_nt__G3.Mal_nt_V7.reach3v s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HU HR2g Hreach Hall Hsc48 Hml0).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).
Local Notation "§23§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd sr Hzs HIr HU HR2g Hall Hsc48 Hml0) (at level 10, h__ global).
Local Abbreviation s3r_inv := (§23§ U.Mal_nt__G3.Mal_nt_V7.s3r_inv).
Local Abbreviation s3v_real := (§23§ U.Mal_nt__G3.Mal_nt_V7.s3v_real).
Local Abbreviation tier3v := (@U.Mal_nt__G3.Mal_nt_V7.tier3v s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hreach Hml0).
Local Abbreviation deltaU3v := (§22§ U.Mal_nt__G3.Mal_nt_V7.deltaU3v).
Local Abbreviation ub3v := (§22§ U.Mal_nt__G3.Mal_nt_V7.ub3v).
Local Abbreviation amPar'_fields := (§18§ U.Mal_nt__G3.Mal_nt_V7.amPar'_fields).
Local Abbreviation HL3v := (§22§ U.Mal_nt__G3.Mal_nt_V7.HL3v).
Local Abbreviation o_stk_top := (@U.Mal_nt__G5.Mal_nt_V8.o_stk_top).
Local Abbreviation HromL := (@U.Mal_nt__G5.Mal_nt_V8.HromL tr md).
Local Abbreviation sp0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.sp0_range4 am rho gd Hgd Hsp Hsc48).
Local Abbreviation D0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.D0_range4 am rho gd Hgd Hdepth Hsc48).
Local Abbreviation phaseF := (@U.Mal_nt__G5.Mal_nt_V9.phaseF s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hall Hsc48 Hml0).
Local Abbreviation phaseF_here := (@U.Mal_nt__G5.Mal_nt_V9.phaseF_here s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 HP13 Hsp Hdepth mV Erd ms Hgd_holds mW HZ Hsp_high K tr md EmW Hsm_pre Hsc48).
Section CallStep.
Hypothesis HdepthT : ltac2:(tb__ "0|0|
S34S14cVrho;A1S3cS157S19fS15eVam;A1A1A1A1A2").

Lemma st_usage_3v : ltac2:(tb__ "0|1|
S0S4aS8A1S2eS143Vs;Vg;Vam;A3A1S33S15eVam;A1M0S38S24Vs;G0A2S35S12Vam;A1Z1A2A2S2eVs;A1A3A3").
Proof using .
  pose proof (flds_upd g (MFree None None) (upd_meta gPar (MUsed amPar') (fgm_s2 s g am))) as (C1 & _).
  pose proof (flds_upd gPar (MUsed amPar') (fgm_s2 s g am)) as (C2 & _).
  pose proof flds_s1 as (C3 & _). unfold cx3, U.Mal_nt__G3.Mal_nt_V4.cx3 in C1, C2, C3.
  change s3v with (upd_meta g (MFree None None) (upd_meta gPar (MUsed amPar') (fgm_s2 s g am))).
  pose proof (f_equal (fun t => fst (fst t)) C1) as E1. pose proof (f_equal (fun t => fst (fst t)) C2) as E2. pose proof (f_equal (fun t => fst (fst t)) C3) as E3.
  cbn [fst] in E1, E2, E3. rewrite E1, E2. unfold fgm_s2. cbn [st_usage set_usage]. rewrite E3. reflexivity.
Qed.
Lemma usage_of_3v c : ltac2:(tb__ "0|1|
S34Z0Vc;A2S0S8S24S143Vs;Vg;Vam;A3Vc;A2S45S8L_;S39Vc;S15eVam;A1M0A2S38S24Vs;G0A2S35S12Vam;A1Z1A2A2S24Vs;Vc;A2X45x2A3F_;").
Proof using HMI Hgd Hsc48 rho.
  intros Hc. unfold usage_of at 1. rewrite st_usage_3v. pose proof Hsc48 as SC. pose proof (proj1 (proj2 Hctx_ok)) as LU.
  rewrite znth_zset by (unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia). rewrite LU. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *.
  replace (am_sc am <? Z.of_nat 48%nat) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
Qed.
Lemma bounded3v : bounded s3v.
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hsp Hu.
  pose proof (mig_bounded HMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4. pose proof usage_ge as UG. pose proof Hsc48 as SC. pose proof R_all as R.
  pose proof deltaU3v as (_ & _ & _ & A4 & A5 & _ & _ & A8 & A10 & A11 & _).
  split; [|rewrite A8, A4, A10, A11, A5; auto].
  assert (POS : forall c, 0 <= c -> 0 <= usage_of s3v c < 2 ^ 48).
  { intros c Hc. rewrite (usage_of_3v c Hc). pose proof (B1 c) as Bc. pose proof (B1 sc) as Bs. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. destruct (c =? am_sc am); lia. }
  intros c. destruct (Z.le_gt_cases 0 c) as [Hc|Hc]; [exact (POS c Hc)|].
  replace (usage_of s3v c) with (usage_of s3v 0) by (unfold usage_of, znth; replace (Z.to_nat c) with (Z.to_nat 0) by lia; reflexivity).
  exact (POS 0 ltac:(lia)).
Qed.
Lemma tier_sc_pos : (1 <= NestTier.tier sc)%nat.
Proof using HMI Hgd Hml0 Hreach Hsc48 Hsp Hu. pose proof tier3v. lia. Qed.
Lemma Htier_c_pf : D0 + 96 <= - 96.
Proof using HMI HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. pose proof HdepthT as T. pose proof tier_sc_pos as P. unfold nt_stack, NT_D in T. lia. Qed.
Lemma HtierP_pf : ltac2:(tb__ "0|0|
S34S35S14cVrho;A1Z60A2S3cS157S19fSfS149Vs;Vg;Vam;A3A1A1A1A1A2").
Proof using HMI HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu.
  pose proof HdepthT as T. pose proof tier3v as P. pose proof amPar'_fields as (_ & _ & E & _). rewrite E.
  unfold nt_stack, NT_D in *. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. nia.
Qed.

Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agreesW rhoF.
Let scut : Z := 96.
Lemma Hscut : ltac2:(tb__ "0|1|
S1S34Z0M0Vscut;A2S34S35S14cVrho;A1Vscut;A2G0A2A2").
Proof using Hdepth Hgd Hsc48. pose proof D0_range4. unfold scut. lia. Qed.
Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC dsO dsB : list od).
Local Abbreviation dsX := (@U.Mal_nt__G3.Mal_nt_V7.dsX dsC dsO dsB).
Local Abbreviation oStkF := (@U.Mal_nt__G3.Mal_nt_V7.oStkF stkc).
Local Abbreviation NRELW := (@U.Mal_nt__G3.Mal_nt_V7.NRELW dsF).
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S4aS5bA1S6bVSF;A1S43S5bS14bVstkc;A1VobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S45S1a1VobjsF;S146VdsF;A1A2S46A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
S66S55VrhoF;VSF;S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S0S45S9bS5bS1bdS171A1S146VdsF;A1A3S46A3").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S0S45S9bSa3SaaVdsF;A3S46A3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
Sa3S9aSa3R1VdsF;A3Sb5Vam;R2A2F_;Fd;").
Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
Sa3S9aSa3R1VdsF;A3S4S198Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S9aSa3R2S147VdsC;VdsO;VdsB;A3A3A2F_;Fd;").
Let s' : astate := s3v.
Let locs : list loc := ltac2:(tb__ "0|1|
S50SeaS50SeaS50SeaS1f5Vs;Vg;Vam;A3S43SeaSf6S35Sf9S3eZ8S15eVam;A1A2A2A1S4fSeaA1M0A3A3G0A3S1cfVg;A1A3").
Lemma HI' : ltac2:(tb__ "0|0|
Sf1S43ScVg;VX;A3S47S4bScS8A2S49ScS8S161Vs;Vg;Vam;A3S163Vs;Vg;Vam;A3A4A2VU;Vs';A4").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact HI3v. Qed.
Lemma HXz' : ltac2:(tb__ "0|0|
S158S43ScVg;VX;A3Vs';A2").
Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hsc48 Hu rho. exact HXz3v. Qed.
Lemma Hdelta : ltac2:(tb__ "0|0|
S20fVs;Vs';Vlocs;A3").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact deltaU3v. Qed.
Lemma Hbounded' : bounded s'.
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hsp Hu. exact bounded3v. Qed.
Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Hypothesis HdsC : ltac2:(tb__ "0|0|
Sa3S9aSa3R1VdsC;A3S1S9aSa3R2VdsF;A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs';R2AaS144R2A1A2A2F_;Fd;").
Hypothesis HdsO : ltac2:(tb__ "0|1|
Sa3S9aSa3R1VdsO;A3S1S9aSa3R2VdsF;A3S1S0S44S9A1Sb6R2A1S4eS9A1A3S1S34S15dVL;Vg;A2M0Sa5Vs;VL;Vg;Vam;R2A5A2S34Sa4Vs;VL;Vg;Vam;R2A5S35G0Z28A2A2A2A2A2F_;Fd;").
Hypothesis HdsO_cover : ltac2:(tb__ "0|1|
S8S1S34S15dVL;Vg;A2M0R1A2S36R1S35G0Z28A2A2A2S3Sa3Sa3S1S9aSa3R1VdsO;A3S1S34Sa5Vs;VL;Vg;Vam;R1A5R3A2S36R3Sa4Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fx;").
Hypothesis HdsB : ltac2:(tb__ "0|2|
Sa3S9aSa3R1VdsB;A3S1S9aSa3R2VdsF;A3S1S0S44S9A1Sb6R2A1S4eS9A1A3S1S150Vs;VL;VX;Vg;Vam;R2A6S1Se9S9aSe9R1S50Se9Sf0Vs';A1S194Vs';A1A3A3S212VL;R2Sa5Vs;VL;Vg;Vam;R4A5M0S38Sa4Vs;VL;Vg;Vam;R4A5G0A2A4S7F_;F_;Fc;S1S4S34Sa4Vs;VL;Vg;Vam;R2A5Z10000A2S34Z5b000Sa5Vs;VL;Vg;Vam;R2A5M1A2A2S1S34Z1000G1A2S8S1S34Sa5Vs;VL;Vg;Vam;R3A5R1A2S36R1Sa4Vs;VL;Vg;Vam;R3A5A2A2Sf4VL;Vs;R2A3F_;Fx;A2A2A2A2A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|3|
SeaS9aSeaR1Vlocs;A3S4S3Sa3Sa3S1S9aSa3R1VdsC;A3S1S34Sa5Vs;VL;Vg;Vam;R1A5SecVL;R3A2M0A2S36G0Sa4Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2S1S34S15dVL;Vg;A2M1SecVL;R2A2M2A2S36G2S35G1Z28A2A2A2A2F_;Fl;").
Hypothesis HdsCB_g : ltac2:(tb__ "0|1|
Sa3S9aSa3R1S50Sa3VdsC;VdsB;A3A3S4S34Sa4Vs;VL;Vg;Vam;R2A5S15dVL;Vg;A2M0A2S34S35G0Z28A2Sa5Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;").
Local Abbreviation stk := (@U.Mal_nt__G3.Mal_nt_V7.stk rho scut).
Local Notation "§24§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ tr md msF rhoF HagF SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent) (at level 10, h__ global).
Local Abbreviation V1' := (§24§ U.Mal_nt__G3.Mal_nt_V7.V1').
Local Abbreviation owned_below_ceiling := (@U.Mal_nt__G3.Mal_nt_V7.owned_below_ceiling s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsp Hsc48 dsC dsO dsB s' locs Hdelta).
Local Abbreviation stk_high := (@U.Mal_nt__G3.Mal_nt_V7.stk_high s L g am rho gd Hgd Hsp Hsp_high Hsc48 scut Hscut dsC dsO dsB).
Local Abbreviation m'c := (@U.Mal_nt__G3.Mal_nt_V7.m'c rho msF rhoF scut dsF).
Local Abbreviation m'c_stk := (@U.Mal_nt__G3.Mal_nt_V7.m'c_stk s L g am i rho gd Hgd Hsp Hdepth Hsc48 msF rhoF scut Hscut dsF dsC dsO dsB).
Local Abbreviation m'c_nstk := (@U.Mal_nt__G3.Mal_nt_V7.m'c_nstk s L g am i rho gd Hgd Hsp Hdepth Hsc48 msF rhoF scut Hscut dsF dsC dsO dsB).
Local Abbreviation keptC := (@U.Mal_nt__G4.Mal_nt_V7b.keptC s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok Hm_sct mW HZ tr md EmW Hsc48 msF rhoF HagF scut Hscut SF dsF dsC dsO dsB HsmF HdsF_DS HdsF_cond HdsF_ent s' HdsC HdsO HdsB).
Hypothesis HSF_pc : ss_pc SF = 0x2084c.
Hypothesis HSF_fregs : ltac2:(tb__ "0|0|
S0S4aS5aA1S6eVSF;A1S56A3").
Hypothesis HSF_fcsr : ltac2:(tb__ "0|0|
S0S70S6dVSF;A1S76A3").
Hypothesis HSF_resv : ss_resv SF = None.
Hypothesis HSF_sp : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S65VrhoF;S5eVSF;Z2A2A2Sa1G0S38S14dVrho;A1Vscut;A2A2A3").
Lemma Hscut16 : scut mod 16 = 0.
Proof using . reflexivity. Qed.
Lemma Htier_c : ltac2:(tb__ "0|0|
S34S35S14cVrho;A1Vscut;A2N60A2").
Proof using HMI HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. exact Htier_c_pf. Qed.
Local Abbreviation reg_of_var := (@U.Mal_nt__G4.Mal_nt_V7c.reg_of_var).
Local Notation "§25§ h__" := (h__ rho rhoF scut SF) (at level 10, h__ global).
Local Abbreviation rwC := (§25§ U.Mal_nt__G4.Mal_nt_V7c.rwC).
Local Abbreviation rhoC := (@U.Mal_nt__G4.Mal_nt_V7c.rhoC rho msF rhoF scut SF dsF).
Local Abbreviation rwC_15 := (@U.Mal_nt__G4.Mal_nt_V7c.rwC_15 s L g am rho gd Hgd Hsp Hdepth Hsc48 rhoF scut Hscut SF dsC dsO dsB).
Local Abbreviation rwC_reg := (§25§ U.Mal_nt__G4.Mal_nt_V7c.rwC_reg).
Local Abbreviation rwC_other := (§25§ U.Mal_nt__G4.Mal_nt_V7c.rwC_other).
Local Abbreviation HOF_stkC := (@U.Mal_nt__G4.Mal_nt_V7c.HOF_stkC tr md msF rhoF SF stkc objsF HSF_objs HsmF).
Local Abbreviation stkF_range := (@U.Mal_nt__G4.Mal_nt_V7c.stkF_range s L g am i rho gd rd0 Hgd mW Hsc48 rhoF HagF scut dsC dsO dsB).
Local Abbreviation smatch_call := (@U.Mal_nt__G4.Mal_nt_V7c.smatch_call s L g am i rho gd rd0 Hgd Hsp Hdepth mW Hsp_high tr md Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HSF_pc HSF_fregs HSF_fcsr HSF_resv HSF_sp Hscut16 Htier_c).
Let aP : ameta := amPar'.
Lemma HuP' : ltac2:(tb__ "0|0|
SefS43ScVg;VX;A3Vs';S161Vs;Vg;Vam;A3VaP;A4").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact HuP3v. Qed.
Hypothesis Ha0 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S65VrhoF;S5eVSF;ZaA2A2A2Se0VL;S161Vs;Vg;Vam;A3A2A3").
Hypothesis Ha1 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S65VrhoF;S5eVSF;ZbA2A2A2S163Vs;Vg;Vam;A3A3").
Lemma HR2P : ltac2:(tb__ "0|2|
S2S0S4bS44ScA1M0G0A2S49G0G0S18VaP;A1S13VaP;A1A4S49G0G0S4eScA1M1G1A4A3A1S2S0G0SeeVs';SfVaP;A1A2S47ScS161Vs;Vg;Vam;A3A2A3A1S2S0S8S16VaP;A1Z0A3A1F_;F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact (proj2 (proj2 (proj2 (proj2 N3_call)))). Qed.
Lemma Hreach' : reach_ok s'.
Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hreach Hsc48 Hu rho. exact reach3v. Qed.
Lemma HtierP : ltac2:(tb__ "0|0|
S34S35S14cVrho;A1Vscut;A2S3cS157S19fSfVaP;A1A1A1A1A2").
Proof using HMI HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. exact HtierP_pf. Qed.
Let sr' : astate := s3r.
Lemma Hzs' : ltac2:(tb__ "0|0|
S0S10Vs';S1f4S43ScVg;VX;A3Vsr';A2A3").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. exact s3v_real. Qed.
Lemma HIr' : ltac2:(tb__ "0|0|
Sf1S43ScVg;VX;A3S47S4bScS8A2S49ScS8S161Vs;Vg;Vam;A3S163Vs;Vg;Vam;A3A4A2VU;Vsr';A4").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. exact (proj1 s3r_inv). Qed.
Lemma HuPr : ltac2:(tb__ "0|0|
SefS43ScVg;VX;A3Vsr';S161Vs;Vg;Vam;A3VaP;A4").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. exact (proj2 s3r_inv). Qed.
Local Abbreviation call_J := (@U.Mal_nt__G4.Mal_nt_V7c.call_J s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high sr HIr tr md Evm HU HR2g Hsc48 msF rhoF HagF scut Hscut SF stkc objsF dsF dsC dsO dsB HSF_objs HSF_match HsmF HdsF_DS HdsF_cond HdsF_ent s' locs HI' HXz' Hdelta Hbounded' HdsC HdsO HdsO_cover HdsB Hlocs HdsCB_g aP Ha0 Ha1 HR2P Hreach' HtierP sr' Hzs' HIr' HuPr).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).

Lemma canary_untouchedC x : ltac2:(tb__ "0|3|
S4S1S34Z28d50M0Vx;A2S36Vx;S35G0Z8M1A2A2A2S1S34Z5a338M2Vx;A2S36Vx;S35G2G1A2A2A2A2S2S1a3Sa3Sa5Vs;VL;Vg;Vam;A4Sa4Vs;VL;Vg;Vam;A4S147VdsC;VdsO;VdsB;A3Vx;A5A1F_;").
Proof using HMI HdsB HdsC HdsO Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hx (d & HdX & R). pose proof Hctx as HCX. pose proof g_zone as GZ. unfold U.Mal_nt__G1.Mal_nt_D.dhi in R.
  unfold dsX in HdX. apply in_app_iff in HdX as [HdC|HdX]; [|apply in_app_iff in HdX as [HdO|HdB]].
  - destruct (HdsC d HdC) as (Hd & Hok' & Hrom').
    destruct d as [| | |kk pv nv av fv|hv|sx|ua ub uc ud|fx|fk five pv nv|ux|bx|gx| |c0| | | | |cs]; try (destruct Hrom'; fail); cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz] in R; cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok'.
    + destruct Hok' as (Hkc & _). pose proof (k_zone kk Hkc) as ZK. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am kk) with (klo kk) in R. lia.
    + pose proof R_all. unfold CTX_SIZE, sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + lia.
    + lia.
    + lia.
    + destruct Hok' as (Hfc & _). pose proof (f_zone fk Hfc) as ZK. lia.
    + destruct Hok' as [Hsc' _]. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + destruct Hok' as [Hr _]. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
    + lia.
  - destruct (HdsO d HdO) as (_ & _ & R1 & R2). unfold U.Mal_nt__G1.Mal_nt_D.dhi in R2. lia.
  - destruct (HdsB d HdB) as (_ & _ & _ & _ & IMG & LO & _). unfold U.Mal_nt__G1.Mal_nt_D.dhi in IMG. lia.
Qed.
Lemma stk_not_low x : ltac2:(tb__ "0|0|
S36Vx;Z5b000A2S2S148Vrho;Vscut;Vx;A3A1F_;").
Proof using Hdepth Hgd Hsc48 Hsp Hsp_high. intros Hx S. unfold stk, U.Mal_nt__G3.Mal_nt_V7.stk in S. pose proof Hsp_high. pose proof D0_range4. pose proof (ceiling_small L). top_ranges. lia. Qed.
Theorem canaryC : ltac2:(tb__ "0|0|
S1e8S55Se1S5fVrho;A1S14aVrho;VmsF;VrhoF;Vscut;VdsF;A5A4").
Proof using EmW Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hgd_holds Hm_sct Hrom Hsc48 HsmF Hsp Hsp_high Hu.
  intros a Ha. cbn [mc_chk_guard_got mc_chk_guard C_U] in Ha.
  assert (Ra : 0 <= a < 2 ^ 64) by lia.
  destruct (V1' a Ra (canary_untouchedC a Ha)) as [_ E]. unfold byteview_of in E.
  replace ((0 <=? a) && (a <? 2 ^ 64) && true)%bool with true in E
    by (symmetry; rewrite andb_true_r; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  change (Glue.rd_of segsU m'c (Z_to_bv 64 a) = Glue.rd_of segsU (rm rho) (Z_to_bv 64 a)). rewrite <- EmW.
  set (M' := WalkReab.m' od obj_of msF rhoF dsF) in *.
  assert (EM : m'c (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) by (apply m'c_nstk; rewrite u64_of_sum by lia; apply stk_not_low; lia).
  replace (Glue.rd_of segsU m'c (Z_to_bv 64 a)) with (Glue.rd_of segsU M' (Z_to_bv 64 a)) by (unfold Glue.rd_of; rewrite EM; reflexivity).
  destruct (Glue.rd_of segsU M' (Z_to_bv 64 a)) as [b1|]; destruct (Glue.rd_of segsU mW (Z_to_bv 64 a)) as [b0|]; try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

Lemma obj_holds_shrink_lo rhoX msX b lo lo' hi cs : ltac2:(tb__ "0|2|
S64S55VrhoX;VmsX;S77Vb;Vlo;Vhi;Vcs;S71A5M0A4S34S90VrhoX;G0A2S7eVrhoX;Vlo';A2M1A2S34G1S8fVrhoX;G0A2A2S177S68S68S34G1S7eVrhoX;S7fR1A1A2A2Lc;Vcs;A3S64S55VrhoX;VmsX;S77Vb;Vlo';Vhi;Vcs;S71A5A4F_;F_;F_;F_;").
Proof using Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros (Hb & Hw & Hc & Hd & _) L1 L2 Hfit. unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [lia|]. split; [intros off Hoff Hwr; apply Hw; [lia | exact Hwr]|].
  split.
  { apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3). pose proof (proj1 (Forall_forall _ _) Hfit c Hin) as F.
    split; [exact F|]. split; [exact C2 | exact C3]. }
  split; [|exact I].
  intros off Hoff NC. apply Hd; [lia|]. exact NC.
Qed.

Hypothesis Estkc : ltac2:(tb__ "0|0|
S0S4aS68A1Vstkc;S73S17eA1A3").
Lemma stk_cells_fit : ltac2:(tb__ "0|3|
S0S45S9bS68S68S5aS45Lx;S7fR1A1S8S4cS3fN60R1A2S40R1Z0A2A2Lz;S9S4dLi0;S1c9S5aS5aS4dLb;La;M0Lop;M1G1S1caG0Lop;M2G2S45SbS5aS4dLa;Lw;Lsgn;S9S5aS8S4dLk;Li0;Ll;X5ax8Lc;S73S17eA1A3S46A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma stk_top_vars : ltac2:(tb__ "0|0|
S0S45S1bdS171S134A2S46A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma HromF' : rom_ok segsU msF. Proof using HsmF. exact (proj1 (proj2 (proj2 (proj2 (proj2 HsmF))))). Qed.

Lemma stk_top_holds (mL : word -> option byte) (msL : machine_state) : ltac2:(tb__ "0|1|
S98S55VmsL;A2Sa0Q40M0A1S148Vrho;Vscut;Sa2G0R1A2A3S0S44Sa0Q8A1A1VmL;R2A1S1e6VmsF;R2A2A3F_;Fa;S64S55VrhoW;S17cVmsL;VmL;A2S134A4F_;F_;").
Proof using Estkc HSF_objs HagF Hdepth Hgd Hsc48 HsmF Hsp dsB dsC dsO. try clear Hsp_high.
  intros HromL EQ. pose proof stkF_range as (E10 & E15 & E0). pose proof D0_range4 as DR. pose proof sp0_range4 as SPR.
  pose proof HOF_stkC as H1. unfold oStkF in H1. rewrite Estkc in H1.

  assert (H2 : obj_holds segsU rhoF msF (mkObj (SVar 10) (SLit (-96)) (SLit 0) (ob_cells o_stk_saved) DUnknown)).
  { apply (obj_holds_shrink_lo rhoF msF (SVar 10) (SVar 15)); [exact H1 | | |].
    - unfold obj_lo_of. cbn [ob_lo]. rewrite E15, soff_lit_small by lia. lia.
    - unfold obj_hi_of. cbn [ob_hi]. rewrite E0, soff_lit_small by lia. lia.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) stk_cells_fit c Hc) as F. cbn beta in F.
      destruct (c_off c) as [z| | | | | | |]; try discriminate F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. rewrite !soff_lit_small by lia. exact F1. }

  assert (H3 : obj_holds segsU rhoF (with_mem msL mL) (mkObj (SVar 10) (SLit (-96)) (SLit 0) (ob_cells o_stk_saved) DUnknown)).
  { apply (obj_holds_mem_ext segsU rhoF msF); [| | exact H2].
    - intros a. cbn [ms_rom with_mem]. rewrite HromL, HromF'. reflexivity.
    - intros off Hoff. unfold obj_lo_of, obj_hi_of in Hoff. cbn [ob_base ob_lo ob_hi] in Hoff. rewrite !soff_lit_small in Hoff by lia.
      cbn [ms_mem with_mem ob_base]. rewrite E10. apply EQ. rewrite u64_of_sum by lia. unfold stk, U.Mal_nt__G3.Mal_nt_V7.stk, scut. lia. }

  change o_stk_top with (mkObj (SVar 10) (SLit (-96)) (SLit 0) (ob_cells o_stk_saved) DUnknown).
  apply (obj_holds_agreeing segsU below200 rhoF rhoW); [| | exact stk_top_vars | exact H3].
  - intros vv Hvv. symmetry. exact (proj1 HagF vv Hvv).
  - intros l. symmetry. exact (proj1 (proj2 HagF) l).
Qed.

Hypothesis IH : ltac2:(tb__ "0|2|
S62VTR;S176S55S1faS19fS15eVam;A1A1S43ScVg;VX;A3M0VU;S13fS145Vs;Vg;Vam;Vsr;A4VL;A2M1VK;A5S155S151A1R1A4S1bcS55S57R1S153S55Se1S151G0VU;G1VK;A7A4A2FrhoX;").
Hypothesis HKw : K tr md.

Hypothesis HSF_ra : ltac2:(tb__ "0|0|
S0S5aS5eVSF;Z1A2S5dZ20ad4A1A3").
Hypothesis HSF_x8 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;Z8A2SdfP8eA1A3").
Hypothesis HSF_x9 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;Z9A2S5dZ5a338A1A3").
Hypothesis HSF_x18 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;Z12A2S5dZ5a3d0A1A3").
Hypothesis HSF_x19 : ltac2:(tb__ "0|0|
S0S5aS5eVSF;Z13A2SdfPcA1A3").
Hypothesis HSF_low : ltac2:(tb__ "0|0|
S9S9aS9R1S43S9P17S43S9P18S43S9P28S43S9P29S43S9P2aS43S9P2bS43S9P2cS43S9P2dS43S9P2eS43S9P2fS4fS9A1A3A3A3A3A3A3A3A3A3A3A3S0S5aS5eVSF;S38SaR2A1Z14A2A2S61R2A1A3F_;Fj;").

Lemma owned3v a : ltac2:(tb__ "0|0|
S5S140Se1S13fS143Vs;Vg;Vam;A3VL;A2Va;A3S140Se1S13fVs;VL;A2Va;A3A2").
Proof using HMI HR2g HU Hall Hdepth Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high.
  pose proof deltaU3v as (Dfp & _). pose proof (ub_same_user_blocks s s3v (proj1 (inv_keys HI)) (proj1 (inv_keys HI3v)) ub3v) as Dub.
  unfold ma_owned, owned, alloc_owned, in_footprint, in_user_block. cbn [ma_s ma_L]. rewrite Dfp, Dub. tauto.
Qed.
Lemma EVF e : ltac2:(tb__ "0|1|
S0S45S109Ve;A1S46A3S0S45S1beS171Ve;A2S46A3S0Sa0Q40M0A1S65VrhoF;Ve;A2Sa1G0S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Ve;A3A2A3F_;F_;").
Proof using HagF. drop_sp. intros Hs Hv. exact (EV rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoF e HagF Hv Hs). Qed.

Lemma owned_t4_below (t4 : astate) (mv4 : word -> option byte) x : ltac2:(tb__ "0|0|
S196Se1S43ScVg;VX;A3S4eS4bScS8A2A1VU;S13fVt4;VL;A2S106S55Vmv4;A2S107S55Vmv4;A2Vvm;A8Sf4VL;Vt4;Vx;A3S36Vx;Se3VL;A1A2F_;F_;").
Proof using Hgd Hsc48 Hsp. try clear Hsp_high. try clear Hdepth.
  intros HMI4 [(rg & Hin & Hx) _]. assert (HCX : ly_ctx L = 0x5a3d0) by exact (mig_ctx HMI4).
  destruct rg as [[o|p] n]; cbn [fst snd] in *.
  - unfold footprint in Hin. destruct Hin as [E|Hin].
    + injection E as <- <-. cbn [loc_addr] in Hx. rewrite HCX in Hx. top_ranges. unfold CTX_SIZE in Hx. lia.
    + exfalso. apply in_app_iff in Hin as [Hin|Hin].
      * apply in_map_iff in Hin as (a & E & _). discriminate E.
      * apply in_flat_map in Hin as (k & _ & Hin). destruct (region_of t4 k) as [rg|]; [|destruct Hin].
        destruct (rg_kind rg); try destruct Hin. destruct (rg_live rg); [|destruct Hin]. destruct Hin as [E|[]]. discriminate E.
  - change (loc_addr L (LMem p)) with (addr_of L p) in Hx. pose proof (proj1 (proj2 (footprint_mem_range C_U L t4 vm p n (mig_vm HMI4) (mig_ledger HMI4) Hin ltac:(lia)))). lia.
Qed.

Lemma reg_of_var_none j : ltac2:(tb__ "0|0|
S34Z34SaVj;A1A2S0S44S8A1S214Vj;A1S4eS8A1A3F_;").
Proof using Hgd Hsc48 rho. drop_sp.
  intros Hj. unfold reg_of_var, U.Mal_nt__G4.Mal_nt_V7c.reg_of_var.
  repeat match goal with |- context [if ?c then _ else _] => let e := fresh in destruct c eqn:e; [exfalso; first [apply Z.eqb_eq in e | apply Bool.orb_true_iff in e as [e|e]; apply andb_prop in e as [e e']; apply Z.leb_le in e; apply Z.leb_le in e']; lia|] end.
  reflexivity.
Qed.

Theorem call_safe : ltac2:(tb__ "0|0|
VTR;SdeS0SdeR1S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4A3Lw;S1bcS55S57Vrho;S153S55Se1S151VX;VU;S13fVsr;VL;A2VKc;A7A4A2").
Proof using EmW Erd Estkc Evm Ewok HIr HKc HKw HMI HP12 HP13 HP13w HR2g HSF_fcsr HSF_fregs HSF_low HSF_match HSF_objs HSF_pc HSF_ra HSF_resv HSF_sp HSF_x18 HSF_x19 HSF_x8 HSF_x9 HU HXz HZ Ha0 Ha1 HagF Hall Hdepth HdepthT HdsB HdsC HdsCB_g HdsF_DS HdsF_cond HdsF_ent HdsO HdsO_cover Hgd Hgd_holds Hlocs Hm_sct Hml0 Hreach Hrom Hsc48 HsmF Hsm_pre Hsp Hsp_high Hu Hzs IH TR_conseq TR_pointwise TR_seq aP sr'.
  eapply TR_seq.
  { eapply TR_conseq; [| intros w Hw; exact Hw | exact (IH rhoC)]. intros w ->. split; [exact smatch_call |].
    apply (J_nt_preT_intro _ _ _ _ _ _ _ _ gPar amPar' (call_J K HKw)). intros g' am' Eg' Hu'.
    change (addr_of L g' = bv_unsigned (rw rhoC 12%positive)) in Eg'. change (usedX (g :: X) s3r g' am') in Hu'.
    apply (proj2 (usedX_zomb (g :: X) s3r g' am')) in Hu'. rewrite <- s3v_real in Hu'.
    assert (E12 : rw rhoC 12%positive = eval rhoF (reg_sv SF 10)) by (cbn [rw U.Mal_nt__G4.Mal_nt_V7c.rhoC]; apply rwC_reg; reflexivity).
    rewrite E12, Ha0 in Eg'.
    pose proof (proj1 (usedX_MT _ _ _ _ Hu')) as M1. pose proof (proj1 (usedX_MT _ _ _ _ HuP3v)) as M2.
    pose proof (addr_of_injective (g :: X) (Some (gPar, iPar)) U s3v L HI3v HL3v g' gPar (MT_Some_In_keys _ _ _ M1) (MT_Some_In_keys _ _ _ M2) Eg') as Eg.
    subst g'. rewrite M2 in M1. injection M1 as <-. pose proof amPar'_fields as (_ & _ & E & _). rewrite E. exact tier3v. }
  apply TR_pointwise. intros [tr4 [ms4 md4]] (Lx & JLx & rhoL & HinP & Hav & HsmL & HJL).
  destruct HinP as [E|[]]. injection E as <- <-. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HsmL, HJL.
  unfold JL_nt, zv in HJL. cbn [ma_s ma_L] in HJL.
  destruct HJL as ([t4r L4] & mv4 & r4 & HMI4 & HZ4 & EL & Hinit4 & HI4r & Hxk4 & Cr4r & UB4r & Hreach4 & Hres_r & Heq4g & Hkept & Hcan & HK4). cbn [ma_s ma_L] in *. subst L4.
  destruct (HKc _ _ HK4) as (_ & -> & ->). rewrite <- Evm in HMI4.

  set (t4 := zomb (g :: X) t4r) in *.
  rewrite <- s3v_real in Hkept.
  assert (HXz4 : xzomb (g :: X) t4) by (exact (xzomb_real (g :: X) None U t4r HI4r)).
  assert (Cr4 : corr (g :: X) s3v t4) by (rewrite s3v_real; apply (proj1 (corr_zomb (g :: X) s3r t4r)); exact Cr4r).
  assert (UB4 : ub_same s3v t4) by (rewrite s3v_real; apply ub_same_zomb; exact UB4r).
  assert (Hres : (bv_unsigned (rw rhoL V_RES1) = 0 /\ bv_unsigned (rw rhoL V_RES) = 0)
            \/ (0 < bv_unsigned (rw rhoL V_RES1) /\ exists k rg, region_of t4 k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true
                  /\ rg_len rg = page_round (bv_unsigned (rw rhoL V_RES1)) /\ ly_reg L k = bv_unsigned (rw rhoL V_RES)
                  /\ (forall q a, usedX (g :: X) t4 q a -> 0 < am_maplen a -> prid (am_mem a) <> k))).
  { destruct Hres_r as [(_ & H1 & H2)|(k & rg & _ & Hlen & R1 & R2 & R3 & R4 & R5 & Hno)]; [left; split; assumption|].
    right. split; [exact Hlen|]. exists k, rg. subst t4. rewrite region_of_zomb. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    intros q a Hq. apply (Hno q a). apply (proj1 (usedX_zomb (g :: X) t4r q a)). exact Hq. }
  assert (Heq4 : forall F, (fneed (am_sc amPar) <= F)%nat -> nontrivial_free F gPar iPar s3r = IRet (r4, t4r)).
  { intros F HF.
    assert (E12 : rw rhoC 12%positive = eval rhoF (reg_sv SF 10)) by (cbn [rw U.Mal_nt__G4.Mal_nt_V7c.rhoC]; apply rwC_reg; reflexivity).
    assert (E13 : rw rhoC 13%positive = eval rhoF (reg_sv SF 11)) by (cbn [rw U.Mal_nt__G4.Mal_nt_V7c.rhoC]; apply rwC_reg; reflexivity).
    pose proof (Heq4g gPar amPar' F) as E. rewrite E12, E13, Ha0, Ha1 in E. pose proof amPar'_fields as (_ & _ & Esc & _). rewrite Esc in E.
    exact (E eq_refl (proj2 s3r_inv) HF). }

  assert (AV : forall j, (j < 100)%positive -> rw rhoL j = rw rhoC j) by (intros j Hj; symmetry; exact (proj1 Hav j Hj)).
  pose proof sp0_range4 as SPR. pose proof D0_range4 as DR. pose proof R_all as RA. pose proof (ceiling_small L) as CS. pose proof g_zone as GZ.
  assert (HrL10 : rw rhoL 10%positive = Z_to_bv 64 (sp0 - 96)).
  { rewrite (AV 10%positive) by lia. cbn [rw rhoC]. unfold rwC, U.Mal_nt__G4.Mal_nt_V7c.rwC. rewrite Pos.eqb_refl. reflexivity. }
  assert (HrL15 : bv_unsigned (rw rhoL 15%positive) = (D0 + 96) mod 2 ^ 64).
  { rewrite (AV 15%positive) by lia. exact (proj1 rwC_15). }
  assert (REGv : forall j r, (j < 100)%positive -> reg_of_var j = Some r -> rw rhoL j = eval rhoF (reg_sv SF r)).
  { intros j r Hj Hr. rewrite (AV j Hj). cbn [rw rhoC]. exact (rwC_reg j r Hr). }
  assert (HrL11 : rw rhoL 11%positive = Z_to_bv 64 0x20ad4) by (rewrite (REGv 11%positive 1 ltac:(lia) eq_refl), HSF_ra; reflexivity).
  assert (HrL28 : rw rhoL 28%positive = Z_to_bv 64 zM) by (rewrite (REGv 28%positive 8 ltac:(lia) eq_refl), HSF_x8, (EVF (v 142) eq_refl eq_refl), ze142; reflexivity).
  assert (HrL29 : rw rhoL 29%positive = Z_to_bv 64 0x5a338) by (rewrite (REGv 29%positive 9 ltac:(lia) eq_refl), HSF_x9; reflexivity).
  assert (HrL38 : rw rhoL 38%positive = Z_to_bv 64 0x5a3d0) by (rewrite (REGv 38%positive 18 ltac:(lia) eq_refl), HSF_x18; reflexivity).
  assert (HrL39 : rw rhoL 39%positive = Z_to_bv 64 zG) by (rewrite (REGv 39%positive 19 ltac:(lia) eq_refl), HSF_x19, (EVF (v 12) eq_refl eq_refl), ze12; reflexivity).
  assert (HrLlow : forall j, In j [23; 24; 40; 41; 42; 43; 44; 45; 46; 47]%positive -> rw rhoL j = rw rho j).
  { intros j Hj.
    assert (Hj100 : (j < 100)%positive /\ reg_of_var j = Some (Z.pos j - 20) /\ j <> 13%positive).
    { cbn [In] in Hj. destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; (split; [reflexivity | split; [reflexivity | discriminate]]). }
    destruct Hj100 as (Hj100 & Hr & N13).
    rewrite (REGv j _ Hj100 Hr), (HSF_low j Hj). cbn [eval]. rewrite (proj1 HagF j) by (unfold below200; apply Pos.ltb_lt; lia).
    cbn [rw rhoW rho1]. apply rw1_low; [exact Hj100 | exact N13]. }
  assert (HrLf : forall j, (60 <= j < 92)%positive -> rw rhoL j = rw rho j).
  { intros j Hj. rewrite (AV j) by lia. cbn [rw rhoC]. apply rwC_other; [apply Pos.eqb_neq; lia | apply Pos.eqb_neq; lia | apply reg_of_var_none; lia]. }
  assert (Hres64 : 0 <= bv_unsigned (rw rhoL V_RES) < 2 ^ 64 /\ 0 <= bv_unsigned (rw rhoL V_RES1) < 2 ^ 64) by (split; apply urange).
  assert (HrL110 : rw rhoL 110%positive = Z_to_bv 64 (bv_unsigned (rw rhoL V_RES))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (HrL111 : rw rhoL 111%positive = Z_to_bv 64 (bv_unsigned (rw rhoL V_RES1))) by (symmetry; apply Z_to_bv_bv_unsigned).

  assert (STK : forall a, stk (bv_unsigned a) -> rm rhoL a = ms_mem msF a).
  { intros a S. pose proof (stk_high (bv_unsigned a) S) as SH. pose proof (urange a) as Ua.
    rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite (Hkept (bv_unsigned a) Ua).
    - cbn [rm rhoC]. rewrite (m'c_stk (Z_to_bv 64 (bv_unsigned a))); [reflexivity|]. rewrite u64_of_sum by lia. exact S.
    - intros OW. unfold ma_owned, owned in OW. cbn [ma_s ma_L] in OW.
      destruct OW as [OW|OW]; [pose proof (owned_below_ceiling _ OW); lia|]. cbn [mc_lock C_U] in OW. top_ranges. lia.
    - intros OW. unfold ma_owned, owned in OW. cbn [ma_s ma_L] in OW.
      destruct OW as [OW|OW]; [pose proof (owned_t4_below t4 mv4 _ HMI4 OW); lia|]. cbn [mc_lock C_U] in OW. top_ranges. lia.
    - unfold errno_range, mc_errno. cbn [mc_tp C_U]. top_ranges. lia.
    - unfold alloc_static. cbn [mc_libc mc_chk_guard_got mc_chk_guard mc_replaced C_U]. top_ranges. lia. }
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 HsmL))))) as HromL. cbn [fst snd cfg_ms] in HromL.
  pose proof (stk_top_holds (rm rhoL) ms4 HromL STK) as Hstk.
  assert (Hkept4 : forall a, 0 <= a < 2 ^ 64 -> ~ ma_owned C_U (mkMA s L) a -> ~ ma_owned C_U (mkMA t4 L) a ->
            ~ errno_range C_U a -> ~ alloc_static C_U a -> ~ (sp0 - 96 <= a < sp0) -> rm rhoL (Z_to_bv 64 a) = rm rho (Z_to_bv 64 a)).
  { intros a Ha NO NO4 NE NS NSK. rewrite (Hkept a Ha ltac:(intros OW; exact (NO (proj1 (owned3v a) OW))) NO4 NE NS).
    cbn [rm rhoC]. apply (keptC a Ha NO); [intros OW; exact (NO (proj1 (owned3v a) OW)) | exact NE | exact NS | unfold stk, U.Mal_nt__G3.Mal_nt_V7.stk, scut; exact NSK]. }
  assert (Hcanary4 : canary_kept segsU C_U (rm rho) (rm rhoL)).
  { intros a Ha. rewrite (Hcan a Ha). exact (canaryC a Ha). }
  eapply TR_conseq; [| intros w Hw; exact Hw
    | exact (phaseF rhoL ms4 t4 mv4 (bv_unsigned (rw rhoL V_RES)) (bv_unsigned (rw rhoL V_RES1)) HsmL HMI4 HZ4 HXz4 Cr4 UB4 Hreach4 Hres Hres64 Hstk Hkept4 Hcanary4 HK4
               t4r r4 eq_refl HI4r Hres_r Heq4 Hxk4)].
  intros w ->.
  exact (phaseF_here rhoL ms4 t4 mv4 (bv_unsigned (rw rhoL V_RES)) (bv_unsigned (rw rhoL V_RES1)) HsmL HMI4 HZ4 HXz4 Hres Hres64 HrL10 HrL15 HrL11 HrL28 HrL29 HrL38 HrL39 HrLlow HrLf HrL110 HrL111 Hstk Hcanary4 HK4 t4r r4 Hres_r).
Qed.

End CallStep.
End V.
End Mal_nt_V10.

Module Mal_nt_V11.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7b OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G4.Mal_nt_V7c OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V8 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V9 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G5.Mal_nt_V10.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Fixpoint cells_eqb (a b : list cell) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => cell_eqb x y && cells_eqb a' b' | _, _ => false end.
Lemma cells_eqb_sound a b : ltac2:(tb__ "0|0|
S0S45S20aVa;Vb;A2S46A3S0S4aS68A1Va;Vb;A3F_;").
Proof.
  revert b. induction a as [|x a' IH]; intros [|y b'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply cell_eqb_sound in H1. rewrite H1, (IH b' H2). reflexivity.
Qed.
Definition obj_eqb (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S4cS4cS4cS4cS63S7cVo;A1S7cVo';A1A2S63S81Vo;A1S81Vo';A1A2A2S63S80Vo;A1S80Vo';A1A2A2S20aS73Vo;A1S73Vo';A1A2A2S1fcS7dVo;A1S7dVo';A1A2A2").
Lemma obj_eqb_sound o o' : ltac2:(tb__ "0|0|
S0S45S20bVo;Vo';A2S46A3S0S5bVo;Vo';A3F_;").
Proof.
  unfold obj_eqb. intros H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. apply cells_eqb_sound in H4. apply odefault_eqb_sound in H5.
  destruct o, o'; cbn in *; subst; reflexivity.
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S196Se1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;S13fVs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
SefVX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§26§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§26§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§26§ U.Mal_nt__G1.Mal_nt_I.HL).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PcA2A2Se0VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S8Sa2Q40S5cVrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation bits := (@U.Mal_nt__G1.Mal_nt_I.bits am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Notation "§27§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§27§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation bits_range := (§27§ U.Mal_nt__G1.Mal_nt_I.bits_range).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Notation "§28§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation apQ := (§28§ U.Mal_nt__G1.Mal_nt_I.apQ).
Local Notation "§29§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNn := (§29§ U.Mal_nt__G1.Mal_nt_I.zNn).
Local Abbreviation zPp := (§29§ U.Mal_nt__G1.Mal_nt_I.zPp).
Local Abbreviation zU := (@U.Mal_nt__G1.Mal_nt_I.zU s am).
Local Abbreviation gPar := (§28§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§28§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§28§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation zQ := (§29§ U.Mal_nt__G1.Mal_nt_I.zQ).
Local Notation "§30§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§30§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Notation "§31§ h__" := (h__ s L g am i rho gd rd0 Hgd) (at level 10, h__ global).
Local Abbreviation rw1_low := (§31§ U.Mal_nt__G1.Mal_nt_I.rw1_low).
Local Abbreviation zr1 := (§30§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§30§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§30§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§30§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation zl1_1 := (§31§ U.Mal_nt__G1.Mal_nt_I.zl1_1).
Local Abbreviation zr1_10 := (§30§ U.Mal_nt__G1.Mal_nt_I.zr1_10).
Local Notation "§32§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation zr1_142 := (§32§ U.Mal_nt__G1.Mal_nt_I.zr1_142).
Local Abbreviation RN := (§27§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation RP := (§27§ U.Mal_nt__G1.Mal_nt_I.RP).
Local Abbreviation RQ := (§27§ U.Mal_nt__G1.Mal_nt_I.RQ).
Local Abbreviation zQ_range := (§27§ U.Mal_nt__G1.Mal_nt_I.zQ_range).
Local Abbreviation par_last := (§27§ U.Mal_nt__G1.Mal_nt_I.par_last).
Local Abbreviation zHb_eq := (§27§ U.Mal_nt__G1.Mal_nt_I.zHb_eq).
Local Abbreviation zOff_eq := (§27§ U.Mal_nt__G1.Mal_nt_I.zOff_eq).
Local Abbreviation par_bits_clear := (§27§ U.Mal_nt__G1.Mal_nt_I.par_bits_clear).
Local Abbreviation par_off_chk := (§27§ U.Mal_nt__G1.Mal_nt_I.par_off_chk).
Local Abbreviation par_map_chk := (§27§ U.Mal_nt__G1.Mal_nt_I.par_map_chk).
Local Abbreviation hdr_cells := (@U.Mal_nt__G1.Mal_nt_I.hdr_cells s L X U g am i gd vm rd0 wok0 HMI HXz Hu Hgd).
Local Abbreviation zU_range := (@U.Mal_nt__G1.Mal_nt_I.zU_range s L X U g am i vm rd0 wok0 HMI).
Local Abbreviation RH := (§27§ U.Mal_nt__G1.Mal_nt_I.RH).
Local Abbreviation zHb_range := (§27§ U.Mal_nt__G1.Mal_nt_I.zHb_range).
Local Abbreviation ze_lit := (§30§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§30§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation ze_aluw := (§30§ U.Mal_nt__G1.Mal_nt_I.ze_aluw).
Local Abbreviation ze_ext := (§30§ U.Mal_nt__G1.Mal_nt_I.ze_ext).
Local Abbreviation ze135 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze135).
Local Abbreviation ze141 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Abbreviation ze151 := (@U.Mal_nt__G1.Mal_nt_I.ze151 s L X U g am i rho gd vm rd0 wok0 HMI Hgd).
Local Abbreviation ze153 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze153).
Local Abbreviation ze155 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze155).
Local Abbreviation ze112 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze112).
Local Abbreviation ze113 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze113).
Local Abbreviation ze170 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze170).
Local Abbreviation ze171 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze171).
Local Abbreviation ze172 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze172).
Local Abbreviation ze173 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze173).
Local Abbreviation ze174 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze174).
Local Abbreviation ze169 := (§32§ U.Mal_nt__G1.Mal_nt_I.ze169).
Local Abbreviation bits_mod32 := (§27§ U.Mal_nt__G1.Mal_nt_I.bits_mod32).
Local Abbreviation ze_maplen := (§32§ U.Mal_nt__G1.Mal_nt_I.ze_maplen).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S34Z1000Sa2Q40S5cVrho;PaA2A2M0A2S0S8S3aG0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S34S10aZ40Sa2Q40S5cVrho;PfA2A2A2M0N60A2S34S3cS37Z2Z28A2A1G0A2A2").
Local Abbreviation ZF_base := (@U.Mal_nt__G1.Mal_nt_I.ZF_base s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth).
Local Abbreviation ZF_freeable := (§32§ U.Mal_nt__G1.Mal_nt_I.ZF_freeable).
Local Notation "§33§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ZF_sc48 := (§33§ U.Mal_nt__G1.Mal_nt_I.ZF_sc48).
Local Abbreviation ZF_all := (§32§ U.Mal_nt__G1.Mal_nt_I.ZF_all).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;Vrd0;S106S55VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sa0Q40A1S45F_;Vwok0;S107S55VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S8S1S34Z0R1A2S36R1Z60A2A2S0S44Sa0Q8A1M0A1VmV;Sa1Q40S35Z108ecR2A2A2A1S4eG0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
Se4Se2Vrd0;Sa0Q40A1S46L_;A2Se5Se1A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
Se2S106S55VmV;A2S107S55VmV;A2A2").
Local Abbreviation AGq := (@U.Mal_nt__G1.Mal_nt_Ic.AGq L rho gd Hgd).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§28§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§28§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§29§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§29§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§29§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation od_svs := (@U.Mal_nt__G1.Mal_nt_D.od_svs).
Local Abbreviation sv_sem := (@U.Mal_nt__G1.Mal_nt_D.sv_sem).
Local Abbreviation dsxb := (@U.Mal_nt__G1.Mal_nt_D.dsxb).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S152VL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation od_ok_at := (§30§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§30§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§28§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§29§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§29§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation par_zone := (§33§ U.Mal_nt__G2.Mal_nt_Z.par_zone).
Local Abbreviation od_disjoint := (@U.Mal_nt__G2.Mal_nt_Z.od_disjoint s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp).
Local Abbreviation od_pairwise := (§29§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation zfree_of := (§33§ U.Mal_nt__G2.Mal_nt_Z.zfree_of).
Local Abbreviation od_ok_shdr_entry := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_ok_shdr_entry).
Local Abbreviation od_ok_bptr_entry' := (@U.Mal_nt__G2.Mal_nt_Z.od_ok_bptr_entry' s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Abbreviation od_ok_pbase_entry := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_ok_pbase_entry).
Local Abbreviation od_ok_parmeta_entry := (§32§ U.Mal_nt__G2.Mal_nt_Z.od_ok_parmeta_entry).
Local Abbreviation od_ok_parea_entry := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_ok_parea_entry).
Local Abbreviation od_ok_secret_entry := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_ok_secret_entry).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S34Se3VL;A1S35S14dVrho;A1S14cVrho;A1A2A2").
Local Abbreviation od_ok_sct := (§30§ U.Mal_nt__G2.Mal_nt_Z.od_ok_sct).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S4aS12aA1S12bOF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1e9S55VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
SddVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1eeS55VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
SddSddSddVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1f0S55VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OSddSddR3VTR;R3R2A2F_;VTR;SdeS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1edS55VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
SddSddSddSddSdeR4R1A1M0R6R2A1F_;Fw;SdeG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1eaS55VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
SddSddSdeR3R1A1VTR;SdeS0SdeR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1ecS55VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
SddSddSddVTR;R3R1A2VTR;R3R2A2VTR;SdeS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1ebS55VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1cbVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sf1VX;S47S4bScS8A2S49ScS8Vg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sa0Q40M0A1S5cVrho;PdA2Sa1G0Vi;A2A3").
Local Abbreviation segRm := (@U.Mal_nt__G2.Mal_nt_V3.segRm s L g am i rho gd rd0 TR K TRR).
Local Abbreviation ZF_holdsm := (§30§ U.Mal_nt__G2.Mal_nt_V3.ZF_holdsm).
Local Notation "§34§ h__" := (h__ s L g am i rho gd rd0 mW) (at level 10, h__ global).
Local Abbreviation agreesV_of := (§34§ U.Mal_nt__G2.Mal_nt_V3.agreesV_of).
Local Abbreviation agrees_of_V := (§34§ U.Mal_nt__G2.Mal_nt_V3.agrees_of_V).
Local Notation "§35§ h__" := (h__ s L g am i rho gd rd0 ms mW) (at level 10, h__ global).
Local Abbreviation riding := (§35§ U.Mal_nt__G2.Mal_nt_V3.riding).
Local Abbreviation riding_nil := (§35§ U.Mal_nt__G2.Mal_nt_V3.riding_nil).
Local Abbreviation od_hold_m := (@U.Mal_nt__G2.Mal_nt_V3.od_hold_m s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ).
Local Abbreviation objs_matchb_refl := (@U.Mal_nt__G2.Mal_nt_V3.objs_matchb_refl).
Local Abbreviation objs_matchb_app := (@U.Mal_nt__G2.Mal_nt_V3.objs_matchb_app).
Local Abbreviation smatch_canon := (@U.Mal_nt__G2.Mal_nt_V3.smatch_canon).
Local Abbreviation scratch_pairb := (@U.Mal_nt__G2.Mal_nt_V3.scratch_pairb).
Local Abbreviation diffs_ok_scratch := (@U.Mal_nt__G2.Mal_nt_V3.diffs_ok_scratch).
Local Notation "§36§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp ms Hrom mW Hsp_high) (at level 10, h__ global).
Local Abbreviation carve_on := (§36§ U.Mal_nt__G2.Mal_nt_V3.carve_on).
Local Abbreviation release_seg := (@U.Mal_nt__G2.Mal_nt_V3.release_seg s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp ms Hrom mW).
Local Abbreviation svl_eqb := (@U.Mal_nt__G2.Mal_nt_V3.svl_eqb).
Local Abbreviation svl_eqb_sound := (@U.Mal_nt__G2.Mal_nt_V3.svl_eqb_sound).
Local Abbreviation carve_back := (§36§ U.Mal_nt__G2.Mal_nt_V3.carve_back).
Local Abbreviation gl_pv := (@U.Mal_nt__G2.Mal_nt_V3.gl_pv).
Local Abbreviation gl_nv := (@U.Mal_nt__G2.Mal_nt_V3.gl_nv).
Local Abbreviation pvnv_okb := (@U.Mal_nt__G2.Mal_nt_V3.pvnv_okb).
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0Sa0Q40A1S44Sa0Q8A1A1F_;VmW;S5fVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S12dVvm;S12cVmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S4aS12aA1M0S12bVK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S12bR2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
S66S55Vrho;S155S151A1S49S4aS12aA1S173Vtr;S174Vms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S8S34Z0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S4bS44ScA1M0G0A2S49G0G0S18Vam;A1S13Vam;A1A4S49G0G0S4eScA1M1G1A4A3A1S2S0G0SeeVs;SfVam;A1A2S47ScVg;A2A3A1S2S0S8S16Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S8S35S167Vam;A1S1bVi;A1A2S1cS12Vam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation Hsc48' := (@U.Mal_nt__G3.Mal_nt_V4.Hsc48' am Hsc48).
Local Abbreviation LenA3 := (§26§ U.Mal_nt__G3.Mal_nt_V4.LenA3).
Local Abbreviation l1_locs := (§28§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation usage_ge := (@U.Mal_nt__G3.Mal_nt_V4.usage_ge s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp HU Hsc48).
Local Abbreviation E_usage := (@U.Mal_nt__G3.Mal_nt_V4.E_usage).
Local Abbreviation E_avN := (@U.Mal_nt__G3.Mal_nt_V4.E_avN).
Local Abbreviation E_frN := (@U.Mal_nt__G3.Mal_nt_V4.E_frN).
Local Notation "§37§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp mV Erd Ewok Hsc48) (at level 10, h__ global).
Local Abbreviation ze_avN := (§37§ U.Mal_nt__G3.Mal_nt_V4.ze_avN).
Local Abbreviation ze_frN := (§37§ U.Mal_nt__G3.Mal_nt_V4.ze_frN).
Local Abbreviation RG := (§32§ U.Mal_nt__G3.Mal_nt_V4.RG).
Local Abbreviation HnN := (@U.Mal_nt__G3.Mal_nt_V4.HnN g am).
Local Abbreviation HpN := (§32§ U.Mal_nt__G3.Mal_nt_V4.HpN).
Local Abbreviation nQ_ng := (§32§ U.Mal_nt__G3.Mal_nt_V4.nQ_ng).
Local Abbreviation pQ_ng := (§32§ U.Mal_nt__G3.Mal_nt_V4.pQ_ng).
Local Abbreviation zNx_n := (§32§ U.Mal_nt__G3.Mal_nt_V4.zNx_n).
Local Abbreviation an2 := (§28§ U.Mal_nt__G3.Mal_nt_V4.an2).
Local Abbreviation MT_dq_nQ := (§32§ U.Mal_nt__G3.Mal_nt_V4.MT_dq_nQ).
Local Abbreviation an2_fields := (§32§ U.Mal_nt__G3.Mal_nt_V4.an2_fields).
Local Abbreviation s1_act := (§32§ U.Mal_nt__G3.Mal_nt_V4.s1_act).
Hypothesis Hml0 : am_maplen am = 0.
Local Notation "§38§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hml0) (at level 10, h__ global).
Local Abbreviation HuP := (§38§ U.Mal_nt__G3.Mal_nt_V7.HuP).
Local Abbreviation HscP := (§38§ U.Mal_nt__G3.Mal_nt_V7.HscP).
Local Abbreviation HgPg := (§38§ U.Mal_nt__G3.Mal_nt_V7.HgPg).
Local Abbreviation amPar' := (§28§ U.Mal_nt__G3.Mal_nt_V7.amPar').
Local Abbreviation s3v := (§28§ U.Mal_nt__G3.Mal_nt_V7.s3v).
Local Abbreviation N3_call := (@U.Mal_nt__G3.Mal_nt_V7.N3_call s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HU HR2g Hall Hsc48 Hml0).
Local Abbreviation s3r := (@U.Mal_nt__G3.Mal_nt_V7.s3r s g am sr).
Local Abbreviation tier3v := (@U.Mal_nt__G3.Mal_nt_V7.tier3v s L X U g am i gd vm rd0 wok0 HMI Hu Hgd Hreach Hml0).
Local Abbreviation bptr_free := (@U.Mal_nt__G3.Mal_nt_V7.bptr_free s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HU HR2g Hall Hsc48 Hml0).
Local Abbreviation sp0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.sp0_range4 am rho gd Hgd Hsp Hsc48).
Local Abbreviation D0_range4 := (@U.Mal_nt__G5.Mal_nt_V8.D0_range4 am rho gd Hgd Hdepth Hsc48).

Local Abbreviation dsX := (@U.Mal_nt__G3.Mal_nt_V7.dsX).
Local Abbreviation oStkF := (@U.Mal_nt__G3.Mal_nt_V7.oStkF).
Local Abbreviation od_chgC := (@U.Mal_nt__G3.Mal_nt_V7.od_chgC).
Local Abbreviation usage_of_3v := (@U.Mal_nt__G5.Mal_nt_V10.usage_of_3v s L X U g am i rho gd vm rd0 wok0 HMI Hgd Hsc48).
Local Abbreviation EVF := (§34§ U.Mal_nt__G5.Mal_nt_V10.EVF).
Local Abbreviation call_safe := (@U.Mal_nt__G5.Mal_nt_V10.call_safe s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high TR K TRR sr Hzs HIr HP13w tr md Kc EmW Evm HKc Hsm_pre HU HR2g Hreach Hall Hsc48 Hml0).

Ltac drop_sp := try clear Hsp_high; try clear Hdepth; try clear Hsp.

Hypothesis HdepthT : ltac2:(tb__ "0|0|
S34S14cVrho;A1S3cS157S19fS15eVam;A1A1A1A1A2").
Ltac inlist := cbn [In]; repeat (try (left; reflexivity); right).
Ltac zfact := cbn [zholds zcond].

Lemma MT_3v_keep q : ltac2:(tb__ "0|0|
S2S0ScVq;Vg;A3A1S2S0ScVq;S161Vs;Vg;Vam;A3A3A1S0S44SdA1SebS143Vs;Vg;Vam;A3Vq;A2SebS207Vs;Vg;Vam;A3Vq;A2A3F_;F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. drop_sp. intros H1 H2. rewrite (proj1 (proj2 (proj2 (proj2 N3_call))) q H1 H2). reflexivity. Qed.
Lemma active_3v_all c : ltac2:(tb__ "0|0|
S0S44ScA1SeeS143Vs;Vg;Vam;A3Vc;A2SeeS207Vs;Vg;Vam;A3Vc;A2A3").
Proof using . drop_sp.
  change s3v with (upd_meta g (MFree None None) (upd_meta gPar (MUsed amPar') (fgm_s2 s g am))).
  rewrite !active_hd_upd_meta. unfold fgm_s2. unfold active_hd. cbn [st_active set_usage]. reflexivity.
Qed.

Lemma gPar_not_used_sc q a : ltac2:(tb__ "0|0|
SefVX;Vs;Vq;Va;A4S0S8SfVa;A1S15eVam;A1A3S2S0ScS161Vs;Vg;Vam;A3Vq;A3A1F_;F_;").
Proof using HMI Hgd Hml0 Hsc48 Hu rho. drop_sp.
  intros Hq Hc E. subst q. pose proof (proj1 (usedX_MT _ _ _ _ Hq)) as M1. pose proof (proj1 (usedX_MT _ _ _ _ HuP)) as M2.
  rewrite M1 in M2. injection M2 as ->. pose proof HscP as C2. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. lia.
Qed.

Lemma ze_usageN : ltac2:(tb__ "0|0|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S1f6A3S38S16fVs;Vam;A2S35S12Vam;A1Z1A2A2A3").
Proof using HMI HU Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  unfold E_usage, U.Mal_nt__G3.Mal_nt_V4.E_usage. rewrite !ze_alu, ze151, ze135, !ze_lit. cbn [zalu].
  pose proof bits_range as B. pose proof zU_range as ZU. pose proof usage_ge as UG. pose proof R_all as R. pose proof bits_mod32 as (BM & _).
  change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1). change (18446744073709551584 mod 2 ^ 64) with (2 ^ 64 - 32).
  rewrite (Z.mod_small bits) by lia. rewrite (Z.mod_small (2 ^ 64 - 1)) by lia.
  pose proof (Z.mod_pos_bound bits 32 ltac:(lia)).
  rewrite (Z.mod_small (Z.lxor bits (2 ^ 64 - 1))) by (rewrite lxor_2p64m1 by lia; lia). rewrite (Z.mod_small (2 ^ 64 - 32)) by lia.
  rewrite neg_last_word by lia. rewrite BM.
  unfold zU, U.Mal_nt__G1.Mal_nt_I.zU, sc, U.Mal_nt__G1.Mal_nt_I.sc in *.
  replace (usage_of s (am_sc am) + (2 ^ 64 - 1 - am_last am)) with ((usage_of s (am_sc am) - (am_last am + 1)) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma okC3_usage : ltac2:(tb__ "0|1|
S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3Sb8S1f6A1M0AaS144G0A1A2").
Proof using HMI HU Hgd Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|]. rewrite ze_usageN, (usage_of_3v sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)). rewrite Z.eqb_refl. reflexivity. Qed.

Section Ring3.
Hypothesis HnS : ltac2:(tb__ "0|0|
S3ScScS1S0S44ScA1S13Vam;A1S47ScR1A2A3S2S0ScR1Vg;A3A1A2Ln;A2").
Lemma gPar_not_nQ : gPar <> nQ.
Proof using HMI Hgd Hml0 HnS Hsc48 Hu rho. drop_sp. destruct (RG HnS) as (p & n & ap & an & _ & _ & _ & _ & _ & Hun & Cn & _ & _ & _ & EnQ & _ & EanQ & _). rewrite EnQ. apply (gPar_not_used_sc n an Hun Cn). Qed.
Lemma gPar_not_pQ : gPar <> pQ.
Proof using HMI Hgd Hml0 HnS Hsc48 Hu rho. drop_sp. destruct (RG HnS) as (p & n & ap & an & _ & _ & _ & _ & Hup & _ & _ & Cp & _ & _ & _ & EpQ & _). rewrite EpQ. apply (gPar_not_used_sc p ap Hup Cp). Qed.
Lemma MT_3v_nQ_skip : ltac2:(tb__ "0|0|
S2S0S44ScA1SeeVs;S15eVam;A1A2S47ScVg;A2A3A1S0S44SdA1SebS143Vs;Vg;Vam;A3S164Vg;Vam;A2A2S47SdS26S1f7Vs;Vg;Vam;A3A1A2A3F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 HnS Hsc48 Hu rho. drop_sp.
  intros Hnh. rewrite (MT_3v_keep nQ (nQ_ng HnS) ltac:(intros E; exact (gPar_not_nQ (eq_sym E)))).
  pose proof (MT_dq_nQ HnS) as M. unfold fgm_s1. destruct (RG HnS) as (p & n & ap & an & En & _). rewrite (act_post_skip s g am n En Hnh). exact M.
Qed.
Lemma act_3v_skip : ltac2:(tb__ "0|3|
S2S0S44ScA1M0SeeVs;S15eVam;A1M1A2M2S47ScVg;A2A3A1S0G0SeeS143Vs;Vg;Vam;A3G1A2G2A3F_;").
Proof using HMI HR2g Hgd HnS Hsc48 Hu rho. drop_sp.
  intros Hnh. rewrite active_3v_all. destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & _).
  unfold fgm_s1. rewrite (act_post_skip s g am n En Hnh).
  rewrite (hd_dq_gen s g am Hsc48' LenA3 p n ap an Ep En Hng Mp Mn sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)).
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. destruct (active_hd s (am_sc am)) as [h|]; cbn [osptr_eqb andb]; [|reflexivity].
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hnh eq_refl)). reflexivity.
Qed.
Lemma okC3_N_skip (pv nv : sv) : ltac2:(tb__ "0|5|
S2S0S44ScA1SeeVs;S15eVam;A1A2S47ScVg;A2A3A1S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vpv;A3Se0VL;S168Vg;Vam;A2M2A2A3S0S8S108G0G1Vnv;A3S45S8L_;S29S164Vg;Vam;A2M3G2A2Se0VL;G3A2S16bVs;VL;Vg;Vam;A4X45x2A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3Sa7SadVpv;Vnv;SdfP99A1SdfP9bA1A5M4AaS144G4A1A2F_;F_;F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 HnS Hsc48 Hu. drop_sp.
  intros Hnh Epv Env. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact (HnN HnS)|].
  exists an2. split; [exact (MT_3v_nQ_skip Hnh)|]. destruct (an2_fields HnS) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  rewrite E1, E2, E6, E7, E3, E4, Epv, Env, ze153, ze155. pose proof RN as R'. unfold zNn, U.Mal_nt__G1.Mal_nt_I.zNn.
  repeat split; try reflexivity; try (apply Z.mod_small; lia). destruct (sptr_eqb nQ pQ); reflexivity.
Qed.
Lemma MT_3v_pQ : ltac2:(tb__ "0|3|
S2S0ScS168Vg;Vam;A2M0S164Vg;Vam;A2M1A3A1S0S44SdA1SebS143Vs;Vg;Vam;A3G0A2S47SdS26S31S18S16cVs;Vg;Vam;A3M2A1S47ScG1A2G2A3A1A2A3F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 HnS Hsc48 Hu rho. drop_sp.
  intros Hpn. destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & _ & _ & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
  rewrite (MT_3v_keep pQ (pQ_ng HnS) ltac:(intros E; exact (gPar_not_pQ (eq_sym E)))).
  rewrite EnQ, EpQ, EapQ in *. unfold fgm_s1, act_post. rewrite En.
  assert (MP : MT (dq_post s g am) p = Some (MUsed (am_set_links (am_prev ap) (Some n) ap))) by (apply (MT_dq_p s g am p n ap an Ep En Hng Hpg Mp Mn); exact Hpn).
  destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s (am_sc am)) (Some g))%bool; [|exact MP].
  destruct (MT (dq_post s g am) n) as [[| |an']|]; rewrite ?(MT_upd_other n _ _ p Hpn); exact MP.
Qed.
Lemma okC3_P (pv : sv) : ltac2:(tb__ "0|1|
S2S0ScS168Vg;Vam;A2S164Vg;Vam;A2A3A1S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vpv;A3S16eVs;VL;Vg;Vam;A4A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3Sa7Sb7Vpv;SdfP8dA1SdfP70A1SdfP71A1A5M0AaS144G0A1A2F_;F_;").
Proof using HMI HR2g HU Hall Hgd Hml0 HnS Hsc48 Hu. drop_sp.
  intros Hpn Epv. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact (HpN HnS)|].
  exists (am_set_links (am_prev apQ) (Some nQ) apQ). split; [exact (MT_3v_pQ Hpn)|]. cbn [am_mem am_prev am_next am_avail am_freed meta_bits am_set_links].
  rewrite Epv, ze141, ze112, ze113, (zNx_n HnS). pose proof RP as R'. unfold zPp, U.Mal_nt__G1.Mal_nt_I.zPp. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.

Section Head3.
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S44ScA1SeeVs;S15eVam;A1A2S47ScVg;A2A3").
Lemma MT_3v_nQ_act : ltac2:(tb__ "0|0|
S0S44SdA1SebS143Vs;Vg;Vam;A3S164Vg;Vam;A2A2S47SdS26S211S1f7Vs;Vg;Vam;A3A1A1A2A3").
Proof using HMI HR2g HU Hall Hgd Hhd Hml0 HnS Hsc48 Hu rho. drop_sp.
  rewrite (MT_3v_keep nQ (nQ_ng HnS) ltac:(intros E; exact (gPar_not_nQ (eq_sym E)))).
  rewrite (s1_act HnS Hhd). apply MT_upd_same.
Qed.
Lemma act_3v_head : ltac2:(tb__ "0|0|
S0S44ScA1SeeS143Vs;Vg;Vam;A3S15eVam;A1A2S47ScS164Vg;Vam;A2A2A3").
Proof using HMI Hgd Hhd HnS Hsc48 Hu rho. drop_sp.
  rewrite active_3v_all, (s1_act HnS Hhd), active_hd_upd_meta. destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & EnQ & _).
  rewrite (hd_dq_gen s g am Hsc48' LenA3 p n ap an Ep En Hng Mp Mn sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)).
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl, Z.eqb_refl. cbn [andb]. rewrite EnQ. reflexivity.
Qed.
Lemma okC3_act_head : ltac2:(tb__ "0|1|
S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3SaeSdfP8dA1A1M0AaS144G0A1A2").
Proof using HMI Hgd Hhd HnS Hsc48 Hu. drop_sp. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|]. rewrite ze141, act_3v_head. cbn [optrA]. exact (zNx_n HnS). Qed.
Lemma okC3_N_act (pv nv : sv) : ltac2:(tb__ "0|5|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vpv;A3Se0VL;S168Vg;Vam;A2M2A2A3S0S8S108G0G1Vnv;A3S45S8L_;S29S164Vg;Vam;A2M3G2A2Se0VL;G3A2S16bVs;VL;Vg;Vam;A4X45x2A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3Sa7SadVpv;Vnv;S1f8S1f9A5M4AaS144G4A1A2F_;F_;").
Proof using Erd Ewok HMI HR2g HU HXz Hall Hgd Hhd Hml0 HnS Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Epv Env. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact (HnN HnS)|].
  exists (am_activate an2). split; [exact MT_3v_nQ_act|]. destruct (an2_fields HnS) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold am_activate, act_of, am_set_avail, am_set_freed. cbn [am_mem am_prev am_next am_avail am_freed am_aidx am_last am_sc am_maplen meta_bits].
  rewrite E1, E6, E7, Epv, Env, ze_avN, ze_frN, E4, E5. unfold zNn, U.Mal_nt__G1.Mal_nt_I.zNn.
  split; [reflexivity|]. split; [rewrite <- E2; reflexivity|].
  split; [reflexivity|]. split; [destruct (sptr_eqb nQ pQ); reflexivity|]. split; reflexivity.
Qed.
End Head3.
End Ring3.

Lemma act_3v_none : ltac2:(tb__ "0|1|
S0S44ScA1M0S13Vam;A1S47ScVg;A2A3S0G0SeeS143Vs;Vg;Vam;A3S15eVam;A1A2S4eScA1A3F_;").
Proof using HMI Hsc48. drop_sp.
  intros Hng. rewrite active_3v_all, (fgm_s1_D1 s g am Hng). unfold dq_post. rewrite Hng, sptr_eqb_refl, active_hd_upd_meta.
  apply active_hd_set_hd_same; [exact Hsc48' | exact LenA3].
Qed.
Lemma okC3_act_none : ltac2:(tb__ "0|1|
S0S44ScA1S13Vam;A1S47ScVg;A2A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3SaeS5dZ0A1A1M0AaS144G0A1A2F_;").
Proof using HMI Hsc48. drop_sp. intros Hng. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|]. rewrite ze_lit, (act_3v_none Hng). reflexivity. Qed.

Lemma ZF_maplen0 : ltac2:(tb__ "0|0|
S10bS160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S67S1c2S18bS5dZ0A1A3A3").
Proof using HMI Hgd Hml0 Hu. drop_sp. zfact. rewrite ze_maplen, ze_lit, Hml0. reflexivity. Qed.
Lemma D0_192 : D0 <= - 192.
Proof using HMI HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. pose proof HdepthT as T. pose proof tier3v as P. unfold nt_stack, NT_D in T. lia. Qed.
Lemma ZF_depth192 : ltac2:(tb__ "0|0|
S10bS160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S67S1c3S5dNc0A1S61PfA1A3A3").
Proof using HMI Hdepth HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  zfact. cbn [zeval]. pose proof D0_192 as D. pose proof D0_range4 as DR. unfold D0, U.Mal_nt__G2.Mal_nt_Z.D0 in D, DR.
  replace (zr1 15%positive) with (bv_unsigned (rw rho 15%positive)) by (unfold zr1, U.Mal_nt__G1.Mal_nt_I.zr1, zr_of; cbn [rw rho1 U.Mal_nt__G1.Mal_nt_I.rho1]; rewrite (rw1_low 15) by lia; reflexivity).
  rewrite (Z.mod_small (bv_unsigned (rw rho 15%positive))) by apply urange.
  replace (toS 64 ((-192) mod 2 ^ 64)) with (-192) by reflexivity. apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma ZF_preN (extra : list sprop) : ltac2:(tb__ "0|2|
S177S60S10bS160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2M0Vextra;A3S177S60G0S50S60S50S60S43S60S190S43S60S18eS4fS60A1M1A3A3S50S60S191S43S60S67S1c2S18bS5dZ0A1A3S43S60S67S1c3S5dNc0A1S61PfA1A3G1A3A3A3A3S50S60Vextra;S18fA3A3A3F_;").
Proof using HMI HP12 Hall Hdepth HdepthT Hgd Hml0 Hreach Hsc48 Hsp Hu. try clear Hsp_high.
  intros HE. apply Forall_app. split; [|apply Forall_app; split; [exact HE | apply ZF_base]].
  constructor; [apply ZF_freeable|]. constructor; [apply (ZF_all Hall)|]. apply Forall_app. split; [apply (ZF_sc48 Hsc48)|].
  constructor; [apply ZF_maplen0|]. constructor; [apply ZF_depth192 | constructor].
Qed.

Definition bP : Z := meta_bits amPar.
Lemma amPar_ranges : ltac2:(tb__ "0|8|
S1S1S34Z0M0S30S162Vs;Vg;Vam;A3M1A1M2A2S36G2S37Z2Z20A2M3A2A2S1S1S34G0S16G1A1M4A2S36G4G3A2A2S1S1S34G0S12G1A1M5A2S34G5Z1fA2A2S1S34G0S17G1A1A2S1S1S34G0SfG1A1M6A2S36G6Z30A2A2S1S34G0S163Vs;Vg;Vam;A3M7A2S34G7G5A2A2A2A2A2A2A2").
Proof using HMI Hgd Hml0 Hsc48 Hu rho. drop_sp.
  pose proof (used_ranges X (Some (g, i)) U s HI gPar amPar HuP) as (A & B & C & _ & E). pose proof (par_last Hml0) as (P1 & P2 & P3 & _). repeat split; lia.
Qed.
Lemma bP_range : 0 <= bP < 2 ^ 48. Proof using HMI Hgd Hml0 Hsc48 Hu rho. unfold bP. pose proof (RQ Hml0). lia. Qed.
Lemma maplenP_range : ltac2:(tb__ "0|1|
S1S34Z0S17S162Vs;Vg;Vam;A3A1M0A2S36G0S37Z2Z24A2A2A2").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth. pose proof amPar_ranges as (_ & _ & _ & M & _). pose proof bP_range as B. unfold bP, meta_bits in B. pose proof amPar_ranges. lia. Qed.
Lemma bP_fields : ltac2:(tb__ "0|2|
S1S0S8S3aS1ddZ20A2S12S162Vs;Vg;Vam;A3M0A1A3S1S0S8S41S1ddZ1000A2S17G0A1A3S0S8S41S3aS3eS1ddS37Z2M1Z34A2A2S37G1Z40A2A2S37G1Z3aA2A2SfG0A1A3A2A2").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  unfold bP, meta_bits. pose proof amPar_ranges as (_ & _ & L3 & M & C & _). pose proof maplenP_range as MR.
  set (l := am_last amPar) in *. set (c := am_sc amPar) in *. set (m := am_maplen amPar) in *.
  repeat split.
  - replace (l + 32 + 64 * c + 4096 * m) with (l + (1 + 2 * c + 128 * m) * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 4096) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
  - replace (2 ^ 64) with (2 ^ 12 * 2 ^ 52) by reflexivity. rewrite Z.mul_mod_distr_r by lia.
    replace ((l + 32 + 64 * c + 4096 * m) mod 2 ^ 12) with (l + 32 + 64 * c).
    2:{ replace (l + 32 + 64 * c + 4096 * m) with ((l + 32 + 64 * c) + m * 2 ^ 12) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    replace (2 ^ 58) with (2 ^ 52 * 2 ^ 6) by reflexivity. rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia.
    change (2 ^ 6) with 64. replace (l + 32 + 64 * c) with ((l + 32) + c * 64) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Definition e_psc : sv := ltac2:(tb__ "0|0|
S72S1c7S72S1c4SdfPa9A1S5dZ34A1A3S5dZ3aA1A3").
Definition e_pidx : sv := SAlu ALU_AND (v 170) (SLit 31).
Lemma ze_psc : ltac2:(tb__ "0|0|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S1e2A3SfS162Vs;Vg;Vam;A3A1A3").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  unfold e_psc. rewrite !ze_alu, (ze169 Hml0), !ze_lit. cbn [zalu]. fold bP. pose proof bP_range as B. pose proof bP_fields as (_ & _ & M).
  change (52 mod 2 ^ 64 mod 64) with 52. change (58 mod 2 ^ 64 mod 64) with 58.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small ((bP * 2 ^ 52) mod 2 ^ 64) (2 ^ 64)) by (apply Z.mod_pos_bound; lia). exact M.
Qed.
Lemma ze_pidx : ltac2:(tb__ "0|0|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S1dbA3S163Vs;Vg;Vam;A3A3").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  unfold e_pidx. rewrite ze_alu, (ze170 Hml0), ze_lit. cbn [zalu]. rewrite (zHb_eq Hml0). pose proof amPar_ranges as (_ & _ & L3 & _ & _ & HI0).
  change (31 mod 2 ^ 64) with 31. rewrite (Z.mod_small (iPar + 192)) by lia. rewrite land_31.
  replace (iPar + 192) with (iPar + 6 * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_plast : ltac2:(tb__ "0|0|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S72S1c6SdfPa9A1S5dZ1fA1A3A3S12S162Vs;Vg;Vam;A3A1A3").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  rewrite ze_alu, (ze169 Hml0), ze_lit. cbn [zalu]. fold bP. pose proof bP_range as B. pose proof bP_fields as (M & _). pose proof amPar_ranges as (_ & _ & L3 & _).
  change (31 mod 2 ^ 64) with 31. rewrite (Z.mod_small bP) by lia. rewrite land_31, M. reflexivity.
Qed.

Lemma ze_bit_test (e : sv) (w : Z) : ltac2:(tb__ "0|3|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Ve;A3Vw;A3S1S34Z0M2Vw;A2S36Vw;S37Z2Z20A2A2A2S0S45S42Vw;S163Vs;Vg;Vam;A3A2S4dA3S0S8S108G0G1S72S1c6S84S46Q20Ve;A3S88S1c4S5dZ1A1S1dbA3A3A3G2A3F_;F_;F_;").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Ee Hw Hb. pose proof amPar_ranges as (_ & _ & L3 & _ & _ & HI0).
  rewrite ze_alu, ze_ext, Ee, ze_aluw, ze_pidx, ze_lit. cbn [zalu]. change (Z.of_N 32) with 32.
  change (1 mod 2 ^ 64 mod 2 ^ 32) with 1. rewrite (Z.mod_small iPar (2 ^ 32)) by lia. rewrite (Z.mod_small iPar 32) by lia.
  rewrite Z.shiftl_1_l. assert (P : 0 < 2 ^ iPar <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite (Z.mod_small (2 ^ iPar)) by lia.
  change ((toS 32 w) mod 2 ^ 64) with (sx32 w). pose proof (sx32_range w). pose proof (sx32_range (2 ^ iPar)).
  rewrite !Z.mod_small by lia. rewrite sx32_land by lia.
  replace (Z.land w (2 ^ iPar)) with 0; [reflexivity|]. symmetry.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec iPar k) as [<-|NE]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
Qed.

Lemma table_u16' c : ltac2:(tb__ "0|1|
S1S34Z0Vc;A2S36Vc;Z30A2A2S0S8S10eS110S3eZ2M0Vc;A2G0Se7A3A1S2fVc;S2bA2A3F_;").
Proof using . drop_sp.
  intros Hc.
  pose proof (forall_range_dec (fun c => zle (zsublist (2 * c) 2 size_classes_bytes) =? znth c size_classes) 0 48 ltac:(vm_compute; reflexivity) c Hc) as E.
  apply Z.eqb_eq in E. exact E.
Qed.
Lemma ze_pclass : ltac2:(tb__ "0|0|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S84S4dQ10S89P1S72S1c4S1e2S5dZ1A1A3Z2A3A3A3S2fSfS162Vs;Vg;Vam;A3A1S2bA2A3").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  pose proof amPar_ranges as (_ & _ & _ & _ & C & _). pose proof (znth_size_classes_range (am_sc amPar) C) as R.
  rewrite ze_ext. change (Z.of_N 16) with 16. cbn [zeval]. fold (zeval zr1 zl1 e_psc). rewrite ze_psc. cbn [zalu].
  change (1 mod 2 ^ 64 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite (Z.mod_small (am_sc amPar * 2)) by lia.
  replace (am_sc amPar * 2) with (2 * am_sc amPar) by lia. rewrite zl1_1, table_u16' by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_mul a b : ltac2:(tb__ "0|2|
S0S8S108S160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1S8aS1c8Va;Vb;A3A3S3aS3eS108G0G1Va;A3S108G0G1Vb;A3A2S37Z2Z40A2A2A3"). Proof using . reflexivity. Qed.
Definition pbN : bool := negb (am_maplen amPar =? 0).
Theorem ZF_pm : ltac2:(tb__ "0|0|
S177S60S10bS160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S184S1dcA1A3").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  pose proof amPar_ranges as (AV & FR & L3 & ML & C & HI0). pose proof (par_off_chk Hml0) as (O1 & O2 & O3). pose proof (zOff_eq Hml0) as [_ ZO].
  pose proof (znth_size_classes_range (am_sc amPar) C) as CR. pose proof R_all as RA. pose proof (zHb_range Hml0) as HB. pose proof maplenP_range as MR.
  pose proof (par_bits_clear Hml0) as [B1 B2].
  assert (EM1 : zeval zr1 zl1 (SMd M_MUL (SExt false 16%N (SLBytes 1%positive (SAlu ALU_SLL e_psc (SLit 1)) 2)) e_pidx) = znth (am_sc amPar) size_classes * iPar).
  { rewrite ze_mul, ze_pclass, ze_pidx. apply Z.mod_small. nia. }
  assert (EM2 : zeval zr1 zl1 (SMd M_MUL (SAlu ALU_ADD e_pidx (SLit 1)) (SExt false 16%N (SLBytes 1%positive (SAlu ALU_SLL e_psc (SLit 1)) 2))) = (iPar + 1) * znth (am_sc amPar) size_classes).
  { rewrite ze_mul, ze_alu, ze_pclass, ze_pidx, ze_lit. cbn [zalu].
    change (1 mod 2 ^ 64) with 1. rewrite (Z.mod_small (iPar + 1)) by lia. apply Z.mod_small. nia. }
  unfold pm_facts. fold e_psc e_pidx. apply Forall_app. split.
  - constructor. { cbn [zholds]. split; [lia|]. rewrite zr1_142. rewrite (Z.mod_small zM) by lia. change (2 ^ 4) with 16. unfold zM, U.Mal_nt__G1.Mal_nt_I.zM in *. lia. }
    constructor. { zfact. rewrite (ze170 Hml0), ze_lit. change (255 mod 2 ^ 64) with 255. lia. }
    constructor. { zfact. rewrite (ze171 Hml0), ze_lit. change (65535 mod 2 ^ 64) with 65535. lia. }
    constructor. { zfact. rewrite ze_plast, ze_pidx. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor. { zfact. rewrite (ze_bit_test (v 173) (am_avail amPar) (ze173 Hml0) ltac:(lia) B1), ze_lit. reflexivity. }
    constructor. { zfact. rewrite (ze_bit_test (v 174) (am_freed amPar) (ze174 Hml0) ltac:(lia) B2), ze_lit. reflexivity. }
    constructor. { zfact. rewrite ze_psc, ze_lit. change (47 mod 2 ^ 64) with 47. intros E. apply Z.ltb_lt in E. lia. }
    constructor. { zfact. rewrite ze_alu, ze_psc, !ze_lit. cbn [zalu]. change (1 mod 2 ^ 64 mod 64) with 1. change (94 mod 2 ^ 64) with 94. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small; lia. }
    constructor. { zfact. fold e_psc e_pidx. rewrite EM1, (ze171 Hml0). apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
    constructor. { zfact. fold e_psc e_pidx. rewrite EM2, (ze171 Hml0). intros E. apply Bool.negb_true_iff in E. apply Z.ltb_ge in E. nia. }
    constructor.
  - unfold pbN. destruct (Z.eqb_spec (am_maplen amPar) 0) as [E0|N0]; cbn [negb].
    + constructor; [|constructor]. zfact. rewrite ze_alu, (ze169 Hml0), !ze_lit. cbn [zalu]. fold bP. pose proof bP_range. pose proof bP_fields as (_ & M2 & _).
      change (12 mod 2 ^ 64 mod 64) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. rewrite (Z.mod_small bP) by lia. rewrite M2, E0. reflexivity.
    + pose proof (par_map_chk Hml0 N0) as [PM _]. pose proof bP_range as BR. pose proof bP_fields as (_ & M2 & _).
      assert (EML : zeval zr1 zl1 (SAlu ALU_SRL (v 169) (SLit 12)) = am_maplen amPar).
      { rewrite ze_alu, (ze169 Hml0), !ze_lit. cbn [zalu]. fold bP. change (12 mod 2 ^ 64 mod 64) with 12. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
        rewrite (Z.mod_small bP) by lia. exact M2. }
      constructor. { zfact. rewrite EML, ze_lit. change (0 mod 2 ^ 64) with 0. rewrite (proj2 (Z.eqb_neq _ _) N0). intros E. discriminate E. }
      constructor; [|constructor]. zfact. rewrite (ze_alu ALU_ADD), (ze_alu ALU_SLL), EML, (ze171 Hml0), !ze_lit. cbn [zalu]. change (8 mod 2 ^ 64 mod 64) with 8.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite (Z.mod_small (am_maplen amPar * 256)) by lia.
      change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
      replace (am_maplen amPar * 256 + (2 ^ 64 - 1)) with ((am_maplen amPar * 256 - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
      apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma pm_facts_sem pb : ltac2:(tb__ "0|1|
S1S0S45S9bS60S1bfS171A1S184Vpb;A1M0A3S46A3S0S45S9bS60S10cG0A3S46A3A2").
Proof using . drop_sp. destruct pb; split; vm_cast_no_check (@eq_refl bool true). Qed.

Definition ds_newN : list od := ltac2:(tb__ "0|0|
S43Sa3Sb4S43Sa3SafSdfPcA1A1S43Sa3Sb1S43Sa3Sb2S43Sa3Sb0S43Sa3Sb3S4fSa3A1A3A3A3A3A3A3").
Lemma ds_newN_ok : Forall od_ok ds_newN.
Proof using HMI HP12 Hgd Hml0 Hu. drop_sp.
  constructor; [exact (od_ok_shdr_entry Hml0)|]. constructor; [exact (od_ok_bptr_entry' Hml0)|]. constructor; [exact (od_ok_pbase_entry Hml0)|].
  constructor; [exact (od_ok_parmeta_entry Hml0)|]. constructor; [exact (od_ok_parea_entry Hml0)|]. constructor; [exact od_ok_secret_entry | constructor].
Qed.

Definition link_okbN (Lf Cs : sstate) (nf0 : list sprop) : bool := ltac2:(tb__ "0|4|
S44S4bS4aS4bS5aS5aA2M0A1M1S4aS60A1M2A2M3A1S45Lx;S17dVLf;VCs;A2G3G3S45Lp;R1G1G2S178S4bS9S5aA2S9S52S9S5aA2S1abR2A1A4S4aS9A1S4cS4cS4cS4cS4cS4cS4cS1c1S9S51S172R2R1A2A1Lu;VLf;A2S9bS9S9S51S171R1A1A1Lj;R1A3A2S9bG0S1d7R1A1R3A3A2S1a8R1A1A2S79VCs;A1A2S9bS60S60S9dS60S99R1A1Vnf0;A3Lp;R2A3A2S9bS60S1bfS171A1Vnf0;A3A2S9bS60S10cVnf0;A3A2Tkeys;Lnf;Ld;X4bx1Lp;S4dX44x2").
Lemma link_scratchN m (Lf Cs : sstate) nf0 rhoB w : ltac2:(tb__ "0|1|
S0S45S1dfVLf;VCs;Vnf0;A3S46A3S177S60S10bS160Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S15fVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2Vnf0;A3S170S169Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9M0VrhoB;A2S175S55VK;VLf;VrhoB;Vw;A5S3S62S62S1S170G0R1A2S175S55VK;VCs;R1Vw;A5A2LrhoB';A2F_;F_;F_;F_;").
Proof using . drop_sp.
  intros H ZF Hag HSP. unfold link_okbN in H. destruct (state_diff Lf Cs) as [[d nf]|] eqn:Hsd; try discriminate.
  apply andb_prop in H as [H Hsup]. apply andb_prop in H as [H Hvars0]. apply andb_prop in H as [H Hnf].
  apply andb_prop in H as [H Hwf]. apply andb_prop in H as [H Hkd]. apply andb_prop in H as [H Hsc]. apply andb_prop in H as [Hvars Hb].
  exists (setp rhoB (scratch_of d)). split; [exact (agrees_setp (rho1 m) rhoB (scratch_of d) Hag Hb)|].
  refine (relinkp segsU K rhoB Lf Cs w (scratch_of d) d nf Hvars Hwf Hsd (diffs_ok_scratch rhoB d Hsc Hkd) _ HSP).
  apply Forall_forall. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) Hnf p Hp) as E. apply existsb_exists in E as (p0 & Hp0 & E). apply sprop_eqb_sound in E. subst p0.
  exact (proj1 (Forall_forall _ _) (ZF_holdsm m (setp rhoB (scratch_of d)) nf0 (agrees_setp (rho1 m) rhoB (scratch_of d) Hag Hb) Hvars0 Hsup ZF) p Hp0).
Qed.

Lemma objs_b_eq pv nv : ltac2:(tb__ "0|0|
S0S4aS5bA1S18cVpv;Vnv;A2S50S5bS43S5bS17eS43S5bS185Vpv;Vnv;A2S43S5bSa6Sa9A1S4fS5bA1A3A3A3S178Sa3S5bSa6S1daA4A3A3").
Proof using . drop_sp. reflexivity. Qed.

Definition canonN (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S7bS74VLf;A1S83VLf;A1S6eVLf;A1S6dVLf;A1S75VLf;A1S18cS1d3VLf;A1S1d2VLf;A1A2S82VLf;A1S6fVLf;A1S6aVLf;A1A9").

Definition movedN (dsP : list od) (Lf : sstate) : sstate := ltac2:(tb__ "0|0|
S7bS74VLf;A1S83VLf;A1S6eVLf;A1S6dVLf;A1S75VLf;A1S50S5bS43S5bS17eS43S5bS185S1d3VLf;A1S1d2VLf;A1A2S43S5bSa6Sa9A1S4fS5bA1A3A3A3S178Sa3S5bSa6VdsP;A4A3S82VLf;A1S6fVLf;A1S6aVLf;A1A9").
Definition ds_liveN (Lf : sstate) : list od := ltac2:(tb__ "0|0|
S43Sa3Sa7SabS1d3VLf;A1S1d2VLf;A1SdfP85A1SdfP86A1A5S43Sa3Sa9S4fSa3A1A3A3").
Definition prefix_leaf_okbN (dsP : list od) (Lf : sstate) : bool := ltac2:(tb__ "0|c|
S4cS4cS4cS4cS4cS4cS4cS4cS4cS4cS4cS4cS4aS5bA1M0S45Lx;S6bVLf;A1M1S4dS5bG0G0S45Ll;R1S4dS5bG0G0S45Ll0;R1S4dS5bG0G0S45Ll1;R1S4dS5bG0S1a1S50S5bS1a4S5bU2M2S1a4S5bG2G1A3A3S43S5bR4S43S5bR2S4fS5bA1M3A3A3A3S6bS1e4VdsP;VLf;A2M4A1A2Lrest;Lo3;X4ax2Ll1;Lo2;X4ax2Ll0;Lo1;X4ax2Ll;Lo0;X4ax2S79G4A1A2S79S1e3VLf;A1M5A1A2S1a1S43S5bS185S1d3VLf;A1M6S1d2VLf;A1M7A2S43S5bSa6Sa9A1G3A3A3S178Sa3S5bSa6S1e1VLf;A1M8A4A2A2S9bSa3SaaG8A3A2S9bS5bS1bdS171A1S178Sa3S5bSa6VdsP;A4M9A3A2S9bS5bS91Pc8MaA1MbG9A3A2S9bS5bGbS178Sa3S5bSa6S1daA4A3A2S19bGaS6fVLf;A1A2A2S51S6aVLf;A1A1A2S1d6G6G7A2A2S1dfG5S182G6G7S46A3S184S46A1A3A2S1dfG5S182G6G7S4dA3S184S4dA1A3A2").

Lemma XliveN Lf : ltac2:(tb__ "0|0|
Sa3S9aSa3R1S1e1VLf;A1A3S177Sa3S14eVs;VL;Vg;Vam;R2A5S1daA3F_;Fd;").
Proof using HMI Hgd Hml0 Hu. drop_sp. clear HKc Hsm_pre EmW Evm. pose proof Hml0 as ML. pose proof HgPg as GP. intros d [<-|[<-|[]]]; cbn; od_pw. Qed.

Lemma prefix_linkN (dsP : list od) Lf rhoX tr0 msL md0 : ltac2:(tb__ "0|2|
S0S45S1e5VdsP;VLf;A2S46A3S177Sa3SacVam;A1VdsP;A3S14fVs;VL;Vg;Vam;VdsP;A5Sa3S9aSa3R1VdsP;A3Sb5Vam;R2A2F_;Fd;Sa3S9aSa3R1S1daA3S177Sa3S14eVs;VL;Vg;Vam;R2A5VdsP;A3F_;Fd;S170VrhoW;VrhoX;A2S175S55VK;VLf;VrhoX;S49S4aS12aA1S173Vtr0;S174VmsL;Vmd0;A2A4M0A5S3Sa0Q40A1S44Sa0Q8A1A1F_;M1G1S3S62S62S1S1d4Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VdsP;R2AcS1S170S169Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9R1A2S175S55VK;S182S1d3VLf;A1S1d2VLf;A1S1dcA3R1G0A5A2A2LrhoB;A2Lm1;A2F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hml0 Hrom Hsc48 Hsp Hsp_high Hu.
  intros H DSP PWP CNP HX1 Hag [Hsm HKw]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw.
  unfold prefix_leaf_okbN in H.
  apply andb_prop in H as [H HlinkF]. apply andb_prop in H as [H HlinkT]. apply andb_prop in H as [H Hpv]. apply andb_prop in H as [H Hlen]. apply andb_prop in H as [H Hnx].
  apply andb_prop in H as [H Hwfn]. apply andb_prop in H as [H HwP]. apply andb_prop in H as [H HvP]. apply andb_prop in H as [H Hdsl]. apply andb_prop in H as [H Hml].
  apply andb_prop in H as [H Hwfc]. apply andb_prop in H as [Hmv Hwfm].
  apply Pos.leb_le in Hnx.
  destruct (ss_objs Lf) as [|o0 [|o1 [|o2 [|o3 rest]]]] eqn:Eobjs; try discriminate.

  pose proof (smatch_move_last segsU rhoX Lf (tr0, mkCfg msL md0) 2 o2 ltac:(rewrite Eobjs; reflexivity) Hsm) as Hsm1. cbn zeta in Hsm1. rewrite Eobjs in Hsm1.
  pose proof (smatch_move_last segsU rhoX (mkSS (ss_pc Lf) (ss_regs Lf) (ss_fregs Lf) (ss_fcsr Lf) (ss_resv Lf) (remove_nth 2 (o0 :: o1 :: o2 :: o3 :: rest) ++ [o2]) (ss_facts Lf) (ss_next Lf) (ss_lenient Lf))
                (tr0, mkCfg msL md0) 2 o3 ltac:(reflexivity) Hsm1) as Hsm1'.
  cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hsm1'.

  assert (Hsm2 : smatch segsU rhoX (movedN dsP Lf) (tr0, mkCfg msL md0)).
  { eapply (smatch_canon rhoX _ (movedN dsP Lf) tr0 msL md0 Hsm1'); try reflexivity; [exact Hwfm | | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm)))))))))))].
    cbn [remove_nth app] in Hmv |- *. rewrite <- app_assoc. cbn [app]. exact Hmv. }

  destruct (release_seg [] dsP mW rhoX (movedN dsP Lf) tr0 msL md0 [o_stk_saved; o_gmeta (gl_pv Lf) (gl_nv Lf); obj_of OD_sct]
              riding_nil Hag Hsm2 eq_refl DSP PWP HvP HwP ltac:(intros d _; constructor)) as (m1 & Hsm3 & Hag3 & RID).
  rewrite app_nil_r in RID.

  assert (DSL : Forall DS (ds_liveN Lf)).
  { apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) Hdsl d Hd)|]. destruct Hd as [<-|[<-|[]]]; exact I. }
  pose proof (carve_on ds_newN m1 (set_rm rhoX m1) _ tr0 msL md0 (ob_cells o_stk_saved) [o_gmeta (gl_pv Lf) (gl_nv Lf); obj_of OD_sct] (ds_liveN Lf)
                Hag3 Hsm3 eq_refl Hml DSL
                ltac:(apply Forall_forall; intros d Hd; exact (proj1 (proj1 (Forall_forall _ _) ds_newN_ok d Hd)))
                ltac:(clear - Hml0; cbn; pose proof Hml0; od_pw) eq_refl
                ltac:(intros d Hd; apply (od_hold_m dsP m1 d RID (proj1 (Forall_forall _ _) ds_newN_ok d Hd) (HX1 d Hd)))
                (XliveN Lf) Hnx Hwfn) as Hsm4. cbn zeta in Hsm4.

  assert (HSP4 : SymSoundR.SP segsU K (canonN Lf) (set_rm rhoX m1) (tr0, mkCfg msL md0)) by (split; [exact Hsm4 | exact HKw]).
  pose proof ZF_pm as ZP. unfold pbN in *.
  destruct (am_maplen amPar =? 0); cbn [negb] in ZP |- *.
  - destruct (link_scratchN m1 (canonN Lf) (S_b_of (gl_pv Lf) (gl_nv Lf) false) (pm_facts false) (set_rm rhoX m1) (tr0, mkCfg msL md0) HlinkF ZP Hag3 HSP4) as (rhoB & HagB & HSPB).
    exists m1, rhoB. split; [exact RID|]. split; [exact HagB | exact HSPB].
  - destruct (link_scratchN m1 (canonN Lf) (S_b_of (gl_pv Lf) (gl_nv Lf) true) (pm_facts true) (set_rm rhoX m1) (tr0, mkCfg msL md0) HlinkT ZP Hag3 HSP4) as (rhoB & HagB & HSPB).
    exists m1, rhoB. split; [exact RID|]. split; [exact HagB | exact HSPB].
Qed.

Definition dsB_live (pv nv : sv) : list od := ltac2:(tb__ "0|0|
S43Sa3Sa7SabVpv;Vnv;SdfP85A1SdfP86A1A5S43Sa3Sa9S43Sa3Sb4S43Sa3SafS5dZ0A1A1S43Sa3Sb1S43Sa3Sb2S43Sa3Sb0S43Sa3Sb3S4fSa3A1A3A3A3A3A3A3A3A3").
Definition regs_b_okb (SF : sstate) : bool := ltac2:(tb__ "0|0|
S4cS4cS4cS4cS4cS4cS4cS4cS63S5eVSF;Z1A2S5dZ20ad4A1A2S63S5eVSF;Z2A2S72S1c5S61PaA1S5dN60A1A3A2A2S63S5eVSF;Z8A2SdfP8eA1A2A2S63S5eVSF;Z9A2S5dZ5a338A1A2A2S63S5eVSF;Z12A2S5dZ5a3d0A1A2A2S63S5eVSF;Z13A2SdfPcA1A2A2S63S5eVSF;ZaA2S61PacA1A2A2S63S5eVSF;ZbA2S1dbA2A2S9bS9S9S63S5eVSF;S38SaR1A1Z14A2A2S61R1A1A2Lj;S43S9P17S43S9P18S43S9P28S43S9P29S43S9P2aS43S9P2bS43S9P2cS43S9P2dS43S9P2eS43S9P2fS4fS9A1A3A3A3A3A3A3A3A3A3A3A3A2").
Definition b_leaf_okb (pv nv : sv) (SF : sstate) : bool := ltac2:(tb__ "0|4|
S4cS4cS4cS4cS4cS4cS4cS4cS4cS4cS1a1S9cS5bS6bVSF;A1M0A2S178Sa3S5bSa6S1d9Vpv;Vnv;A2M1A4M2A2S9bSa3SaaG1A3A2S9bS5bS1bdS171A1G2A3A2S4aS5bA1M3S45Lx;G0S4dS5bG3S20bR2S17eA2Ll;Lo;X4ax2A2S39S74VSF;A1Z2084cA2A2S1e0VSF;A1A2S1d5S6eVSF;A1S56A2A2S70S45Lx;S6dVSF;A1S46S5aS4dLv;X70x2A2S44S5aA1S45Lx;S75VSF;A1S5aS4dLs0;S46X44x2A2S19bPc8S6fVSF;A1A2A2S51S6aVSF;A1A1A2").
Definition b_run_okb (pv nv : sv) (pb : bool) : bool := ltac2:(tb__ "0|1|
S44S4aS111A1M0A1S45Lx;S112S55U12cS180S182Vpv;Vnv;Vpb;A3S46A5G0G0S45Ll;R1S4dS111G0G0S45Ll0;R1S114S45Lx;S115R2A1S4dS1d8Vpv;Vnv;S113R2A1A3S4dS4dS4dS4dS4dX114x7S111G0S4dLl2;Ll1;X4ax2Ll0;LLf;X4ax2Ll;S4dX44x2").
Lemma BCERT : ltac2:(tb__ "0|3|
S0S45S9bS4bS5aS5aA2M0G0S4cS1deS52S5aS5aR1A3M1S53S5aS5aR1A3M2S46A3S1deG1G2S4dA3A2Lq;S183A3S46A3").
Proof using . drop_sp. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma b_run_split pv nv pb : ltac2:(tb__ "0|1|
S0S45S1deVpv;Vnv;Vpb;A3S46A3S3S111S111S1S0S44S4aS111A1M0A1S112S55U12cS180S182Vpv;Vnv;Vpb;A3S46A5S47G0S43S111R1S4fS111A1A3A2A3S0S45S1d8Vpv;Vnv;S113R1A1A3S46A3A2LLf;A2F_;").
Proof using . drop_sp.
  unfold b_run_okb. intros H. destruct (sym_run segsU 300 CUTS0 (S_b_of pv nv pb) true) as [[|Lf [|]]|]; try discriminate.
  exists Lf. split; [reflexivity|]. destruct (lf_reason Lf); try discriminate. exact H.
Qed.
Lemma b_run_ok pv nv : ltac2:(tb__ "0|1|
S9aS4bS5aS5aA2S49S5aS5aVpv;Vnv;A4S183A3S3S111S111S1S0S44S4aS111A1M0A1S112S55U12cS180S182Vpv;Vnv;S1dcA3S46A5S47G0S43S111R1S4fS111A1A3A2A3S0S45S1d8Vpv;Vnv;S113R1A1A3S46A3A2LLf;A2F_;").
Proof using . drop_sp.
  intros Hin. pose proof (proj1 (forallb_forall _ _) BCERT (pv, nv) Hin) as C. cbn [fst snd] in C. apply andb_prop in C as [CT CF].
  unfold pbN. destruct (am_maplen amPar =? 0); cbn [negb]; [exact (b_run_split pv nv false CF) | exact (b_run_split pv nv true CT)].
Qed.
Lemma regs_b_okb_sound SF : ltac2:(tb__ "0|0|
S0S45S1e0VSF;A1S46A3S1S0S5aS5eVSF;Z1A2S5dZ20ad4A1A3S1S0S5aS5eVSF;Z2A2S72S1c5S61PaA1S5dN60A1A3A3S1S0S5aS5eVSF;Z8A2SdfP8eA1A3S1S0S5aS5eVSF;Z9A2S5dZ5a338A1A3S1S0S5aS5eVSF;Z12A2S5dZ5a3d0A1A3S1S0S5aS5eVSF;Z13A2SdfPcA1A3S1S0S5aS5eVSF;ZaA2S61PacA1A3S1S0S5aS5eVSF;ZbA2S1dbA3S9S9aS9R1S43S9P17S43S9P18S43S9P28S43S9P29S43S9P2aS43S9P2bS43S9P2cS43S9P2dS43S9P2eS43S9P2fS4fS9A1A3A3A3A3A3A3A3A3A3A3A3S0S5aS5eVSF;S38SaR2A1Z14A2A2S61R2A1A3F_;Fj;A2A2A2A2A2A2A2A2F_;").
Proof using . drop_sp.
  intros H. unfold regs_b_okb in H.
  apply andb_prop in H as [H Hlow]. apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10]. apply andb_prop in H as [H H19]. apply andb_prop in H as [H H18].
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H1 H2].
  repeat match goal with |- _ /\ _ => split end; try (apply sv_eqb_sound; assumption).
  intros j Hj. apply sv_eqb_sound. exact (proj1 (forallb_forall _ _) Hlow j Hj).
Qed.
Lemma b_leaf_okb_sound pv nv SF : ltac2:(tb__ "0|4|
S0S45S1d8Vpv;Vnv;VSF;A3S46A3S1S0S4aS5bA1S6bVSF;A1M0S43S5bS17eS9cS5bG0A2M1A3A3S1S0S45S1a1G1S178Sa3S5bSa6S1d9Vpv;Vnv;A2M2A4M3A2S46A3S1S0S45S9bSa3SaaG2A3S46A3S1S0S45S9bS5bS1bdS171A1G3A3S46A3S1S0S8S74VSF;A1Z2084cA3S1S0S45S1e0VSF;A1S46A3S1S0S4aS5aA1S6eVSF;A1S56A3S1S0S70S6dVSF;A1S76A3S1S0S44S5aA1S75VSF;A1S4eS5aA1A3S1S199Pc8S6fVSF;A1A2S0S45S6aVSF;A1S4dA3A2A2A2A2A2A2A2A2A2A2F_;").
Proof using . drop_sp.
  intros H. unfold b_leaf_okb in H.
  apply andb_prop in H as [H Hlen]. apply andb_prop in H as [H Hnx]. apply andb_prop in H as [H Hrs]. apply andb_prop in H as [H Hfc]. apply andb_prop in H as [H Hfr].
  apply andb_prop in H as [H Hrg]. apply andb_prop in H as [H Hpc]. apply andb_prop in H as [H Hhd]. apply andb_prop in H as [H Hv]. apply andb_prop in H as [Hm Hds].
  destruct (ss_objs SF) as [|o t] eqn:Eo; [discriminate|]. apply obj_eqb_sound in Hhd. subst o.
  split; [reflexivity|]. split; [exact Hm|]. split; [exact Hds|]. split; [exact Hv|]. split; [apply Z.eqb_eq; exact Hpc|]. split; [exact Hrg|].
  split; [apply svl_eqb_sound; exact Hfr|]. split; [destruct (ss_fcsr SF); try discriminate; reflexivity|].
  split; [destruct (ss_resv SF); [discriminate | reflexivity]|]. split; [apply Pos.leb_le; exact Hnx|]. destruct (ss_lenient SF); [discriminate | reflexivity].
Qed.

Hypothesis IH : ltac2:(tb__ "0|2|
S62VTR;S176S55S1faS19fS15eVam;A1A1S43ScVg;VX;A3M0VU;S13fS145Vs;Vg;Vam;Vsr;A4VL;A2M1VK;A5S155S151A1R1A4S1bcS55S57R1S153S55Se1S151G0VU;G1VK;A7A4A2FrhoX;").

Lemma pvnv_sem pv nv : ltac2:(tb__ "0|0|
S9aS4bS5aS5aA2S49S5aS5aVpv;Vnv;A4S183A3S1S0S45Sa8Vpv;A1S46A3S0S45Sa8Vnv;A1S46A3A2F_;").
Proof using . drop_sp. unfold PVNV. intros [E|[E|[]]]; injection E as <- <-; split; reflexivity. Qed.
Lemma DS_bptr0 : DS (OD_bptr (SLit 0)). Proof using Hml0. split; [reflexivity | exact Hml0]. Qed.
Lemma DS_gmeta pv nv : ltac2:(tb__ "0|0|
S0S45Sa8Vpv;A1S46A3S0S45Sa8Vnv;A1S46A3SacVam;Sa7SabVpv;Vnv;SdfP85A1SdfP86A1A5A2F_;F_;").
Proof using . drop_sp. intros Hp Hn. split; [|exact I]. unfold ds_checkb. cbn [od_svs dcells map snd forallb dsxb kmemv kbitsv]. rewrite Hp, Hn. reflexivity. Qed.
Lemma bptr_vs_g pv nv : ltac2:(tb__ "0|2|
S0S45Sa8Vpv;A1S46A3S0S45Sa8Vnv;A1S46A3S4S34S35S166VL;Vam;A2M0Z8A2S15dVL;Vg;A2M1A2S34S35G1Z28A2G0A2A2F_;F_;").
Proof using HMI HXz Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hp Hn. pose proof (od_disjoint (OD_bptr (SLit 0)) (OD_meta KG pv nv (v 133) (v 134)) DS_bptr0 (DS_gmeta pv nv Hp Hn) ltac:(split; [exact Hml0 | split; [exact I | exact I]])) as D.
  unfold SymState.ranges_disjoint, dhi in D. cbn [fst snd dlo dsz klo] in D. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am KG) with zG in D. lia.
Qed.
Lemma bptr_owned x : ltac2:(tb__ "0|1|
S1S34S166VL;Vam;A2M0Vx;A2S36Vx;S35G0Z8A2A2A2Sf4VL;Vs;Vx;A3F_;").
Proof using HMI HXz Hgd Hml0 Hsc48 Hsp Hu. try clear Hsp_high. try clear Hdepth.
  intros Hx. pose proof (proj2 (proj2 (proj2 (hdr_cells Hml0)))) as C0.
  pose proof (image_cell_owned X (Some (g, i)) U s L HI HXr HL (MCell (LMem (am_mem am)) 8 (VP g)) C0 (Z.to_nat (x - zM)) ltac:(cbn [mc_w]; lia)) as OW. cbn [mc_loc] in OW.
  replace (loc_addr L (LMem (am_mem am))) with zM in OW by (unfold zM, U.Mal_nt__G1.Mal_nt_I.zM, addr_of; reflexivity). replace x with (zM + Z.of_nat (Z.to_nat (x - zM))) by lia. exact OW.
Qed.
Lemma meta_locs_g l : ltac2:(tb__ "0|2|
S9aSeaVl;S1cfVg;A1A3S1S34S15dVL;Vg;A2M0SecVL;Vl;A2M1A2S36G1S35G0Z28A2A2A2F_;").
Proof using HIr HMI HP12 HR2g Hgd Hsc48 Hu IH mW. drop_sp.
  assert (AGq : forall dd, loc_addr L (LMem (padd g dd)) = addr_of L g + dd) by (intros dd; unfold addr_of, loc_addr; destruct g; cbn [padd]; lia).
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits. unfold zG, U.Mal_nt__G1.Mal_nt_I.zG.
  intros [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AGq; lia.
Qed.

Theorem call_from_leaf pv nv (dsP1 dsCP1 : list od) m1 rhoT SF msF : ltac2:(tb__ "0|4|
S9aS4bS5aS5aA2S49S5aS5aVpv;Vnv;A4S183A3S1d4Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VdsP1;Vm1;AcS170S169Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm1;A9VrhoT;A2S0S45S1d8Vpv;Vnv;VSF;A3S46A3S175S55VK;VSF;VrhoT;S49S4aS12aA1S173Vtr;S174VmsF;Vmd;A2A4M0A5Sa3S9aSa3R1VdsP1;A3S4S198Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S9aSa3R2VdsCP1;A3A2F_;Fd;Sa3S9aSa3R1VdsCP1;A3M1S1S9aSa3R2VdsP1;A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3R2AaS144R2A1A2A2F_;Fd;SeaS9aSeaR1S50SeaS1f5Vs;Vg;Vam;A3S43SeaSf6S35Sf9S3eZ8S15eVam;A1A2A2A1S4fSeaA1A3A3A3S4S9aSeaR2S1cfVg;A1A3S3Sa3Sa3S1G1S1S34Sa5Vs;VL;Vg;Vam;R1A5SecVL;R3A2M2A2S36G2Sa4Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;Sa3S9aSa3R1S1d9Vpv;Vnv;A2A3S177Sa3S14eVs;VL;Vg;Vam;R2A5VdsP1;A3F_;Fd;Sa3G1S4S34Sa4Vs;VL;Vg;Vam;R2A5S15dVL;Vg;A2M3A2S34S35G3Z28A2Sa5Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;VTR;SdeS0SdeR1G0A3Lw;S1bcS55S57Vrho;S153S55Se1S151VX;VU;S13fVsr;VL;A2VKc;A7A4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TRR.
  intros Hpv RID HagT CERT [HsmT HKw] P1_ent P1_okC P1_locs P1_X P1_g. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw.
  pose proof RID as (RS & RPW & RV & RH & RM & RW).
  destruct (b_leaf_okb_sound pv nv SF CERT) as (Ho & Hm & Hds & Hvars & Hpc & Hrg & Hfr & Hfc & Hrs & Hnx & Hlen).
  destruct (regs_b_okb_sound SF Hrg) as (R1 & R2 & R8 & R9 & R18 & R19 & R10 & R11 & Rlow).
  pose proof (pvnv_sem pv nv Hpv) as [SPV SNV].
  assert (DSB : forall d, In d (dsB_live pv nv) -> dcond d).
  { intros d Hd. cbn [dsB_live In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [dcond]; first [exact I | exact Hml0]. }

  destruct (carve_back dsP1 m1 rhoT SF tr msF md (ob_cells o_stk_saved) (tl (ss_objs SF)) (dsB_live pv nv) RID HagT HsmT
              ltac:(rewrite Ho at 1; reflexivity) Hm Hds DSB P1_X Hnx RW) as [HSM' HFR]. cbn zeta in HSM', HFR.
  pose proof (restore_rm segsU rhoT _ (tr, mkCfg msF md) mW HSM' HFR) as HSMF. cbn [ss_objs] in HSMF.
  set (SF' := mkSS (ss_pc SF) (ss_regs SF) (ss_fregs SF) (ss_fcsr SF) (ss_resv SF) (ss_objs SF ++ map obj_of dsP1) (ss_facts SF) (ss_next SF) (ss_lenient SF)) in *.
  set (rhoF := set_rm rhoT mW) in *.
  assert (HagF : agreesW rhoF) by exact (agrees_of_V rhoT (agreesV_of m1 rhoT HagT)).

  assert (HSF_objs : ss_objs SF' = oStkF (ob_cells o_stk_saved) :: (tl (ss_objs SF) ++ map obj_of dsP1)) by (cbn [ss_objs SF']; rewrite Ho at 1; reflexivity).
  assert (HSF_match : objs_matchb (tl (ss_objs SF) ++ map obj_of dsP1) (map obj_of (dsB_live pv nv ++ dsP1)) = true).
  { rewrite map_app. apply objs_matchb_app; [exact Hm | apply objs_matchb_refl]. }
  assert (HdsF_DS : forallb ds_checkb (dsB_live pv nv ++ dsP1) = true).
  { rewrite forallb_app, Hds. apply forallb_forall. intros d Hd. exact (proj1 (proj1 (Forall_forall _ _) RS d Hd)). }
  assert (HdsF_cond : forall d, In d (dsB_live pv nv ++ dsP1) -> dcond d).
  { intros d Hd. apply in_app_iff in Hd as [Hd|Hd]; [exact (DSB d Hd) | exact (proj2 (proj1 (Forall_forall _ _) RS d Hd))]. }
  assert (HdsF_ent : forall d, In d (dsB_live pv nv ++ dsP1) -> od_ok d \/ In d (U.Mal_nt__G3.Mal_nt_V7.dsX dsCP1 [OD_meta KG pv nv (v 133) (v 134)] [OD_bptr (SLit 0)])).
  { intros d Hd. unfold U.Mal_nt__G3.Mal_nt_V7.dsX. apply in_app_iff in Hd as [Hd|Hd].
    - cbn [dsB_live In] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
      + right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
      + left. exact od_ok_sct.
      + left. exact (od_ok_shdr_entry Hml0).
      + right. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity.
      + left. exact (od_ok_pbase_entry Hml0).
      + left. exact (od_ok_parmeta_entry Hml0).
      + left. exact (od_ok_parea_entry Hml0).
      + left. exact od_ok_secret_entry.
    - destruct (P1_ent d Hd) as [Hok|HC]; [left; exact Hok | right; apply in_app_iff; left; exact HC]. }
  assert (HdsC : forall d, In d dsCP1 -> In d (dsB_live pv nv ++ dsP1) /\ od_ok_at s3v d /\ od_chgC d).
  { intros d Hd. destruct (P1_okC d Hd) as (A & B & C). split; [apply in_app_iff; right; exact A | split; [exact B | exact C]]. }
  assert (HdsO : forall d, In d [OD_meta KG pv nv (v 133) (v 134)] -> In d (dsB_live pv nv ++ dsP1) /\ drom d = None /\ zG <= dlo d /\ dhi d <= zG + 40).
  { intros d [<-|[]]. split; [apply in_app_iff; left; left; reflexivity|]. split; [reflexivity|]. unfold dhi. cbn [dlo dsz klo]. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am KG) with zG. lia. }
  assert (HdsO_cover : forall x, zG <= x < zG + 40 -> exists d, In d [OD_meta KG pv nv (v 133) (v 134)] /\ dlo d <= x < dhi d).
  { intros x Hx. exists (OD_meta KG pv nv (v 133) (v 134)). split; [left; reflexivity|]. unfold dhi. cbn [dlo dsz klo]. change (U.Mal_nt__G1.Mal_nt_D.klo s L g am KG) with zG. lia. }
  pose proof (par_zone Hml0) as (PZ1 & PZ2 & PZ3 & PZ4 & PZ5 & PZ6 & PZ7 & PZ8). pose proof R_all as RA.
  assert (HdsB : forall d, In d [OD_bptr (SLit 0)] -> In d (dsB_live pv nv ++ dsP1) /\ drom d = None /\ zfree d
    /\ (forall c, In c (image s3v ++ footer_cells s3v) -> cmeets L c (dlo d) (dhi d - dlo d) -> False)
    /\ (dhi d <= 0x10000 \/ 0x5b000 <= dlo d) /\ 4096 <= dlo d /\ (forall x, dlo d <= x < dhi d -> alloc_owned L s x)).
  { intros d [<-|[]]. split; [apply in_app_iff; left; cbn; tauto|]. split; [reflexivity|]. split; [exact (zfree_of _ DS_bptr0 I)|].
    unfold dhi. cbn [dlo dsz]. replace (zM + 8 - zM) with 8 by lia.
    split; [exact bptr_free|]. split; [lia|]. split; [lia|]. exact bptr_owned. }
  assert (Hlocs : forall l, In l ((((l1_locs ++ [LCtx (CTX_usage + 8 * sc)]) ++ []) ++ meta_locs g)) ->
            (exists d, In d dsCP1 /\ dlo d <= loc_addr L l < dhi d) \/ (zG <= loc_addr L l < zG + 40)).
  { intros l Hl. rewrite app_nil_r in Hl. apply in_app_iff in Hl as [Hl|Hl]; [|right; exact (meta_locs_g l Hl)].
    destruct (P1_locs l Hl) as [Hg'|Hd]; [right; exact (meta_locs_g l Hg') | left; exact Hd]. }
  assert (HdsCB_g : forall d, In d (dsCP1 ++ [OD_bptr (SLit 0)]) -> dhi d <= zG \/ zG + 40 <= dlo d).
  { intros d Hd. apply in_app_iff in Hd as [Hd|[<-|[]]]; [exact (P1_g d Hd)|]. unfold dhi. cbn [dlo dsz]. exact (bptr_vs_g pv nv SPV SNV). }

  assert (EVF : forall e, zsupported e = true -> sv_vars_all below200 e = true -> eval rhoF e = Z_to_bv 64 (zeval zr1 zl1 e)).
  { intros e Hs Hv. exact (EV rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) rhoF e HagF Hv Hs). }
  pose proof sp0_range4 as SPR.
  assert (HSF_sp : eval rhoF (reg_sv SF' 2) = Z_to_bv 64 (sp0 - 96)).
  { change (reg_sv SF' 2) with (reg_sv SF 2). rewrite R2, (EVF (SAlu ALU_ADD (SVar 10) (SLit (-96))) eq_refl eq_refl). apply f_equal.
    rewrite ze_alu, ze_lit. change (zeval zr1 zl1 (SVar 10)) with (zr1 10%positive mod 2 ^ 64). rewrite zr1_10. change (bv_unsigned (rw rho 10%positive)) with sp0. cbn [zalu].
    rewrite (Z.mod_small sp0) by lia. change ((-96) mod 2 ^ 64) with (2 ^ 64 - 96).
    replace (sp0 + (2 ^ 64 - 96)) with ((sp0 - 96) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (Ha0 : bv_unsigned (eval rhoF (reg_sv SF' 10)) = addr_of L gPar).
  { change (reg_sv SF' 10) with (reg_sv SF 10). rewrite R10, (EVF (SVar 172) eq_refl eq_refl). change (zeval zr1 zl1 (SVar 172)) with (zeval zr1 zl1 (v 172)). rewrite (ze172 Hml0). apply u64_of_sum. pose proof (zQ_range Hml0). pose proof (ceiling_small L). unfold zQ, U.Mal_nt__G1.Mal_nt_I.zQ in *. lia. }
  assert (Ha1 : bv_unsigned (eval rhoF (reg_sv SF' 11)) = iPar).
  { change (reg_sv SF' 11) with (reg_sv SF 11). rewrite R11, (EVF e_pidx eq_refl eq_refl), ze_pidx. apply u64_of_sum. pose proof amPar_ranges. lia. }
  refine (call_safe HdepthT msF rhoF HagF SF' (ob_cells o_stk_saved) (tl (ss_objs SF) ++ map obj_of dsP1) (dsB_live pv nv ++ dsP1) dsCP1
            [OD_meta KG pv nv (v 133) (v 134)] [OD_bptr (SLit 0)]
            HSF_objs HSF_match HSMF HdsF_DS HdsF_cond HdsF_ent HdsC HdsO HdsO_cover HdsB Hlocs HdsCB_g
            Hpc Hfr Hfc Hrs HSF_sp Ha0 Ha1 eq_refl IH HKw R1 R8 R9 R18 R19 Rlow).
Qed.

Theorem segB_call pv nv (dsP1 dsCP1 : list od) m1 rhoB : ltac2:(tb__ "0|3|
S9aS4bS5aS5aA2S49S5aS5aVpv;Vnv;A4S183A3S1d4Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VdsP1;Vm1;AcS170S169Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm1;A9VrhoB;A2Sa3S9aSa3R1VdsP1;A3S4S198Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S9aSa3R2VdsCP1;A3A2F_;Fd;Sa3S9aSa3R1VdsCP1;A3M0S1S9aSa3R2VdsP1;A3S1S197Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S143Vs;Vg;Vam;A3R2AaS144R2A1A2A2F_;Fd;SeaS9aSeaR1S50SeaS1f5Vs;Vg;Vam;A3S43SeaSf6S35Sf9S3eZ8S15eVam;A1A2A2A1S4fSeaA1A3A3A3S4S9aSeaR2S1cfVg;A1A3S3Sa3Sa3S1G0S1S34Sa5Vs;VL;Vg;Vam;R1A5SecVL;R3A2M1A2S36G1Sa4Vs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;Sa3S9aSa3R1S1d9Vpv;Vnv;A2A3S177Sa3S14eVs;VL;Vg;Vam;R2A5VdsP1;A3F_;Fd;Sa3G0S4S34Sa4Vs;VL;Vg;Vam;R2A5S15dVL;Vg;A2M2A2S34S35G2Z28A2Sa5Vs;VL;Vg;Vam;R2A5A2A2F_;Fd;VTR;S175S55VK;S182Vpv;Vnv;S1dcA3VrhoB;A4S1bcS55S57Vrho;S153S55Se1S151VX;VU;S13fVsr;VL;A2VKc;A7A4A2F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth HdepthT Hgd Hgd_holds Hm_sct Hml0 Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs IH TR_pointwise TR_seq.
  intros Hpv RID HagB P1_ent P1_okC P1_locs P1_X P1_g.
  destruct (b_run_ok pv nv Hpv) as (Lf & Hrun & CERT).
  eapply TR_seq.
  - apply (segRm m1 CUTS0 300 (S_b_of pv nv pbN) [Lf] (fun w => exists rhoT, agrees (rho1 m1) rhoT /\ SymSoundR.SP segsU K (lf_state Lf) rhoT w)
             rhoB ltac:(destruct pbN; reflexivity) ltac:(unfold Pos.le; destruct pbN; cbn; discriminate) Hrun HagB).
    intros Lf' rhoT w [<-|[]] HagT HSP. exists rhoT. split; [exact HagT | exact HSP].
  - apply TR_pointwise. intros [tr0 [msF md0]] (rhoT & HagT & HSP).
    pose proof HSP as [_ HKw]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HKw. destruct (HKc _ _ HKw) as (_ & -> & ->).
    exact (call_from_leaf pv nv dsP1 dsCP1 m1 rhoT (lf_state Lf) msF Hpv RID HagT CERT HSP P1_ent P1_okC P1_locs P1_X P1_g).
Qed.

End V.
End Mal_nt_V11.
