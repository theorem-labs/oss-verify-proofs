(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "False"; "True"; "iff"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "ameta"; "am_next"; "am_last"; "region"; "am_sc"; "st_free_meta_head"; "MUsed"; "astate"; "MFree"; "am_prev"; "am_maplen"; "am_aidx"; "am_mem"; "am_freed"; "st_seq"; "ones"; "sptr_eqb"; "frame"; "okay_to_free"; "st_active"; "bit"; "st_unmap_seq"; "stride_of"; "usage_of"; "am_avail"; "class_size"; "IRet"; "am_set_links"; "nth_slot"; "slot_start"; "ss_fr"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_meta_alloc_shift"; "st_regions"; "zset"; "RkMap"; "am_slots"; "bounce_idx"; "itree"; "nontrivial_free"; "osptr_eqb"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_brk"; "st_init_done"; "st_usage"; "FGroup"; "PGSZ"; "SP"; "brkst"; "fkind"; "fr_kind"; "free_meta"; "links_of"; "page_round"; "prid"; "size_classes"; "slotst"; "st_bounces"; "with_links"; "znth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D"; "od"; "dlo"; "dhi"; "OD_free"; "obj_of"; "FM"; "FG"; "OD_fmh"; "ds_checkb"; "DS"; "OD_guard"; "drom"; "OD_meta"; "dcells"; "FT"; "rngD"; "dcond"; "KG"; "range64D"; "KN"; "OD_usage"; "useq_okb"; "KP"; "OD_act"; "OD_seq"; "OD_useqL"; "fkey"; "kcond"; "klo"; "kptr"; "mkey"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "cons"; "bool"; "list"; "true"; "nat"; "pair"; "app"; "andb"; "false"; "nil"; "None"; "orb"; "fst"; "S"; "snd"; "unit"; "negb"; "tt"; "@Stdlib.Lists.List"; "In"; "forallb"; "NoDup"; "existsb"; "tl"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "callee_saved"; "pre_fregs"; "pre_reg"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "modulo"; "of_nat"; "sub"; "eqb"; "div"; "leb"; "ltb"; "opp"; "to_nat"; "land"; "ldiff"; "testbit"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "MT"; "active_hd"; "mcell"; "loc_addr"; "usedX"; "mc_w"; "LCtx"; "keys"; "mc_loc"; "Inv"; "image"; "CTX_usage"; "alloc_owned"; "cell_holds"; "le_byte"; "region_of"; "footprint"; "CTX_active"; "group_extent"; "meta_bits"; "optr"; "sval"; "user_blocks"; "CTX_free_meta_head"; "VZ"; "ly_reg"; "mc_val"; "memb"; "sval_num"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "SAlu"; "swf"; "smatch"; "rw"; "valuation"; "SExt"; "SPNot"; "SPBranch"; "obj_wf"; "SLBytes"; "reg_sv"; "ss_lenient"; "ss_next"; "SAluW"; "SVar"; "eval"; "rm"; "ss_objs"; "sstate"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "obj_holds"; "sprop_eqb"; "ss_facts"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "v"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I"; "sc"; "zl1"; "zr1"; "nQ"; "pQ"; "fmQ"; "amPar"; "ftQ"; "iPar"; "anQ"; "gPar"; "rho1"; "zG"; "fmem"; "apQ"; "mask"; "fmL"; "zM"; "zl1_any"; "zr1_any"; "frPar"; "ftL"; "zB"; "zNn"; "zU"; "optrA"; "udw"; "zA8"; "zNx"; "zPp"; "zPv"; "zSeq";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.V.Free3"; "s_m"; "fshape"; "ds_t2new"; "dsT"; "l1_locs"; "E_act"; "E_usage"; "dsCT"; "CREL"; "E_avN"; "E_frN"; "LOCS"; "an2"; "fq_locs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "psupported"; "toS"; "sx32"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "C_U"; "addr_of"; "topL"; "holds"; "mc_chk_guard"; "vm_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "meta_locs"; "delta"; "set_hd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "agrees"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.V"; "hasf"; "ot3"; "cx3"; "X_sz"; "F_18_lt"; "F_bnc_lt"; "F_last0"; "F_stA_lt"; "F_stB_lt"; "F_us_lt"; "F_us_lt0"; "X_stA"; "X_stB"; "X_9cnt"; "X_bnc"; "free_reason_okb"; "keep_reason_okb"; "s_m"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7.V"; "s3v"; "amPar'"; "s3r"; "s2n"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V7.V.ReabC"; "dsX"; "gslot"; "stk"; "m'v"; "HdsF"; "m'c"; "oStkF"; "touchedV"; "HdsX_sub"; "NRELW"; "gslotb"; "stkb"; "EmW'"; "meets"; "od_chgC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z"; "od_disj"; "needs_ring"; "sp0"; "D0"; "zfree"; "od_pairwise"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db"; "od_ok_at"; "od_ok"; "cellsD"; "cellsInD"; "dunkD"; "semD"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "VmMaps"; "m_vmmaps"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W"; "od_chg"; "oStkF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab"; "objs_matchb"; "m'"; "touched"; "touched_dec"; "cell_from_od"; "cell_from_od_sub"; "cell_from_od_zero"; "m'_in"; "m'_out"; "@Corelib.Init.Peano"; "lt"; "le"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "sym_run"; "stop_reason"; "lf_reason"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs"; "S_t1_of"; "S_t2_of"; "o_gmeta"; "o_stk_saved"; "objs_t2"; "O_guard_"; "PVNV"; "nt_sc"; "facts_t2"; "nt_last"; "F_t1hi"; "F_t1lo"; "CUTSP"; "F_all"; "F_base"; "F_freeable"; "F_sc48"; "nt_maplen"; "regs_t2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.V.Free3.RingGen"; "an2"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "dq_post"; "fgm_s1"; "fgm_s5"; "nmask"; "fgm_res"; "fgm_post"; "or_post"; "seq_post"; "fq_post"; "shape_kept"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NTE_U"; "in_zslots"; "Posts_nt"; "magree"; "xzomb"; "Pre_nt"; "zslotb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "mkMA";
"@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3"; "t2_run_okb"; "riding"; "t1_P2"; "gkeep"; "ds_new1"; "useq_cell_okb"; "E_seq'"; "F_seq_eq"; "F_seq_ne"; "ds_live1"; "keep_okb"; "leaf_okb"; "leaf_regs_map"; "prefix_leaf_okb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "LQP"; "obj_vars_all"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_AND"; "BC_LTU"; "BC_NE"; "ALU_OR"; "ALU_SRL"; "ALU_SUB"; "ALU_XOR"; "BC_EQ"; "@Corelib.Init.Nat"; "add"; "mul"; "@Corelib.Init.Specif"; "sumbool"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage"; "deltaU"; "dq_locs"; "rec_locs"; "seq_locs_b"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "cellZ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.V.Keep"; "s_k"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal"; "zomb_rel"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN"; "REALPOST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "fneed"; "nf_post"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "tier"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules"; "TRrules"; "tr_conseq"; "tr_disj"; "tr_pointwise"; "tr_pure"; "tr_refl"; "tr_run"; "tr_seq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost"; "am_activate"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "cmeets"; "xraw"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "with_mem"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested"; "fgn_s2"; "fgn_s3"; "fgn_s3v"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.V.Free3.Mid"; "Q2"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4"; "l1_locs"].
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
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mal_nt_V4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1bcS115VX;S6dS6eS8S6aA2S74S8S6aVg;Vi;A4A2VU;S192Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Local Abbreviation HXr := (@U.Mal_nt__G1.Mal_nt_I.HXr s X HXz).
Hypothesis Hu : ltac2:(tb__ "0|0|
Sa1VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§1§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§1§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation Hctx := (§1§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6aSdaQ40Sc1Vrho;PcA2A2S116VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S6aSdaQ40Sc1Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Notation "§2§ h__" := (h__ L am) (at level 10, h__ global).
Local Abbreviation zM := (§2§ U.Mal_nt__G1.Mal_nt_I.zM).
Local Abbreviation zPv := (§2§ U.Mal_nt__G1.Mal_nt_I.zPv).
Local Abbreviation zNx := (§2§ U.Mal_nt__G1.Mal_nt_I.zNx).
Local Abbreviation bits := (@U.Mal_nt__G1.Mal_nt_I.bits am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Notation "§3§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI Hu) (at level 10, h__ global).
Local Abbreviation G := (§3§ U.Mal_nt__G1.Mal_nt_I.G).
Local Notation "§4§ h__" := (h__ s X g am Hu) (at level 10, h__ global).
Local Abbreviation HMg_inst := (§4§ U.Mal_nt__G1.Mal_nt_I.HMg_inst).
Local Abbreviation g_key := (§4§ U.Mal_nt__G1.Mal_nt_I.g_key).
Local Abbreviation Hres := (§3§ U.Mal_nt__G1.Mal_nt_I.Hres).
Local Notation "§5§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§5§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation maplen_range := (§5§ U.Mal_nt__G1.Mal_nt_I.maplen_range).
Local Abbreviation bits_range := (§5§ U.Mal_nt__G1.Mal_nt_I.bits_range).
Local Abbreviation linked_ring := (§5§ U.Mal_nt__G1.Mal_nt_I.linked_ring).
Local Abbreviation prev_used := (§5§ U.Mal_nt__G1.Mal_nt_I.prev_used).
Local Abbreviation next_used := (§5§ U.Mal_nt__G1.Mal_nt_I.next_used).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Notation "§6§ h__" := (h__ s g) (at level 10, h__ global).
Local Abbreviation fmQ := (§6§ U.Mal_nt__G1.Mal_nt_I.fmQ).
Local Abbreviation fmL := (§6§ U.Mal_nt__G1.Mal_nt_I.fmL).
Local Abbreviation ftQ := (§6§ U.Mal_nt__G1.Mal_nt_I.ftQ).
Local Abbreviation ftL := (§6§ U.Mal_nt__G1.Mal_nt_I.ftL).
Local Abbreviation zF := (@U.Mal_nt__G1.Mal_nt_I.zF s L).
Local Notation "§7§ h__" := (h__ s L g) (at level 10, h__ global).
Local Abbreviation zFp := (§7§ U.Mal_nt__G1.Mal_nt_I.zFp).
Local Abbreviation zFn := (§7§ U.Mal_nt__G1.Mal_nt_I.zFn).
Local Abbreviation zTTp := (§7§ U.Mal_nt__G1.Mal_nt_I.zTTp).
Local Abbreviation zSeq := (@U.Mal_nt__G1.Mal_nt_I.zSeq s).
Local Abbreviation Hctx_ok := (§1§ U.Mal_nt__G1.Mal_nt_I.Hctx_ok).
Local Abbreviation seq_range := (§1§ U.Mal_nt__G1.Mal_nt_I.seq_range).
Local Abbreviation useq_len := (§1§ U.Mal_nt__G1.Mal_nt_I.useq_len).
Local Abbreviation useq_byte := (@U.Mal_nt__G1.Mal_nt_I.useq_byte s L X U g i gd vm rd0 wok0 HMI Hgd).
Local Abbreviation fmem := (@U.Mal_nt__G1.Mal_nt_I.fmem s X).
Local Abbreviation fmem_facts := (§4§ U.Mal_nt__G1.Mal_nt_I.fmem_facts).
Local Abbreviation fmem_head := (§1§ U.Mal_nt__G1.Mal_nt_I.fmem_head).
Local Abbreviation fmL_cases := (§3§ U.Mal_nt__G1.Mal_nt_I.fmL_cases).
Local Abbreviation nQ := (@U.Mal_nt__G1.Mal_nt_I.nQ g am).
Local Abbreviation pQ := (@U.Mal_nt__G1.Mal_nt_I.pQ g am).
Local Notation "§8§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation anQ := (§8§ U.Mal_nt__G1.Mal_nt_I.anQ).
Local Abbreviation apQ := (§8§ U.Mal_nt__G1.Mal_nt_I.apQ).
Local Notation "§9§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation zNm := (§9§ U.Mal_nt__G1.Mal_nt_I.zNm).
Local Abbreviation zNn := (§9§ U.Mal_nt__G1.Mal_nt_I.zNn).
Local Abbreviation zPp := (§9§ U.Mal_nt__G1.Mal_nt_I.zPp).
Local Abbreviation zU := (@U.Mal_nt__G1.Mal_nt_I.zU s am).
Local Abbreviation zB := (@U.Mal_nt__G1.Mal_nt_I.zB s am).
Local Abbreviation zA8 := (@U.Mal_nt__G1.Mal_nt_I.zA8 s L g am rd0).
Local Notation "§10§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§10§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§10§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§10§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Notation "§11§ h__" := (h__ s L g am i rho gd rd0 Hgd) (at level 10, h__ global).
Local Abbreviation zl1_1 := (§11§ U.Mal_nt__G1.Mal_nt_I.zl1_1).
Local Notation "§12§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation zr1_142 := (§12§ U.Mal_nt__G1.Mal_nt_I.zr1_142).
Local Abbreviation nQ_used := (§5§ U.Mal_nt__G1.Mal_nt_I.nQ_used).
Local Abbreviation pQ_used := (§5§ U.Mal_nt__G1.Mal_nt_I.pQ_used).
Local Abbreviation RN := (§5§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation RP := (§5§ U.Mal_nt__G1.Mal_nt_I.RP).
Local Notation "§13§ h__" := (h__ s L X U g am i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation zU_range := (§13§ U.Mal_nt__G1.Mal_nt_I.zU_range).
Local Abbreviation zB_range := (@U.Mal_nt__G1.Mal_nt_I.zB_range s L X U g am i gd vm rd0 wok0 HMI Hgd).
Local Abbreviation zA8_range := (@U.Mal_nt__G1.Mal_nt_I.zA8_range s L g am gd rd0 Hgd).
Local Abbreviation RH := (§5§ U.Mal_nt__G1.Mal_nt_I.RH).
Local Abbreviation ze_var := (§10§ U.Mal_nt__G1.Mal_nt_I.ze_var).
Local Abbreviation ze_lit := (§10§ U.Mal_nt__G1.Mal_nt_I.ze_lit).
Local Abbreviation ze_alu := (§10§ U.Mal_nt__G1.Mal_nt_I.ze_alu).
Local Abbreviation ze_aluw := (§10§ U.Mal_nt__G1.Mal_nt_I.ze_aluw).
Local Abbreviation ze_ext := (§10§ U.Mal_nt__G1.Mal_nt_I.ze_ext).
Local Abbreviation ze12 := (@U.Mal_nt__G1.Mal_nt_I.ze12 s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12).
Local Abbreviation ze133 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze133).
Local Abbreviation ze135 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze135).
Local Abbreviation ze141 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze141).
Local Notation "§14§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hgd) (at level 10, h__ global).
Local Abbreviation ze152 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze152).
Local Abbreviation ze116 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze116).
Local Abbreviation ze117 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze117).
Local Abbreviation ze118 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze118).
Local Abbreviation ze119 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze119).
Local Abbreviation ze160 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze160).
Local Abbreviation ze161 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze161).
Local Abbreviation ze162 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze162).
Local Abbreviation ze163 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze163).
Local Abbreviation ze151 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze151).
Local Abbreviation ze185 := (§14§ U.Mal_nt__G1.Mal_nt_I.ze185).
Local Abbreviation ze153 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze153).
Local Abbreviation ze155 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze155).
Local Abbreviation ze158 := (§11§ U.Mal_nt__G1.Mal_nt_I.ze158).
Local Abbreviation ze112 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze112).
Local Abbreviation ze113 := (§12§ U.Mal_nt__G1.Mal_nt_I.ze113).
Local Abbreviation bits_mod32 := (§5§ U.Mal_nt__G1.Mal_nt_I.bits_mod32).
Local Abbreviation ze_sc := (§12§ U.Mal_nt__G1.Mal_nt_I.ze_sc).
Local Abbreviation ze_last := (§12§ U.Mal_nt__G1.Mal_nt_I.ze_last).
Local Abbreviation mask_range := (§5§ U.Mal_nt__G1.Mal_nt_I.mask_range).
Local Abbreviation mask_bit_clear := (§3§ U.Mal_nt__G1.Mal_nt_I.mask_bit_clear).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S8bZ1000SdaQ40Sc1Vrho;PaA2A2M0A2S0S6aS90G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S8bS10fZ40SdaQ40Sc1Vrho;PfA2A2A2M0N60A2S8bS97S8eZ2Z28A2A1G0A2A2").
Local Abbreviation ZF_base := (@U.Mal_nt__G1.Mal_nt_I.ZF_base s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd HP12 Hsp Hdepth).
Local Abbreviation ZF_freeable := (§12§ U.Mal_nt__G1.Mal_nt_I.ZF_freeable).
Local Notation "§15§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation ze_tabidx := (§15§ U.Mal_nt__G1.Mal_nt_I.ze_tabidx).
Local Abbreviation ZF_sc48 := (§15§ U.Mal_nt__G1.Mal_nt_I.ZF_sc48).
Local Abbreviation ZF_all := (§12§ U.Mal_nt__G1.Mal_nt_I.ZF_all).
Local Abbreviation ZF_maplenN0 := (§12§ U.Mal_nt__G1.Mal_nt_I.ZF_maplenN0).
Local Abbreviation ZF_fmN0 := (§12§ U.Mal_nt__G1.Mal_nt_I.ZF_fmN0).
Local Abbreviation ZF_fm_ne_ft := (§15§ U.Mal_nt__G1.Mal_nt_I.ZF_fm_ne_ft).
Local Abbreviation links_both := (§5§ U.Mal_nt__G1.Mal_nt_I.links_both).
Local Abbreviation prev_ne_g := (§12§ U.Mal_nt__G1.Mal_nt_I.prev_ne_g).
Local Abbreviation nonhead_avail0 := (§13§ U.Mal_nt__G1.Mal_nt_I.nonhead_avail0).
Local Abbreviation nQ_eq := (@U.Mal_nt__G1.Mal_nt_I.nQ_eq g am).
Local Abbreviation pQ_eq := (@U.Mal_nt__G1.Mal_nt_I.pQ_eq g am).
Local Abbreviation zNx_eq := (§2§ U.Mal_nt__G1.Mal_nt_I.zNx_eq).
Local Abbreviation zPv_eq := (§2§ U.Mal_nt__G1.Mal_nt_I.zPv_eq).
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd9Q40A1S6cSd9Q8A1A1F_;Vrd0;S136S86VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd9Q40A1S70F_;Vwok0;S137S86VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S6aS1S8bZ0R1A2S8dR1Z60A2A2S0S6cSd9Q8A1M0A1VmV;SdbQ40S8cZ108ecR2A2A2A1S79G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S118S114Vrd0;Sd9Q40A1S72L_;A2S119S115A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S114S136S86VmV;A2S137S86VmV;A2A2").
Local Abbreviation HreprO := (@U.Mal_nt__G1.Mal_nt_Ib.HreprO s L X U g i vm rd0 wok0 HMI mV Erd Ewok).
Local Abbreviation grp_byte_rd := (@U.Mal_nt__G1.Mal_nt_Ic.grp_byte_rd s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd mV Erd Ewok).
Local Abbreviation mkey := (@U.Mal_nt__G1.Mal_nt_D.mkey).
Local Abbreviation kmemv := (@U.Mal_nt__G1.Mal_nt_D.kmemv).
Local Abbreviation kbitsv := (@U.Mal_nt__G1.Mal_nt_D.kbitsv).
Local Abbreviation kptr := (§8§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation krec := (§8§ U.Mal_nt__G1.Mal_nt_D.krec).
Local Abbreviation klo := (§9§ U.Mal_nt__G1.Mal_nt_D.klo).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (§6§ U.Mal_nt__G1.Mal_nt_D.fptr).
Local Abbreviation flo := (§7§ U.Mal_nt__G1.Mal_nt_D.flo).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Abbreviation dlo := (§9§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§9§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation useq_okb := (@U.Mal_nt__G1.Mal_nt_D.useq_okb).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S18dVL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Abbreviation klo_ptr := (§13§ U.Mal_nt__G1.Mal_nt_D.klo_ptr).
Local Notation "§16§ h__" := (h__ rho gd Hgd) (at level 10, h__ global).
Local Abbreviation useq_okb_cell := (§16§ U.Mal_nt__G1.Mal_nt_D.useq_okb_cell).
Local Abbreviation od_ok_at := (§10§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§10§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§8§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§9§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§9§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation od_pairwise := (§9§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S8bS117VL;A1S8cS149Vrho;A1S14aVrho;A1A2A2").
Local Abbreviation od_ok_guard := (§10§ U.Mal_nt__G2.Mal_nt_Z.od_ok_guard).
Local Abbreviation od_ok_fmh_entry := (§10§ U.Mal_nt__G2.Mal_nt_Z.od_ok_fmh_entry).
Local Abbreviation fmem_key := (§4§ U.Mal_nt__G2.Mal_nt_Z.fmem_key).
Local Abbreviation od_ok_fm_entry := (§12§ U.Mal_nt__G2.Mal_nt_Z.od_ok_fm_entry).
Local Abbreviation od_ok_ft_entry := (§12§ U.Mal_nt__G2.Mal_nt_Z.od_ok_ft_entry).
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S71S153A1S154OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1c0S86VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S10aVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1c5S86VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S10aS10aS10aVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1c7S86VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS10aS10aR3VTR;R3R2A2F_;VTR;S10bS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1c4S86VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S10aS10aS10aS10aS10bR4R1A1M0R6R2A1F_;Fw;S10bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1c1S86VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S10aS10aS10bR3R1A1VTR;S10bS0S10bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1c3S86VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S10aS10aS10aVTR;R3R1A2VTR;R3R2A2VTR;S10bS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1c2S86VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1baVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sa6VX;S6dS6eS8S6aA2S74S8S6aVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Local Notation "§17§ h__" := (h__ s L g am i rho gd rd0 mW) (at level 10, h__ global).
Local Abbreviation EVX := (§17§ U.Mal_nt__G2.Mal_nt_W.EVX).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sd9Q40M0A1Sc1Vrho;PdA2SdbG0Vi;A2A3").
Local Abbreviation bounded_of_delta := (§1§ U.Mal_nt__G2.Mal_nt_W.bounded_of_delta).
Local Abbreviation oStkF := (@U.Mal_nt__G2.Mal_nt_W.oStkF).
Local Abbreviation od_chg := (@U.Mal_nt__G2.Mal_nt_W.od_chg).
Local Notation "§18§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 HP13 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ sr Hzs) (at level 10, h__ global).
Local Abbreviation post_ok := (§18§ U.Mal_nt__G2.Mal_nt_W.post_ok).
Local Abbreviation post_ok_map := (§18§ U.Mal_nt__G2.Mal_nt_W.post_ok_map).
Local Abbreviation ze_E_fr := (§12§ U.Mal_nt__G2.Mal_nt_W.ze_E_fr).
Local Abbreviation xraw_or := (@U.Mal_nt__G2.Mal_nt_W.xraw_or s X g am i Hu).
Local Abbreviation leaf_regs_ok_sound := (§16§ U.Mal_nt__G2.Mal_nt_W.leaf_regs_ok_sound).
Local Abbreviation Hhp := (§13§ U.Mal_nt__G2.Mal_nt_W.Hhp).
Local Notation "§19§ h__" := (h__ s L g am i rho gd rd0 TR K TRR) (at level 10, h__ global).
Local Abbreviation segRm := (§19§ U.Mal_nt__G2.Mal_nt_V3.segRm).
Local Abbreviation leaf_factm := (@U.Mal_nt__G2.Mal_nt_V3.leaf_factm s L g am i rho gd rd0 K).
Local Abbreviation EVq := (§10§ U.Mal_nt__G2.Mal_nt_V3.EVq).
Local Abbreviation ZF_holdsm := (§10§ U.Mal_nt__G2.Mal_nt_V3.ZF_holdsm).
Local Abbreviation agreesV_of := (§17§ U.Mal_nt__G2.Mal_nt_V3.agreesV_of).
Local Abbreviation agrees_of_V := (§17§ U.Mal_nt__G2.Mal_nt_V3.agrees_of_V).
Local Abbreviation riding := (@U.Mal_nt__G2.Mal_nt_V3.riding s L g am i rho gd rd0 ms mW).
Local Abbreviation od_hold_m := (@U.Mal_nt__G2.Mal_nt_V3.od_hold_m s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ).
Local Abbreviation objs_matchb_refl' := (@U.Mal_nt__G2.Mal_nt_V3.objs_matchb_refl').
Local Abbreviation objs_matchb_refl := (@U.Mal_nt__G2.Mal_nt_V3.objs_matchb_refl).
Local Abbreviation objs_matchb_app := (@U.Mal_nt__G2.Mal_nt_V3.objs_matchb_app).
Local Abbreviation smatch_canon := (@U.Mal_nt__G2.Mal_nt_V3.smatch_canon).
Local Notation "§20§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp ms Hrom mW Hsp_high) (at level 10, h__ global).
Local Abbreviation carve_on := (§20§ U.Mal_nt__G2.Mal_nt_V3.carve_on).
Local Abbreviation E_len := (@U.Mal_nt__G2.Mal_nt_V3.E_len).
Local Abbreviation F_seq_ne := (@U.Mal_nt__G2.Mal_nt_V3.F_seq_ne).
Local Abbreviation F_seq_eq := (@U.Mal_nt__G2.Mal_nt_V3.F_seq_eq).
Local Abbreviation E_seq1 := (@U.Mal_nt__G2.Mal_nt_V3.E_seq1).
Local Abbreviation E_seq' := (@U.Mal_nt__G2.Mal_nt_V3.E_seq').
Local Abbreviation useq_cell_okb := (@U.Mal_nt__G2.Mal_nt_V3.useq_cell_okb).
Local Abbreviation t1_P2 := (@U.Mal_nt__G2.Mal_nt_V3.t1_P2).
Local Abbreviation t1_run_okb := (@U.Mal_nt__G2.Mal_nt_V3.t1_run_okb).
Local Abbreviation T1pack := (§16§ U.Mal_nt__G2.Mal_nt_V3.T1pack).
Local Abbreviation carve_back := (§20§ U.Mal_nt__G2.Mal_nt_V3.carve_back).
Local Abbreviation gl_pv := (@U.Mal_nt__G2.Mal_nt_V3.gl_pv).
Local Abbreviation gl_nv := (@U.Mal_nt__G2.Mal_nt_V3.gl_nv).
Local Abbreviation ds_live1 := (@U.Mal_nt__G2.Mal_nt_V3.ds_live1).
Local Abbreviation ds_new1 := (@U.Mal_nt__G2.Mal_nt_V3.ds_new1).
Local Abbreviation prefix_leaf_okb := (@U.Mal_nt__G2.Mal_nt_V3.prefix_leaf_okb).
Local Notation "§21§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HP13 mV Erd Ewok Hgd_holds mW sr HIr HP13w) (at level 10, h__ global).
Local Abbreviation pvnv_okb_sound := (§21§ U.Mal_nt__G2.Mal_nt_V3.pvnv_okb_sound).
Local Abbreviation prefix_link := (@U.Mal_nt__G2.Mal_nt_V3.prefix_link s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ Hsp_high K).
Local Abbreviation T1_seg := (@U.Mal_nt__G2.Mal_nt_V3.T1_seg s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp ms Hrom mW TR K TRR).
Local Abbreviation leaf_regs_map := (@U.Mal_nt__G2.Mal_nt_V3.leaf_regs_map).
Local Abbreviation leaf_regs_map_sound := (§16§ U.Mal_nt__G2.Mal_nt_V3.leaf_regs_map_sound).
Local Abbreviation ze_E_len := (§15§ U.Mal_nt__G2.Mal_nt_V3.ze_E_len).
Local Abbreviation leaf_okb := (@U.Mal_nt__G2.Mal_nt_V3.leaf_okb).
Local Abbreviation leaf_okb_sound := (§21§ U.Mal_nt__G2.Mal_nt_V3.leaf_okb_sound).
Local Abbreviation t2_run_okb := (@U.Mal_nt__G2.Mal_nt_V3.t2_run_okb).
Local Abbreviation T2_seg := (§19§ U.Mal_nt__G2.Mal_nt_V3.T2_seg).
Local Abbreviation keep_okb := (@U.Mal_nt__G2.Mal_nt_V3.keep_okb).
Local Abbreviation keep_okb_sound := (§21§ U.Mal_nt__G2.Mal_nt_V3.keep_okb_sound).
Local Abbreviation gkeep := (@U.Mal_nt__G2.Mal_nt_V3.gkeep).

Definition cx3 (t : astate) : ltac2:(tb__ "0|1|
S6eS6eS71S6aA1M0S6aA2G0A2") := ltac2:(tb__ "0|1|
S74S6eS71S6aA1M0S6aA2G0S74G0S6aS3bVt;A1S18Vt;A1A4S1fVt;A1A4").
Definition ot3 (t : astate) : ltac2:(tb__ "0|0|
S6eS6eS6eS6eS6eS71S6aA1S6aA2S71S8A1A2S71SdA1A2S6aA2S8A2") := ltac2:(tb__ "0|6|
S74S6eS6eS6eS6eS71S6aA1M0S6aA2M1S71S8A1M2A2M3S71SdA1M4A2M5S6aA2S8S74G5S6aS74G3G4S74G1G2S74G0S6aS48Vt;A1S2cVt;A1A4S29Vt;A1A4S2dVt;A1A4S2aVt;A1A4S2bVt;A1A4").
Lemma flds_upd q x t : ltac2:(tb__ "0|4|
S1S0S6eS6eS71S6aA1M0S6aA2M1G0A2S122S1b7Vq;Vx;Vt;A3M2A1S122Vt;A1A3S1S0S6eS6eS6eS6eG1S71S8A1A2S71SdA1A2S6aA2S8A2S121G2A1S121Vt;A1A3S1S0S71S6cS8A1M3A1S1dG2A1S1dVt;A1A3S0G3SfG2A1SfVt;A1A3A2A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma flds_set_hd c vv t : ltac2:(tb__ "0|3|
S1S0S6eS6eS71S6aA1M0S6aA2M1G0A2S122S11dVc;Vvv;Vt;A3M2A1S122Vt;A1A3S1S0S6eS6eS6eS6eG1S71S8A1A2S71SdA1A2S6aA2S8A2S121G2A1S121Vt;A1A3S0S6cS8A1SfG2A1SfVt;A1A3A2A2").
Proof using . repeat split; reflexivity. Qed.
Lemma flds_dq : ltac2:(tb__ "0|3|
S1S0S6eS6eS71S6aA1M0S6aA2M1G0A2S122S180Vs;Vg;Vam;A3M2A1S122Vs;A1A3S1S0S6eS6eS6eS6eG1S71S8A1A2S71SdA1A2S6aA2S8A2S121G2A1S121Vs;A1A3S0S6cS8A1SfG2A1SfVs;A1A3A2A2").
Proof using .
  unfold dq_post. destruct (am_next am) as [n|]; [|repeat split; reflexivity]. destruct (sptr_eqb n g); [repeat split; reflexivity|].
  destruct (am_prev am) as [p|]; [|repeat split; reflexivity]. destruct (osptr_eqb _ _); repeat split; reflexivity.
Qed.
Lemma flds_s1 : ltac2:(tb__ "0|3|
S1S0S6eS6eS71S6aA1M0S6aA2M1G0A2S122S181Vs;Vg;Vam;A3M2A1S122Vs;A1A3S1S0S6eS6eS6eS6eG1S71S8A1A2S71SdA1A2S6aA2S8A2S121G2A1S121Vs;A1A3S0S6cS8A1SfG2A1SfVs;A1A3A2A2").
Proof using .
  unfold fgm_s1, act_post. destruct (am_next am) as [n|]; [|apply flds_dq].
  destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s (am_sc am)) (Some g))%bool; [|apply flds_dq].
  destruct (MT (dq_post s g am) n) as [[| |an]|]; apply flds_dq.
Qed.
Lemma flds_fq t q : ltac2:(tb__ "0|1|
S1S0S6eS6eS6eS6eS6eS71S6aA1S6aA2S71S8A1A2S71SdA1A2S6aA2S8A2S121S188Vt;Vq;A2M0A1S121Vt;A1A3S0S71S6cS8A1A1S1dG0A1S1dVt;A1A3A2").
Proof using .
  unfold fq_post. destruct (st_free_meta_head t) as [fm|]; [|split; reflexivity].
  destruct (MT t fm) as [xf|]; [|split; reflexivity]. destruct (fst (links_of xf)) as [hp|]; split; reflexivity.
Qed.
Lemma flds_s5 : ltac2:(tb__ "0|8|
S1S0S6eS6eS71S6aA1M0S6aA2M1G0A2S122S182Vs;Vg;Vam;A3M2A1S74G1G0S74G0S6aS2eSdcVam;A1M3S92S21Vs;G3A2S8cScVam;A1Z1A2A2S3bVs;A1A3S18S187Vs;A1M4A1M5A4S6cS6aA1G0Lx;S31G3A1S6aS2eR1G5S1fG4A1M6A3Lk;G6X6cx2A4A3S1S0S6eS6eS6eS6eG1S71S8A1A2S71SdA1A2S6aA2S8A2S121G2A1S121Vs;A1A3S1S0S71S6cS8A1M7A1S1dG2A1S1dS181Vs;Vg;Vam;A3A1A3S0G7SfG2A1SfVs;A1A3A2A2A2").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds mW.
  pose proof flds_s1 as (C1 & O1 & H1). unfold cx3, ot3 in *.
  unfold fgm_s5, fgm_s4, fgm_s3, fgm_s2. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. unfold seq_post.
  remember (fgm_s1 s g am) as t1 eqn:Et1. clear Et1.
  injection C1 as E1 E2 E3. injection O1 as E4 E5 E6 E7 E8 E9.
  destruct t1. cbn in *. subst.
  destruct (bounce_idx (am_sc am)); destruct (st_seq s =? 255); cbn; repeat split; reflexivity.
Qed.
Lemma active_s1_other c : ltac2:(tb__ "0|0|
S8bZ0Vc;A2S2S0S6aVc;SdcVam;A1A3A1S0S6cS8A1S9eS181Vs;Vg;Vam;A3Vc;A2S9eVs;Vc;A2A3F_;F_;").
Proof using HMI Hgd Hsp Hu.
  intros Hc Hne. unfold fgm_s1, act_post, dq_post. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Hne.
  assert (SC : 0 <= am_sc am) by (pose proof R_all as R; lia).
  destruct (am_next am) as [n|]; [|reflexivity].
  destruct (sptr_eqb n g) eqn:Eng; cbn [negb andb].
  - rewrite active_hd_upd_meta. apply active_hd_set_hd_other; lia.
  - destruct (am_prev am) as [p|].
    + destruct (osptr_eqb (active_hd s (am_sc am)) (Some g)) eqn:Ehd.
      * destruct (MT _ n) as [[| |an]|]; rewrite ?active_hd_upd_meta; (rewrite active_hd_set_hd_other by lia); rewrite !active_hd_upd_meta; reflexivity.
      * rewrite !active_hd_upd_meta. reflexivity.
    + destruct (osptr_eqb (active_hd s (am_sc am)) (Some g)); [destruct (MT s n) as [[| |an]|]; rewrite ?active_hd_upd_meta; reflexivity | reflexivity].
Qed.

Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : mW = rm rho.
Hypothesis Evm : vm = m_vmmaps md.
Hypothesis HKc : ltac2:(tb__ "0|1|
S71S153A1M0S154VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S154R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
Sc0S86Vrho;S18fS18aA1S74S71S153A1S17eVtr;S17fVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S6aS8bZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S6eS6cS8A1M0G0A2S74G0G0S13Vam;A1SbVam;A1A4S74G0G0S79S8A1M1G1A4A3A1S2S0G0S9eVs;SeVam;A1A2S6dS8Vg;A2A3A1S2S0S6aS17Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S6aS8cSebVam;A1S1eVi;A1A2S19ScVam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Hypothesis Hml : am_maplen am <> 0.

Lemma ND_s3 : List.NoDup (keys s). Proof using HMI. exact (proj1 (inv_keys HI)). Qed.
Lemma Hsc48' : 0 <= am_sc am < 48. Proof using Hsc48. exact Hsc48. Qed.
Lemma nmask_mask3 : ltac2:(tb__ "0|0|
S0S6aS183Vam;A1SebVam;A1A3"). Proof using . unfold nmask. apply Z.lor_comm. Qed.
Lemma LenA3 : length (st_active s) = 48%nat. Proof using HMI. exact (proj1 (inv_ctx HI)). Qed.

Lemma mask_bits j : ltac2:(tb__ "0|0|
S1S8bZ0Vj;A2S8bVj;ScVam;A1A2A2S2S0S6aVj;Vi;A3A1S0S70S9bSebVam;A1Vj;A2S72A3F_;F_;").
Proof using HMI Hall Hgd Hml Hsc48 Hsp Hu.
  intros Hj Hji. pose proof R_all as R. pose proof mask_range as MR. pose proof Hall as HA. unfold bit in HA.
  pose proof (lor_add_disjoint_bit mask i ltac:(lia) ltac:(lia) mask_bit_clear) as LA. rewrite LA in HA. clear LA.
  apply (f_equal (fun z => Z.testbit z j)) in HA. rewrite Z.lor_spec, (Z.pow2_bits_false i j) in HA by lia.
  rewrite Bool.orb_false_r in HA. rewrite HA. rewrite testbit_ones by lia.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.

Lemma Hfr0 : ltac2:(tb__ "0|0|
S6aS0S6cS1bA1S28S26Vam;R1A2A1S79S1bA1A3Fj;").
Proof using HMI Hall Hgd Hml Hsc48 Hsp Hu.
  intros j. pose proof Hres as (Ri & Hfr & _). pose proof G as (Gm & _ & Gsl & _). pose proof R_all as R.
  pose proof Gm as (Glast & _ & Len & _).
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length (am_slots am))) as [LT|GE].
  2:{ unfold nth_slot. rewrite nth_overflow by exact GE. reflexivity. }
  rewrite Len in LT. set (j' := Z.of_nat (Z.to_nat j)). assert (Hj' : 0 <= j' <= am_last am) by (unfold j'; lia).
  replace (nth_slot am j) with (nth_slot am j') by (unfold nth_slot, j'; rewrite Nat2Z.id; reflexivity).
  destruct (Z.eq_dec j' i) as [E|NE]; [rewrite E; exact Hfr|].
  pose proof (Gsl j' Hj') as SL. unfold slot_ok in SL. destruct SL as (_ & _ & SL).
  destruct (ss_fr (nth_slot am j')) as [fr|]; [|reflexivity]. exfalso. destruct SL as (AL & _).
  unfold allocated in AL. pose proof (mask_bits j' Hj' NE) as TB. unfold U.Mal_nt__G1.Mal_nt_I.mask in TB.
  rewrite TB in AL. discriminate AL.
Qed.

Lemma next_facts n : ltac2:(tb__ "0|3|
S0S6cS8A1M0SbVam;A1S6dS8Vn;A2A3S2S0S8Vn;Vg;A3A1S3S8S8S3SaSaS3SaSaS1S0G0S13Vam;A1S6dS8R3A2A3S1S2S0S8R3Vg;A3A1S1Sa1VX;Vs;R3R2A4S1Sa1VX;Vs;Vn;R1A4S1S0S6aSeR1A1SdcVam;A1M1A3S1S0S6aSeR2A1G1A3S1S0S6cS9A1M2S9dVs;R3A2S6dS9S10R2A1A2A3S1S0G2S9dVs;Vn;A2S6dS9S10R1A1A2A3S1S0S8SdfVg;Vam;A2Vn;A3S1S0S8Se0Vg;Vam;A2R3A3S1S0SaSe5Vs;Vg;Vam;A3R1A3S0SaSeaVs;Vg;Vam;A3R2A3A2A2A2A2A2A2A2A2A2A2A2Lan;A2Lap;A2Lp;A2F_;F_;").
Proof using HMI Hgd Hu rho.
  intros En Hng. destruct (prev_ne_g n En Hng) as (p & Ep & Hpg).
  destruct (linked_ring ltac:(right; rewrite En; discriminate)) as (c & m0 & rest & Hc & Ec & Hhd & Rg & Hin).
  pose proof (ring_step X s c m0 rest g Rg Hin) as (_ & Hn & Hp).
  unfold mnext, mprev, mrec in Hn, Hp. rewrite HMg_inst in Hn, Hp. rewrite En in Hn. rewrite Ep in Hp.
  destruct (ring_members_used _ _ _ _ _ _ Rg Hn) as (an & Hun & Scn). destruct (ring_members_used _ _ _ _ _ _ Rg Hp) as (ap & Hup & Scp).
  exists p, ap, an. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite Ec.
  repeat split; try assumption.
  - exact (proj1 (usedX_MT _ _ _ _ Hup)).
  - exact (proj1 (usedX_MT _ _ _ _ Hun)).
  - exact (nQ_eq n En).
  - exact (pQ_eq p Ep).
  - unfold anQ, U.Mal_nt__G1.Mal_nt_I.anQ. rewrite (nQ_eq n En). unfold mrec. rewrite (proj1 (usedX_MT _ _ _ _ Hun)). reflexivity.
  - unfold apQ, U.Mal_nt__G1.Mal_nt_I.apQ. rewrite (pQ_eq p Ep). unfold mrec. rewrite (proj1 (usedX_MT _ _ _ _ Hup)). reflexivity.
Qed.
Lemma HnU3 : ltac2:(tb__ "0|0|
S8S0S6cS8A1SbVam;A1S6dS8R1A2A3S3SaSaS0S6cS9A1S9dVs;R3A2S6dS9S10R1A1A2A3Lan;A2F_;Fn;").
Proof using HMI Hgd Hu. intros n En. destruct (next_used n En) as [an Hn]. exists an. exact (proj1 (usedX_MT _ _ _ _ Hn)). Qed.
Lemma HpU3 : ltac2:(tb__ "0|0|
S8S0S6cS8A1S13Vam;A1S6dS8R1A2A3S3SaSaS0S6cS9A1S9dVs;R3A2S6dS9S10R1A1A2A3Lap;A2F_;Fp;").
Proof using HMI Hgd Hu. intros p Ep. destruct (prev_used p Ep) as [ap Hp]. exists ap. exact (proj1 (usedX_MT _ _ _ _ Hp)). Qed.
Lemma Hlinks3 : ltac2:(tb__ "0|2|
S8S0S6cS8A1M0SbVam;A1S6dS8R1A2A3S2S0S8R2Vg;A3A1S3S8S8S3S9S9S3S9S9S1S0G0S13Vam;A1S6dS8R3A2A3S1S2S0S8R3Vg;A3A1S1S0S6cS9A1M1S9dVs;R3A2S6dS9R2A2A3S0G1S9dS1b7R3S49R2S7bG0G0S43R2A1A3S6dS8R6A2A3Vs;A3R6A2S6dS9R1A2A3A2A2A2Lxn;A2Lxp;A2Lp;A2F_;F_;Fn;").
Proof using HMI Hgd Hu rho.
  intros n En Hng. destruct (next_facts n En Hng) as (p & ap & an & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & _).
  exists p, (MUsed ap). destruct (sptr_eq_dec n p) as [->|NE].
  - eexists. split; [exact Ep|]. split; [exact Hpg|]. split; [exact Mp|]. apply MT_upd_same.
  - exists (MUsed an). split; [exact Ep|]. split; [exact Hpg|]. split; [exact Mp|]. rewrite (MT_upd_other p _ _ n NE). exact Mn.
Qed.
Lemma HactU3 : ltac2:(tb__ "0|1|
S8S0S6cS8A1M0SbVam;A1S6dS8R1A2A3S2S0S8R2Vg;A3A1S0G0S9eVs;SdcVam;A1A2S6dS8Vg;A2A3S3SaSaS0S6cS9A1S9dS180Vs;Vg;Vam;A3R5A2S6dS9S10R1A1A2A3Lan;A2F_;F_;F_;Fn;").
Proof using HMI Hgd Hu rho.
  intros n En Hng _. destruct (next_facts n En Hng) as (p & ap & an & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & _).
  eexists. apply (MT_dq_n s g am p n ap an Ep En Hng Mp Mn).
Qed.
Lemma Hact3 : ltac2:(tb__ "0|1|
S8SaS0S6cS8A1M0SbVam;A1S6dS8R2A2A3S2S0S8R3Vg;A3A1S0G0S9eVs;SdcVam;A1A2S6dS8Vg;A2A3S0S6cS9A1S9dS180Vs;Vg;Vam;A3R5A2S6dS9S10R4A1A2A3S0S6aS22R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
Proof using HMI Hgd Hsc48 Hu rho.
  intros n an' En Hng Hhd M'. destruct (next_facts n En Hng) as (p & ap & an & Ep & Hpg & Hup & Hun & Scn & _ & Mp & Mn & _).
  rewrite (MT_dq_n s g am p n ap an Ep En Hng Mp Mn) in M'. injection M' as <-.
  cbn [am_avail am_set_links].
  assert (AV : am_avail an = 0).
  { apply (nonhead_avail0 n an Hun Scn Hsc48). rewrite Hhd. intros E. injection E as E. exact (Hng (eq_sym E)). }
  unfold an1. destruct (sptr_eqb n p) eqn:Enp; [|exact AV].
  apply sptr_eqb_eq in Enp. subst p. rewrite Mn in Mp. injection Mp as ->. exact AV.
Qed.
Lemma Hfree_ring3 : ltac2:(tb__ "0|2|
S8S0S6cS8A1M0SfVs;A1S6dS8R1A2A3S1S2S0S8R2Vg;A3A1S3S8S8S3G0G0S3G0G0S3G0G0S1S0S6cS9A1M1S9dVs;R6A2S6dS9S12S6dS8R4A2R3A2A2A3S1S2S0S8R4Vg;A3A1S0G1S9dVs;R4A2S6dS9S12R2R1A2A2A3A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;").
Proof using HMI Hu.
  intros fm Hfh. destruct fmL_cases as [(E & _) | (fm' & pr & nx & E & _ & Hfm & M & _ & Hpr & _ & _ & pr2 & nx2 & M2 & _)]; [rewrite E in Hfh; discriminate|].
  rewrite E in Hfh. injection Hfh as <-.
  destruct (fmem_facts fm' Hfm) as (_ & _ & _ & _ & _ & _ & NEf & _). destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & _ & NEp & _).
  split; [exact NEf|]. exists pr, (Some nx), (Some pr2), (Some nx2). split; [exact M|]. split; [exact NEp | exact M2].
Qed.
Lemma Hfree_ringX3 : ltac2:(tb__ "0|2|
S8S0S6cS8A1M0SfVs;A1S6dS8R1A2A3S1S2S0S8R2Vg;A3A1S3S8S8S3G0G0S3G0G0S3G0G0S1S0S6cS9A1M1S9dVs;R6A2S6dS9S12S6dS8R4A2R3A2A2A3S1S2S0S8R4Vg;A3A1S1S0G1S9dVs;R4A2S6dS9S12R2R1A2A2A3S0S70Sb8R4VX;A2S77A3A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2A2F_;Ffm;").
Proof using HMI Hu.
  intros fm Hfh. destruct fmL_cases as [(E & _) | (fm' & pr & nx & E & _ & Hfm & M & _ & Hpr & _ & _ & pr2 & nx2 & M2 & _)]; [rewrite E in Hfh; discriminate|].
  rewrite E in Hfh. injection Hfh as <-.
  destruct (fmem_facts fm' Hfm) as (_ & _ & _ & _ & _ & _ & NEf & _). destruct (fmem_facts pr Hpr) as (_ & _ & _ & _ & _ & _ & NEp & Xp).
  split; [exact NEf|]. exists pr, (Some nx), (Some pr2), (Some nx2). split; [exact M|]. split; [exact NEp|]. split; [exact M2 | exact Xp].
Qed.
Lemma mapped3 : ltac2:(tb__ "0|0|
S3S73S73S3SdSdS1S0S8S16Vam;A1S3eR2Z0A2A3S1S0S6cSdA1SacVs;R2A2S6dSdR1A2A3S1S0S38S35R1A1S2fA3S1S0S70S37R1A1S72A3S0S6aS36R1A1S8fS14Vam;A1S3dA2A3A2A2A2A2Lrg;A2Lr;A2").
Proof using HMI Hgd Hml Hsc48 Hu rho.
  pose proof G as (_ & Hml0 & _ & _ & Gmp & _). destruct (Gmp ltac:(lia)) as (r & rg & Em & Hr & Hk & Hl & Hlen & _).
  exists r, rg. auto.
Qed.
Lemma len_range3 : ltac2:(tb__ "0|1|
S1S8dZ0S8fZ1000S14Vam;A1A2M0A2S8dG0S8eZ2Z40A2A2A2"). Proof using HMI Hgd Hml Hsc48 Hsp Hu. pose proof G as (_ & Hml0 & _). pose proof maplen_range. lia. Qed.

Definition X_sz : sv := ltac2:(tb__ "0|0|
SbeS1a5Sc3S77Q10Sc7P1SbeS1a5S171SbdZ1A1A3Z2A3A3SbdZ4A1A3").
Definition X_stA : sv := ltac2:(tb__ "0|0|
SbeS1a5Sc3S77Q10Sc7P1SbeS1a6SbeS1aaSd8P87A1SbdZ5A1A3SbdZ7eA1A3Z2A3A3SbdZ4A1A3").
Definition X_stB : sv := ltac2:(tb__ "0|0|
SbeS1a4SbeS1a6Sd8P87A1SbdZfffffffffffff000A1A3SbdN10A1A3").
Definition X_bnc : sv := SExt false 8 (v 185).
Definition X_9cnt : sv := ltac2:(tb__ "0|0|
SbeS1a4SbeS1a4SbeS1a5S173SbdZ3A1A3S173A3SbdZ9A1A3").
Definition F_stA_lt : sprop := ltac2:(tb__ "0|0|
Sc5S1a7S12bS123A3").
Definition F_stB_lt : sprop := ltac2:(tb__ "0|0|
Sc5S1a7S12cS123A3").
Definition F_last0 : sprop := ltac2:(tb__ "0|0|
Sc4Sc5S1a8S173SbdZ0A1A3A1").
Definition F_bnc_lt : sprop := SPBranch BC_LTU X_bnc (SLit 100).
Definition F_us_lt : sprop := SPBranch BC_LTU (v 151) X_9cnt.
Definition F_us_lt0 : sprop := SPBranch BC_LTU (v 151) (SLit 9).
Definition F_18_lt : sprop := SPBranch BC_LTU (SLit 18) nt_last.
Lemma ze_u16 (x : sv) : ltac2:(tb__ "0|4|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vx;A3S8fZ2M2SdcVam;A1M3A2A3S0S6aS10cG0G1Sc3S77Q10Sc7P1Vx;G2A3A3A3S4aG3S46A2A3F_;").
Proof using Hgd Hsc48 Hsp.
  intros Ex. rewrite ze_ext. cbn [Z.of_N]. change (zeval zr1 zl1 (SLBytes 1 x 2)) with ((zle (zsublist (zeval zr1 zl1 x) 2 (zl1 1%positive))) mod 2 ^ 64).
  rewrite Ex, zl1_1. pose proof Hsc48' as SC. rewrite table_u16 by (unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia). pose proof (znth_size_classes_range (am_sc am) SC).
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_sz : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S123A3S23SdcVam;A1A1A3").
Proof using HMI Hgd Hsc48 Hsp Hu.
  unfold X_sz. rewrite ze_alu, ze_lit. rewrite (ze_u16 (SAlu ALU_SLL nt_sc (SLit 1))).
  2:{ rewrite ze_alu, ze_sc, ze_lit. cbn [zalu]. change ((1 mod 2 ^ 64) mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia. pose proof Hsc48' as SC. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite Z.mod_small; lia. }
  cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia. pose proof (znth_size_classes_range (am_sc am) Hsc48').
  unfold class_size, UNIT, sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_stA : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S12bA3S23SdcVam;A1A1A3").
Proof using HMI Hgd Hsc48 Hsp Hu.
  unfold X_stA. rewrite ze_alu, ze_lit, (ze_u16 _ (ze_tabidx Hsc48)). cbn [zalu]. change ((4 mod 2 ^ 64) mod 64) with 4. rewrite Z.shiftl_mul_pow2 by lia.
  pose proof (znth_size_classes_range (am_sc am) Hsc48'). unfold class_size, UNIT, sc, U.Mal_nt__G1.Mal_nt_I.sc. rewrite !Z.mod_small; lia.
Qed.
Lemma ze_stB : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S12cA3S92S8fS14Vam;A1Z1000A2Z10A2A3").
Proof using HMI Hgd Hml Hsc48 Hsp Hu.
  unfold X_stB. rewrite !ze_alu, ze135, !ze_lit. cbn [zalu]. pose proof bits_range as B. pose proof bits_mod32 as (_ & M2 & _). pose proof maplen_range as MR.
  rewrite !(Z.mod_small bits) by lia. change ((18446744073709547520 mod 2 ^ 64) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 12).
  rewrite (land_high_mask bits 12) by lia. change (2 ^ 12) with 4096. pose proof (Z.div_mod bits 4096 ltac:(lia)). pose proof (Z.mod_pos_bound bits 4096 ltac:(lia)).
  assert (NZ : 1 <= am_maplen am) by (pose proof Hml; lia).
  change ((-16) mod 2 ^ 64) with (2 ^ 64 - 16).
  replace (bits - bits mod 4096 + (2 ^ 64 - 16)) with ((am_maplen am * 4096 - 16) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ze_bnc : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S12eA3Sf2Vs;Vam;A2A3").
Proof using HMI Hgd Hsc48. unfold X_bnc. rewrite ze_ext, ze185. change (Z.of_N 8) with 8. pose proof zB_range. apply Z.mod_small. lia. Qed.
Lemma ze_9cnt : ltac2:(tb__ "0|1|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S12dA3S8cS8fZ9M0ScVam;A1A2G0A2A3").
Proof using HMI Hgd Hml Hsc48 Hsp Hu.
  unfold X_9cnt. rewrite !ze_alu, !ze_last, !ze_lit. cbn [zalu]. change ((3 mod 2 ^ 64) mod 64) with 3. change (9 mod 2 ^ 64) with 9. rewrite Z.shiftl_mul_pow2 by lia. pose proof R_all as R.
  rewrite !Z.mod_small; lia.
Qed.

Lemma ok_free_unfold : ltac2:(tb__ "0|2|
S0S6cS8A1SbVam;A1S6dS8Vg;A2A3S1S8bZ7SdcVam;A1M0A2S8dG0Z27A2A2S0S70S1cVs;Vg;Vam;A3S7aS7aS96S20Vam;A1S23G0A1A2S7fS95Z64Sf2Vs;Vam;A2A2A1A2S76S95S8fZ9S8cScVam;A1Z1A2M1A2Sf4Vs;Vam;A2A2S96G1Z14A2A2A2A3F_;F_;").
Proof using Hgd Hml Hsc48 rho.
  intros En Hr. unfold okay_to_free. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. pose proof Hsc48' as SC.
  replace (48 <=? am_sc am) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
  destruct (stride_of am <? class_size (am_sc am)); [reflexivity|]. cbn [orb].
  replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). rewrite En. cbn [osptr_eqb negb]. rewrite sptr_eqb_refl. cbn [negb].
  unfold is_bouncing, bounce_idx. replace ((7 <=? am_sc am) && (am_sc am <? 39))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold zB, U.Mal_nt__G1.Mal_nt_I.zB, zU, U.Mal_nt__G1.Mal_nt_I.zU, sc, U.Mal_nt__G1.Mal_nt_I.sc. destruct (100 <=? znth (am_sc am - 7) (st_bounces s)); reflexivity.
Qed.
Lemma stride_last : ltac2:(tb__ "0|0|
S2S0S6aScVam;A1Z0A3A1S0S6aS20Vam;A1S23SdcVam;A1A1A3F_;").
Proof using . intros Hl. unfold stride_of. replace (am_last am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl). reflexivity. Qed.
Lemma stride_last0 : ltac2:(tb__ "0|0|
S0S6aScVam;A1Z0A3S0S6aS20Vam;A1S92S8fS14Vam;A1Z1000A2Z10A2A3F_;").
Proof using Hml. intros Hl. unfold stride_of. rewrite Hl. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). reflexivity. Qed.

Definition hasf (Lf : sstate) (p : sprop) : bool := ltac2:(tb__ "0|0|
S84SbcSd6Vp;A1Sd7VLf;A1A3").
Definition free_reason_okb (Lf : sstate) : bool := ltac2:(tb__ "0|1|
S7aS7aS7aS7aS120VLf;S127A2S76S120VLf;S128A2S120VLf;S126A2M0A2A2S120VLf;S125A2A2S76S120VLf;Sc4S129A1A2S120VLf;Sc4S124A1A2A2A2S76S120VLf;Sc4S12aA1A2G0A2A2").
Definition keep_reason_okb (Lf : sstate) : bool := ltac2:(tb__ "0|1|
S76S76S120VLf;Sc4S125A1A2S7aS76S120VLf;Sc4S127A1A2S120VLf;Sc5S1a8S173SbdZ0A1A3A2A2S76S120VLf;Sc4S128A1A2S120VLf;S126A2M0A2A2A2S7aS7aS120VLf;S129A2S120VLf;S124A2A2S76S120VLf;S12aA2G0A2A2A2").
Lemma hasf_zholds m rhoX Lf w p : ltac2:(tb__ "0|0|
S0S70S120VLf;Vp;A2S72A3S0S70S1a1S11fVp;A2S72A3S0S70S10eVp;A1S72A3S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S159S86VK;VLf;VrhoX;Vw;A5S10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vp;A3F_;F_;F_;F_;F_;").
Proof using .
  intros H Hv Hs Hag HSP. unfold hasf in H. apply existsb_exists in H as (q & Hq & E). apply sprop_eqb_sound in E. subst q.
  exact (leaf_factm m rhoX Lf w p Hag HSP Hq Hv Hs).
Qed.
Section Bouncing.
Hypothesis Hng : ltac2:(tb__ "0|0|
S0S6cS8A1SbVam;A1S6dS8Vg;A2A3").
Hypothesis Hbr : 7 <= sc < 39.
Lemma free_reason_sound m rhoX Lf w : ltac2:(tb__ "0|0|
S0S70S12fVLf;A1S72A3S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S159S86VK;VLf;VrhoX;Vw;A5S0S70S1cVs;Vg;Vam;A3S72A3F_;F_;F_;").
Proof using HMI Hbr Hgd Hml Hng Hsc48 Hsp Hu.
  intros H Hag HSP. pose proof R_all as R. pose proof zB_range as ZB. pose proof zU_range as ZU. pose proof (znth_size_classes_range (am_sc am) Hsc48') as SZ. pose proof maplen_range as MR.
  assert (HZF : forall p, hasf Lf p = true -> sprop_vars_all below200 p = true -> psupported p = true -> zholds zr1 zl1 p) by (intros p Hp Hv Hs; exact (hasf_zholds m rhoX Lf w p Hp Hv Hs Hag HSP)).
  rewrite (ok_free_unfold Hng Hbr). unfold free_reason_okb in H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]).
  -
    pose proof (HZF _ H eq_refl eq_refl) as Z1. cbn [zholds zcond] in Z1. unfold F_stA_lt in Z1. cbn [zholds zcond] in Z1. rewrite ze_stA, ze_sz in Z1. apply Z.ltb_lt in Z1. lia.
  - apply andb_prop in H as [H1 H2]. pose proof (HZF _ H1 eq_refl eq_refl) as Z1. pose proof (HZF _ H2 eq_refl eq_refl) as Z2.
    unfold F_stB_lt, F_last0 in *. cbn [zholds zcond] in Z1, Z2. rewrite ze_stB, ze_sz in Z1. rewrite ze_last, ze_lit in Z2. change (0 mod 2 ^ 64) with 0 in Z2.
    apply Z.ltb_lt in Z1. assert (L0 : am_last am = 0) by (destruct (Z.eq_dec (am_last am) 0) as [E|NE]; [exact E | exfalso; apply Z2; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE]).
    rewrite (stride_last0 L0). replace (am_maplen am * 4096 - 16 <? class_size sc) with true by (symmetry; apply Z.ltb_lt; exact Z1). reflexivity.
  - pose proof (HZF _ H eq_refl eq_refl) as Z1. unfold F_bnc_lt in Z1. cbn [zholds zcond] in Z1. rewrite ze_bnc, ze_lit in Z1. change (100 mod 2 ^ 64) with 100 in Z1. apply Z.ltb_lt in Z1.
    replace (100 <=? zB) with false by (symmetry; apply Z.leb_gt; lia). destruct (stride_of am <? class_size sc); reflexivity.
  - apply andb_prop in H as [H1 H2]. pose proof (HZF _ H1 eq_refl eq_refl) as Z1. pose proof (HZF _ H2 eq_refl eq_refl) as Z2.
    unfold F_us_lt, F_18_lt in *. cbn [zholds zcond] in Z1, Z2. rewrite ze151, ze_9cnt in Z1. rewrite ze_lit, ze_last in Z2. change (18 mod 2 ^ 64) with 18 in Z2.
    assert (A1 : 9 * (am_last am + 1) <= zU) by (destruct (zU <? 9 * am_last am + 9) eqn:E; [exfalso; apply Z1; reflexivity | apply Z.ltb_ge in E; lia]).
    assert (A2 : am_last am + 1 < 20) by (destruct (18 <? am_last am) eqn:E; [exfalso; apply Z2; reflexivity | apply Z.ltb_ge in E; lia]).
    replace (9 * (am_last am + 1) <=? zU) with true by (symmetry; apply Z.leb_le; exact A1). replace (am_last am + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; exact A2).
    destruct (stride_of am <? class_size sc), (100 <=? zB); reflexivity.
  - apply andb_prop in H as [H1 H2]. pose proof (HZF _ H1 eq_refl eq_refl) as Z1. pose proof (HZF _ H2 eq_refl eq_refl) as Z2.
    unfold F_us_lt0, F_last0 in *. cbn [zholds zcond] in Z1, Z2. rewrite ze151, ze_lit in Z1. change (9 mod 2 ^ 64) with 9 in Z1. rewrite ze_last, ze_lit in Z2. change (0 mod 2 ^ 64) with 0 in Z2.
    assert (L0 : am_last am = 0) by (destruct (Z.eq_dec (am_last am) 0) as [E|NE]; [exact E | exfalso; apply Z2; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE]).
    assert (A1 : 9 <= zU) by (destruct (zU <? 9) eqn:E; [exfalso; apply Z1; reflexivity | apply Z.ltb_ge in E; lia]).
    rewrite L0. replace (9 * (0 + 1) <=? zU) with true by (symmetry; apply Z.leb_le; lia). cbn. destruct (stride_of am <? class_size sc), (100 <=? zB); reflexivity.
Qed.
Lemma keep_reason_sound m rhoX Lf w : ltac2:(tb__ "0|0|
S0S70S130VLf;A1S72A3S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S159S86VK;VLf;VrhoX;Vw;A5S0S70S1cVs;Vg;Vam;A3S77A3F_;F_;F_;").
Proof using HMI Hbr Hgd Hml Hng Hsc48 Hsp Hu.
  intros H Hag HSP. pose proof R_all as R. pose proof zB_range as ZB. pose proof zU_range as ZU. pose proof (znth_size_classes_range (am_sc am) Hsc48') as SZ. pose proof maplen_range as MR.
  assert (HZF : forall p, hasf Lf p = true -> sprop_vars_all below200 p = true -> psupported p = true -> zholds zr1 zl1 p) by (intros p Hp Hv Hs; exact (hasf_zholds m rhoX Lf w p Hp Hv Hs Hag HSP)).
  rewrite (ok_free_unfold Hng Hbr). unfold keep_reason_okb in H.
  apply andb_prop in H as [H HUS]. apply andb_prop in H as [HB HS].

  pose proof (HZF _ HB eq_refl eq_refl) as ZBn. unfold F_bnc_lt in ZBn. cbn [zholds zcond] in ZBn. rewrite ze_bnc, ze_lit in ZBn. change (100 mod 2 ^ 64) with 100 in ZBn.
  assert (B1 : 100 <= zB) by (destruct (zB <? 100) eqn:E; [exfalso; apply ZBn; reflexivity | apply Z.ltb_ge in E; lia]).
  replace (100 <=? zB) with true by (symmetry; apply Z.leb_le; exact B1). cbn [negb orb].

  assert (ST : (stride_of am <? class_size sc) = false).
  { apply Bool.orb_prop in HS. destruct HS as [HS|HS]; apply andb_prop in HS as [H1 H2]; pose proof (HZF _ H1 eq_refl eq_refl) as Z1; pose proof (HZF _ H2 eq_refl eq_refl) as Z2.
    - unfold F_stA_lt in Z1. cbn [zholds zcond] in Z1, Z2. rewrite ze_last, ze_lit in Z2. change (0 mod 2 ^ 64) with 0 in Z2. apply Bool.negb_true_iff in Z2. apply Z.eqb_neq in Z2.
      rewrite (stride_last Z2). apply Z.ltb_ge. lia.
    - unfold F_stB_lt, F_last0 in *. cbn [zholds zcond] in Z1, Z2. rewrite ze_stB, ze_sz in Z1. rewrite ze_last, ze_lit in Z2. change (0 mod 2 ^ 64) with 0 in Z2.
      assert (L0 : am_last am = 0) by (destruct (Z.eq_dec (am_last am) 0) as [E|NE]; [exact E | exfalso; apply Z2; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE]).
      rewrite (stride_last0 L0). destruct (am_maplen am * 4096 - 16 <? class_size sc) eqn:E; [exfalso; apply Z1; reflexivity | reflexivity]. }
  rewrite ST. cbn [orb].

  repeat (apply Bool.orb_prop in HUS; destruct HUS as [HUS|HUS]).
  - pose proof (HZF _ HUS eq_refl eq_refl) as Z1. unfold F_us_lt in Z1. cbn [zholds zcond] in Z1. rewrite ze151, ze_9cnt in Z1. apply Z.ltb_lt in Z1.
    replace (9 * (am_last am + 1) <=? zU) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - pose proof (HZF _ HUS eq_refl eq_refl) as Z1. unfold F_18_lt in Z1. cbn [zholds zcond] in Z1. rewrite ze_lit, ze_last in Z1. change (18 mod 2 ^ 64) with 18 in Z1. apply Z.ltb_lt in Z1.
    replace (am_last am + 1 <? 20) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r.
  - apply andb_prop in HUS as [H1 H2]. pose proof (HZF _ H1 eq_refl eq_refl) as Z1. pose proof (HZF _ H2 eq_refl eq_refl) as Z2.
    unfold F_us_lt0, F_last0 in *. cbn [zholds zcond] in Z1, Z2. rewrite ze151, ze_lit in Z1. change (9 mod 2 ^ 64) with 9 in Z1. apply Z.ltb_lt in Z1.
    rewrite ze_last, ze_lit in Z2. change (0 mod 2 ^ 64) with 0 in Z2.
    assert (L0 : am_last am = 0) by (destruct (Z.eq_dec (am_last am) 0) as [E|NE]; [exact E | exfalso; apply Z2; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NE]).
    rewrite L0. replace (9 * (0 + 1) <=? zU) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
End Bouncing.

Section Free3.
Hypothesis Hok : ltac2:(tb__ "0|0|
S0S70S1cVs;Vg;Vam;A3S72A3").
Definition s_m : astate := ltac2:(tb__ "0|0|
S185Vs;Vg;Vam;A3").
Lemma Hall' : ltac2:(tb__ "0|0|
S0S6aS8cS183Vam;A1S1eVi;A1A2S19ScVam;A1A1A3"). Proof using Hall. rewrite nmask_mask3. exact Hall. Qed.
Lemma nf_m : ltac2:(tb__ "0|0|
S1beVX;VU;Vs;S74S6cS6eS73S6aA2A1S11S184Vam;A1SfcA4A4").
Proof using HMI HR2g HU Hall Hgd Hml Hok Hsc48 Hu rho.
  apply (fgm_nf_post X U s g am i HI Hu HU HR2g Hall' Hsc48 Hml Hok Hlinks3 HnU3 HpU3 Hact3 HactU3 Hfree_ring3 63%nat).
  change 64%nat with NEST_FUEL. apply fneed_le. pose proof Hsc48'. lia.
Qed.
Lemma post_region3 : ltac2:(tb__ "0|2|
S3S73S73S3SdSdS1S0S6cSdA1SacSfcR2A2S6dSdR1A2A3S1S0S38S35R1A1S2fA3S1S0S70S37R1A1S72A3S1S0S6aS36R1A1M0S44S8fZ1000S14Vam;A1A2A1A3S1S0S6aSb6VL;R2A2SedVL;Vam;A2A3S1S8SaSa1VX;SfcR2R1A4S8dZ0S14R2A1A2S2S0S73S45S16R3A1A1R6A3A1F_;F_;Fa;Fq;S0S6cS6eS73S6aA2M1A1S184Vam;A1S6dG1S74S73S6aR2G0A4A2A3A2A2A2A2A2A2Lrg;A2Lkr;A2").
Proof using HMI HR2g HU Hall Hgd Hml Hok Hsc48 Hu rho.
  pose proof nf_m as (_ & _ & _ & Hm). cbn [fst snd fgm_res] in Hm. destruct Hm as (rg & Hr & Hk & Hl & Hlen & _ & Hno).
  destruct mapped3 as (r & rg0 & Em & _). exists (prid (am_mem am)), rg.
  repeat split; try assumption.
  - rewrite Hlen. f_equal. lia.
  - unfold zM, U.Mal_nt__G1.Mal_nt_I.zM, addr_of, loc_addr. rewrite Em. cbn [prid]. lia.
  - unfold fgm_res. rewrite Hlen, page_round_fixed; [reflexivity|]. unfold PGSZ. apply Z_mod_mult.
Qed.
Lemma real_m : ltac2:(tb__ "0|0|
S1bbVX;VU;Vsr;Vg;Vam;Vi;S184Vam;A1SfcS185Vsr;Vg;Vam;A3A9").
Proof using HIr HMI HR2g HU Hall Hgd Hml Hok Hsc48 Hu Hzs rho. exact (fgm_realW X U sr s g am i Hzs HIr Hu HU HR2g Hall' Hsc48 Hml Hok Hlinks3 HnU3 HpU3 Hact3 HactU3 Hfree_ringX3). Qed.

Definition l1_locs : list loc := ltac2:(tb__ "0|4|
S6cS8A1S71S9cA1M0Lx;SbVam;A1S8S70G0L_;M1S1aR1Vg;A2S75S9cS6fS9cSa3S8cSaeS8fZ8SdcVam;A1M2A2A2A1S78S9cA1M3A3S11bVg;A1A3S75S9cS1b4Vs;Vg;Vam;Se0Vg;Vam;A2R1A5G1S34S9eVs;G2A2S6dS8Vg;A2A2S11bR1A1G3X70x2A3X70x2Ln;G3X6cx2").
Lemma xraw_other t : ltac2:(tb__ "0|0|
S8S81S8R1VX;A3S0S6cS9A1S9dVt;R2A2S9dVs;R2A2A3F_;Fq;S18eVX;Vt;A2F_;").
Proof using HXz. intros H q Hq. rewrite (H q Hq). exact (HXz q Hq). Qed.
Lemma memb_used q a : ltac2:(tb__ "0|0|
Sa1VX;Vs;Vq;Va;A4S81S8Vq;VX;A3S5F_;F_;").
Proof using .
  intros Hq Hin. pose proof (proj2 (usedX_MT _ _ _ _ Hq)) as M. unfold memb in M.
  assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hin | apply sptr_eqb_refl]). rewrite E in M. discriminate.
Qed.
Lemma s1_facts : ltac2:(tb__ "0|2|
S1S11cVs;S181Vs;Vg;Vam;A3M0S100A3S1S3SaSaS1S0S6cS9A1M1S9dG0Vg;A2S6dS9S10R1A1A2A3S0S71S47A1S30R1A1S30Vam;A1A3A2La1;A2S1S189Vs;G0A2S8S2S0S8R1Vg;A3A1S2S0S8R2SdfVg;Vam;A2A3A1S2S0S8R3Se0Vg;Vam;A2A3A1S0G1S9dG0R4A2S9dVs;R4A2A3F_;F_;F_;Fq;A2A2A2").
Proof using HMI Hgd Hsc48 Hu rho.
  clear HR2g. unfold l1_locs. pose proof Hsc48' as SC. pose proof LenA3 as LA. pose proof ND_s3 as ND.
  destruct (am_next am) as [n|] eqn:En.
  - destruct (sptr_eqb n g) eqn:Eng.
    + apply sptr_eqb_eq in Eng. subst n. rewrite (fgm_s1_D1 s g am En).
      split; [exact (delta_dq1 s g am ND HMg_inst SC LA En)|].
      assert (DQ : dq_post s g am = upd_meta g (MUsed (am_set_links None None am)) (set_hd sc None s)) by (unfold dq_post; rewrite En, sptr_eqb_refl; reflexivity).
      rewrite DQ. split; [exists (am_set_links None None am); split; [apply MT_upd_same | reflexivity]|]. split.
      * eapply shape_kept_trans; [apply shape_kept_set_hd|]. apply (shape_kept_upd _ g am); [rewrite MT_set_hd; exact HMg_inst | repeat split; reflexivity].
      * intros q Hq _ _. rewrite (MT_upd_other g _ _ q Hq). apply MT_set_hd.
    + assert (Hng : n <> g) by (intros E; rewrite E, sptr_eqb_refl in Eng; discriminate).
      destruct (next_facts n En Hng) as (p & ap & an & Ep & Hpg & Hup & Hun & Scn & Scp & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
      rewrite EpQ, EnQ. pose proof (delta_dq_gen s g am ND HMg_inst SC LA p n ap an Ep En Hng Hpg Mp Mn) as D1.
      pose proof (MT_dq_g' s g am p n ap an Ep En Hng Mp Mn) as MG.
      pose proof (MT_dq_n s g am p n ap an Ep En Hng Mp Mn) as MN.
      assert (SH1 : shape_kept s (dq_post s g am)).
      { rewrite (dq_post_gen s g am p n ap an Ep En Hng Mp Mn).
        assert (SHa : shape_kept s (dq_s1a s p n ap)) by (unfold dq_s1a; apply (shape_kept_upd _ p ap); [exact Mp | repeat split; reflexivity]).
        assert (SHb : shape_kept s (dq_s1b s p n ap an)).
        { unfold dq_s1b. eapply shape_kept_trans; [exact SHa|]. apply (shape_kept_upd _ n (an1 p n ap an)); [apply MT_s1a_n; exact Mn | repeat split; reflexivity]. }
        assert (SHc : shape_kept s (dq_s1c s g am p n ap an)).
        { unfold dq_s1c. destruct (osptr_eqb _ _); [eapply shape_kept_trans; [exact SHb | apply shape_kept_set_hd] | exact SHb]. }
        eapply shape_kept_trans; [exact SHc|]. apply (shape_kept_upd _ g am); [|repeat split; reflexivity].
        rewrite MT_s1c, (MT_s1b_other s p n ap an g (fun E => Hpg (eq_sym E)) (fun E => Hng (eq_sym E))). exact HMg_inst. }
      assert (XO1 : forall q, q <> g -> q <> n -> q <> p -> MT (dq_post s g am) q = MT s q).
      { intros q Hq Hqn Hqp. rewrite (dq_post_gen s g am p n ap an Ep En Hng Mp Mn).
        rewrite (MT_upd_other g _ _ q Hq). rewrite MT_s1c. exact (MT_s1b_other s p n ap an q Hqp Hqn). }
      unfold fgm_s1. destruct (osptr_eqb (active_hd s sc) (Some g)) eqn:Ehd.
      * assert (Hhd : active_hd s (am_sc am) = Some g).
        { unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Ehd. destruct (active_hd s (am_sc am)) as [h|]; [|discriminate]. cbn in Ehd. apply sptr_eqb_eq in Ehd. rewrite Ehd. reflexivity. }
        pose proof (delta_act_gen s g am ND HMg_inst SC LA p n ap an Ep En Hng Hpg Mp Mn Hhd) as D2.
        split; [exact (delta_trans _ _ _ _ _ D1 D2)|].
        rewrite (act_post_gen s g am p n ap an Ep En Hng Mp Mn Hhd).
        split; [exists (am_set_links None None am); split; [rewrite (MT_upd_other n _ _ g (fun E => Hng (eq_sym E))); exact MG | reflexivity]|]. split.
        -- eapply shape_kept_trans; [exact SH1|]. apply (shape_kept_upd _ n _ _ MN). unfold am_activate. repeat split; reflexivity.
        -- intros q Hq Hqn Hqp. rewrite (MT_upd_other n _ _ q Hqn). exact (XO1 q Hq Hqn Hqp).
      * assert (Hhd : active_hd s (am_sc am) <> Some g).
        { unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Ehd. destruct (active_hd s (am_sc am)) as [h|]; [|discriminate]. cbn in Ehd. intros E. injection E as ->. rewrite sptr_eqb_refl in Ehd. discriminate. }
        rewrite (act_post_skip s g am n En Hhd), app_nil_r.
        split; [exact D1|]. split; [exists (am_set_links None None am); split; [exact MG | reflexivity]|]. split; [exact SH1 | exact XO1].
  - rewrite (fgm_s1_D0 s g am En). split; [apply delta_refl|]. split; [exists am; split; [exact HMg_inst | reflexivity]|]. split; [apply shape_kept_refl | intros; reflexivity].
Qed.
Lemma MT_m5_other q : ltac2:(tb__ "0|0|
S2S0S8Vq;Vg;A3A1S2S0S8Vq;SdfVg;Vam;A2A3A1S2S0S8Vq;Se0Vg;Vam;A2A3A1S0S6cS9A1S9dS182Vs;Vg;Vam;A3Vq;A2S9dVs;Vq;A2A3F_;F_;F_;").
Proof using HMI Hgd Hsc48 Hu rho.
  intros Hq Hqn Hqp. unfold fgm_s5. rewrite (MT_upd_other g _ _ q Hq). unfold fgm_s4, fgm_s3, fgm_s2.
  destruct (bounce_idx _); rewrite ?MT_set_unmap_seq, MT_seq_post, MT_set_usage; exact (proj2 (proj2 (proj2 s1_facts)) q Hq Hqn Hqp).
Qed.
Lemma keys_m5 : ltac2:(tb__ "0|0|
S0S71S8A1Sa4S182Vs;Vg;Vam;A3A1Sa4Vs;A1A3").
Proof using HMI Hall Hgd Hml Hsc48 Hsp Hu. exact (keys_fgm5 s g am ND_s3 Hfr0 Hsc48' LenA3 l1_locs (proj1 s1_facts) (proj1 (proj2 s1_facts))). Qed.
Lemma ND_m5 : ltac2:(tb__ "0|0|
S83S8Sa4S182Vs;Vg;Vam;A3A1A2"). Proof using HMI Hall Hgd Hml Hsc48 Hsp Hu. rewrite keys_m5. exact ND_s3. Qed.
Lemma X_not q a : ltac2:(tb__ "0|0|
Sa1VX;Vs;Vq;Va;A4S8S81S8R1VX;A3S2S0S8R2Vq;A3A1F_;Fx;F_;").
Proof using . intros Hq x Hx E. subst x. exact (memb_used q a Hq Hx). Qed.
Lemma X_not_fmem q : ltac2:(tb__ "0|0|
Se9Vs;VX;Vq;A3S8S81S8R1VX;A3S2S0S8R2Vq;A3A1F_;Fx;F_;").
Proof using Hu.
  intros Hq x Hx E. subst x. destruct (fmem_facts q Hq) as (pr & nx & _ & _ & _ & _ & _ & M). unfold memb in M.
  assert (E : existsb (sptr_eqb q) X = true) by (apply existsb_exists; exists q; split; [exact Hx | apply sptr_eqb_refl]). rewrite E in M. discriminate.
Qed.

Lemma free_not_gnp q pr nx : ltac2:(tb__ "0|0|
S0S6cS9A1S9dVs;Vq;A2S6dS9S12Vpr;Vnx;A2A2A3S1S2S0S8Vq;Vg;A3A1S1S2S0S8Vq;SdfVg;Vam;A2A3A1S2S0S8Vq;Se0Vg;Vam;A2A3A1A2A2F_;").
Proof using HMI Hgd Hu.
  intros M. pose proof (proj1 (usedX_MT _ _ _ _ nQ_used)) as Mn. pose proof (proj1 (usedX_MT _ _ _ _ pQ_used)) as Mp.
  repeat split; intros ->; [rewrite HMg_inst in M | rewrite Mn in M | rewrite Mp in M]; discriminate.
Qed.

Lemma cx3_m : ltac2:(tb__ "0|1|
S0S6eS6eS71S6aA1M0S6aA2G0A2S122SfcA1S122S182Vs;Vg;Vam;A3A1A3").
Proof using . unfold s_m, fgm_post, cx3. destruct (fq_fields (fgm_s5 s g am) g) as (A & B & C & _). rewrite A, B, C. reflexivity. Qed.
Lemma usage_of_m c : ltac2:(tb__ "0|1|
S8bZ0Vc;A2S0S6aS21SfcVc;A2S70S6aL_;S93Vc;SdcVam;A1M0A2S92S21Vs;G0A2S8cScVam;A1Z1A2A2S21Vs;Vc;A2X70x2A3F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 mW.
  intros Hc. pose proof cx3_m as CM. rewrite (proj1 flds_s5) in CM. unfold cx3 in CM. injection CM as E1 E2 E3.
  unfold usage_of at 1. rewrite E1. pose proof Hsc48' as SC. pose proof (proj1 (proj2 Hctx_ok)) as LU.
  rewrite znth_zset by (unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia). rewrite LU. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc.
  replace (am_sc am <? Z.of_nat 48%nat) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
Qed.
Lemma seq_of_m : ltac2:(tb__ "0|4|
S1S0S6aS18SfcA1S18S187Vs;A1M0A1M1A3S0S71S6aA1M2S1fSfcA1S6cS6aA1G2Lx;S31SdcVam;A1A1S6aS2eR1G1S1fG0A1M3A3Lk;G3X6cx2A3A2").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds mW. pose proof cx3_m as CM. rewrite (proj1 flds_s5) in CM. unfold cx3 in CM. injection CM as E1 E2 E3. split; [exact E2 | exact E3]. Qed.
Lemma ot3_m : ltac2:(tb__ "0|0|
S0S6eS6eS6eS6eS6eS71S6aA1S6aA2S71S8A1A2S71SdA1A2S6aA2S8A2S121SfcA1S121Vs;A1A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds mW. unfold s_m, fgm_post. rewrite (proj1 (flds_fq _ _)). exact (proj1 (proj2 flds_s5)). Qed.
Lemma active_m c : ltac2:(tb__ "0|0|
S8bZ0Vc;A2S2S0S6aVc;SdcVam;A1A3A1S0S6cS8A1S9eSfcVc;A2S9eVs;Vc;A2A3F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsp Hu mW.
  intros Hc Hne. rewrite <- (active_s1_other c Hc Hne). unfold active_hd. unfold s_m, fgm_post.
  rewrite (proj2 (flds_fq _ _)), (proj1 (proj2 (proj2 flds_s5))). reflexivity.
Qed.

Lemma usage_ge : ltac2:(tb__ "0|0|
S8bS8cScVam;A1Z1A2S21Vs;SdcVam;A1A2A2").
Proof using HMI HU Hgd Hsc48 Hsp Hu.
  pose proof (inv_usage HI sc Hsc48') as EU. pose proof (HU sc) as U0.
  pose proof (class_sum_ge_contrib X (Some (g, i)) U s sc g HI g_key) as GE.
  rewrite (contrib_used X s sc g am Hu) in GE. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. rewrite Z.eqb_refl in GE. lia.
Qed.
Lemma bounded_m : bounded s_m.
Proof using Erd Ewok HIr HMI HP13 HP13w HU Hgd Hgd_holds Hml Hsc48 Hsp Hu mW.
  pose proof (mig_bounded HMI) as (B1 & B2 & B3 & B4). cbn [ma_s] in B1, B2, B3, B4. pose proof usage_ge as UG. pose proof Hsc48' as SC. pose proof R_all as R.
  pose proof ot3_m as OM. unfold ot3 in OM. injection OM as O1 O2 O3 O4 O5 O6.
  split; [|rewrite O2, O3, O4, O5, O6; auto].
  assert (POS : forall c, 0 <= c -> 0 <= usage_of s_m c < 2 ^ 48).
  { intros c Hc. rewrite (usage_of_m c Hc). pose proof (B1 c) as Bc. pose proof (B1 sc) as Bs. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. destruct (c =? am_sc am); lia. }
  intros c. destruct (Z.le_gt_cases 0 c) as [Hc|Hc]; [exact (POS c Hc)|].
  replace (usage_of s_m c) with (usage_of s_m 0) by (unfold usage_of, znth; replace (Z.to_nat c) with (Z.to_nat 0) by lia; reflexivity).
  exact (POS 0 ltac:(lia)).
Qed.

Definition fq_locs : list loc := ltac2:(tb__ "0|1|
S6cS8A1S71S9cA1Lx;SfVs;A1S8S75S9cS75S9cS11bVg;A1M0S11bSe3Vs;Vg;A2A1A3S11bSe1Vs;Vg;A2A1A3Ls0;S75S9cG0S6fS9cSa3Sb4A1S78S9cA1A3A3X6cx2").
Definition LOCS : list loc := ltac2:(tb__ "0|0|
S75S9cS75S9cS75S9cS75S9cS75S9cS100S6fS9cSa3S8cSa8S8fZ8SdcVam;A1A2A2A1S78S9cA1A3A3S1b6Vs;A1A3S1b5Vam;A1A3S11bVg;A1A3S109A3").
Lemma ring_some fm : ltac2:(tb__ "0|b|
S0S6cS8A1M0SfVs;A1S6dS8Vfm;A2A3S3S8S8S3S8S8S3S8S8S3S8S8S1S0S8Se1Vs;Vg;A2Vfm;A3S1S0S8Se3Vs;Vg;A2R4A3S1Se9Vs;VX;Vfm;A3S1Se9Vs;VX;R4A3S1Se9Vs;VX;R3A3S1Se9Vs;VX;R2A3S1S0S6cS9A1M1S9dVs;Vfm;A2S6dS9S12S6dS8R4A2M2S6dS8R3A2M3A2A2M4A3S1S0G1S9dVs;R4A2S6dS9S12S6dS8R2A2M5S6dS8R1A2M6A2A2M7A3S1S2S0S8Vfm;Vg;A3A1S1S2S0S8R4Vg;A3A1S1S81S8Vfm;Sa4Vs;A1M8A3S1S81S8R4G8A3S1S81S8R3G8A3S1S81S8R2G8A3S1S0S6eG0G0A2M9SecVs;Vg;A2S74G0G0G2G3A4A3S1S0G9Sf1Vs;Vg;A2S74G0G0G5G6A4A3S1S0G1S9dS182Vs;Vg;Vam;A3MaVfm;A2G4A3S0G1S9dGaR4A2G7A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lnx2;A2Lpr2;A2Lnx;A2Lhp;A2F_;").
Proof using HMI Hgd Hsc48 Hu rho.
  intros Hfh.
  destruct fmL_cases as [(E & _) | (fm' & hp & nx & E & Efm & Hfm & M & EL & Hpr & Hnx & Eft & pr2 & nx2 & M2 & EL2 & Hpr2 & Hnx2)]; [rewrite E in Hfh; discriminate|].
  rewrite Hfh in E. injection E as <-.
  destruct (fmem_facts fm Hfm) as (_ & _ & _ & _ & _ & Kf & NEf & _). destruct (fmem_facts hp Hpr) as (_ & _ & _ & _ & _ & Kh & NEh & _).
  destruct (free_not_gnp fm _ _ M) as (F1 & F2 & F3). destruct (free_not_gnp hp _ _ M2) as (P1 & P2 & P3).
  exists hp, nx, pr2, nx2. repeat split; try assumption; try (apply fmem_key; assumption).
  - rewrite (MT_m5_other fm F1 F2 F3). exact M.
  - rewrite (MT_m5_other hp P1 P2 P3). exact M2.
Qed.
Lemma head_none_facts : ltac2:(tb__ "0|2|
S0S6cS8A1M0SfVs;A1S79S8A1M1A3S1S0S8Se1Vs;Vg;A2Vg;A3S1S0S8Se3Vs;Vg;A2Vg;A3S0S6eG0G0A2SecVs;Vg;A2S74G0G0G1G1A4A3A2A2F_;").
Proof using HMI Hu.
  intros Hfh. destruct fmL_cases as [(_ & E1 & E2 & E3 & _) | (fm' & pr & nx & E & _)]; [auto | rewrite E in Hfh; discriminate].
Qed.
Lemma deltaU_m : ltac2:(tb__ "0|0|
S1b3Vs;SfcS107A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hall Hgd Hgd_holds Hml Hsc48 Hsp Hu mW.
  unfold LOCS, s_m, fgm_post. apply (deltaU_trans s (fgm_s5 s g am)).
  - pose proof (deltaU_fgm5 s g am ND_s3 Hfr0 Hsc48' LenA3 l1_locs (proj1 s1_facts) (proj1 (proj2 s1_facts))) as D.
    replace (seq_locs_b (fgm_s1 s g am)) with (seq_locs_b s) in D; [exact D|].
    unfold seq_locs_b. pose proof (proj1 flds_s1) as C1. unfold cx3 in C1. injection C1 as E1 E2 E3. rewrite E2. reflexivity.
  - apply delta_U. unfold fq_locs. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
    destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
    + destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
      rewrite Efm, Eft. exact (delta_fq_ring (fgm_s5 s g am) g ND_m5 (MT_fgm5_g s g am) fm hp nx pr2 nx2 H5 M5 M5' NEf NEh).
    + exact (delta_fq_empty (fgm_s5 s g am) g ND_m5 (MT_fgm5_g s g am) H5).
Qed.
Lemma shape_m : shape_kept s s_m.
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  unfold s_m, fgm_post. eapply shape_kept_trans; [exact (shape_fgm5 s g am (proj1 (proj2 (proj2 s1_facts))))|].
  pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
    exact (shape_fq_ring (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh).
  - exact (shape_fq_empty (fgm_s5 s g am) g H5).
Qed.
Lemma hosts_m : reach_ok s_m. Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hreach Hsc48 Hu mW. exact (reach_ok_kept s s_m shape_m Hreach). Qed.

Lemma MT_m_other q : ltac2:(tb__ "0|0|
S2S0S8Vq;Vg;A3A1S2S0S8Vq;SdfVg;Vam;A2A3A1S2S0S8Vq;Se0Vg;Vam;A2A3A1S2S0S8Vq;Se1Vs;Vg;A2A3A1S2S0S8Vq;Se3Vs;Vg;A2A3A1S0S6cS9A1S9dSfcVq;A2S9dVs;Vq;A2A3F_;F_;F_;F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  intros H1 H2 H3 H4 H5'. unfold s_m, fgm_post. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  rewrite <- (MT_m5_other q H1 H2 H3).
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
    apply (MT_fq_other (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh q H1); [rewrite <- Efm; exact H4 | rewrite <- Eft; exact H5'].
  - exact (MT_fq_empty_other (fgm_s5 s g am) g q H5 H1).
Qed.
Lemma xraw_m : xzomb X s_m.
Proof using Erd Ewok HIr HMI HP13 HP13w HXz Hgd Hgd_holds Hsc48 Hu mW.
  apply xraw_other. intros q Hq. apply MT_m_other.
  - exact (X_not g am Hu q Hq).
  - exact (X_not nQ anQ nQ_used q Hq).
  - exact (X_not pQ apQ pQ_used q Hq).
  - unfold fmQ, U.Mal_nt__G1.Mal_nt_I.fmQ. destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [exact (X_not_fmem fm (fmem_head fm Hfh) q Hq) | exact (X_not g am Hu q Hq)].
  - destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
    + destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & Hhp & _). rewrite Eft. exact (X_not_fmem hp Hhp q Hq).
    + destruct fmL_cases as [(_ & _ & _ & E & _) | (fm' & pr & nx & E & _)]; [rewrite E; exact (X_not g am Hu q Hq) | rewrite E in Hfh; discriminate].
Qed.
Lemma head_m : ltac2:(tb__ "0|0|
S0S6cS8A1SfSfcA1S6dS8Se1Vs;Vg;A2A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  unfold s_m, fgm_post, fmQ, U.Mal_nt__G1.Mal_nt_I.fmQ. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
    exact (head_fq_ring (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh).
  - exact (head_fq_empty (fgm_s5 s g am) g H5).
Qed.
Lemma MT_m_g : ltac2:(tb__ "0|0|
S0S6cS9A1S9dSfcVg;A2S6dS9S12S6dS8Se3Vs;Vg;A2A2S6dS8Se1Vs;Vg;A2A2A2A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  unfold s_m, fgm_post. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
    rewrite Efm, Eft. exact (MT_fq_g (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh).
  - destruct fmL_cases as [(_ & E1 & _ & E2 & _) | (fm' & pr & nx & E & _)]; [|rewrite E in Hfh; discriminate].
    rewrite E1, E2. exact (MT_fq_empty_g (fgm_s5 s g am) g H5).
Qed.

Lemma MT_m_keep q : ltac2:(tb__ "0|0|
S2S0S8Vq;Vg;A3A1S2S0S8Vq;Se1Vs;Vg;A2A3A1S2S0S8Vq;Se3Vs;Vg;A2A3A1S0S6cS9A1S9dSfcVq;A2S9dS181Vs;Vg;Vam;A3Vq;A2A3F_;F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  intros H1 H4 H5'. unfold s_m, fgm_post. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  transitivity (MT (fgm_s5 s g am) q).
  - destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
    + destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & _ & _ & M5 & M5').
      apply (MT_fq_other (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh q H1); [rewrite <- Efm; exact H4 | rewrite <- Eft; exact H5'].
    + exact (MT_fq_empty_other (fgm_s5 s g am) g q H5 H1).
  - unfold fgm_s5. rewrite (MT_upd_other g _ _ q H1). unfold fgm_s4, fgm_s3, fgm_s2.
    destruct (bounce_idx _); rewrite ?MT_set_unmap_seq, MT_seq_post, MT_set_usage; reflexivity.
Qed.
Lemma active_m_all c : ltac2:(tb__ "0|0|
S0S6cS8A1S9eSfcVc;A2S9eS181Vs;Vg;Vam;A3Vc;A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds mW. unfold active_hd. unfold s_m, fgm_post. rewrite (proj2 (flds_fq _ _)), (proj1 (proj2 (proj2 flds_s5))). reflexivity. Qed.

Lemma used_not_fq q a : ltac2:(tb__ "0|0|
Sa1VX;Vs;Vq;Va;A4S2S0S8Vq;Vg;A3A1S1S2S0S8Vq;Se1Vs;Vg;A2A3A1S2S0S8Vq;Se3Vs;Vg;A2A3A1A2F_;F_;").
Proof using HMI Hgd Hsc48 Hu rho.
  intros Hq Hqg. pose proof (proj1 (usedX_MT _ _ _ _ Hq)) as Mq.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & _). rewrite Efm, Eft.
    split; intros ->; [rewrite M in Mq | rewrite M2 in Mq]; discriminate.
  - destruct (head_none_facts Hfh) as (E1 & E2 & _). rewrite E1, E2. auto.
Qed.
Section RingSome.
Variable fm : sptr.
Hypothesis Hfh : ltac2:(tb__ "0|0|
S0S6cS8A1SfVs;A1S6dS8Vfm;A2A3").
Lemma MT_m_fm : ltac2:(tb__ "0|3|
S0S6cS9A1S9dSfcSe1Vs;Vg;A2M0A2S6dS9S12S6dS8Vg;A2M1S70S6cS8A1M2L_;S1aG0Se3Vs;Vg;A2A2G1S7dG2G2SecVs;Vg;A2A3X70x2A2A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hfh Hgd Hgd_holds Hsc48 Hu mW.
  unfold s_m, fgm_post. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & EL & _ & M5 & M5').
  rewrite Efm, Eft, EL. cbn [snd]. rewrite Hfh in H5.
  pose proof (MT_fq_fm (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh) as X0. unfold fq_next' in X0. exact X0.
Qed.
Lemma MT_m_ft : ltac2:(tb__ "0|2|
S2S0S8Se3Vs;Vg;A2M0Se1Vs;Vg;A2A3A1S0S6cS9A1S9dSfcG0A2S6dS9S12S7bS6cS8A1M1G1Sf1Vs;Vg;A2A3S6dS8Vg;A2A2A2A3F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hfh Hgd Hgd_holds Hsc48 Hu mW.
  intros Hne. unfold s_m, fgm_post. pose proof (proj2 (proj2 (proj2 flds_s5))) as H5.
  destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & EL & EL2 & M5 & M5').
  rewrite Efm, Eft in Hne. rewrite Eft, EL2. cbn [fst]. rewrite Hfh in H5. exact (MT_fq_hp (fgm_s5 s g am) g fm hp nx pr2 nx2 H5 M5 M5' NEf NEh Hne).
Qed.
End RingSome.

Lemma res_regs SF rhoF : ltac2:(tb__ "0|2|
S11eVrhoW;VrhoF;A2S0S70S19fVSF;A1S72A3S1S6aS1S8bZ1R1A2S8bR1Z1fA2A2S0S70S88S98R2A1A1S72A3S0SbaSc8VSF;R3A2S8aS98R3A1A1A3F_;F_;Fz;S1S0Sd9Q40M0A1M1ScdVrhoF;Sc8VSF;ZaA2A2SdbG0SedVL;Vam;A2A2A3S0G1ScdVrhoF;Sc8VSF;ZbA2A2SdbG0S8fZ1000S14Vam;A1A2A2A3A2A2F_;F_;").
Proof using HMI Hgd Hml Hsc48 Hsp Hu mW.
  intros Hag Hr. destruct (leaf_regs_map_sound SF Hr) as (Hcs & R10 & R11). split; [exact Hcs|]. rewrite R10, R11. split.
  - rewrite <- (Z_to_bv_bv_unsigned 64 (eval rhoF (SVar 142))). f_equal. rewrite (EVX rhoF (SVar 142) Hag eq_refl eq_refl). rewrite ze_var, zr1_142. pose proof R_all. apply Z.mod_small. unfold zM, U.Mal_nt__G1.Mal_nt_I.zM in *. lia.
  - rewrite <- (Z_to_bv_bv_unsigned 64 (eval rhoF E_len)). f_equal. rewrite (EVX rhoF E_len Hag eq_refl eq_refl). apply ze_E_len.
Qed.

Lemma finish3 P m2 rhoT SF stk (dsT dsCT dsCP : list od) msF : ltac2:(tb__ "0|6|
S194Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VP;Vm2;AcS11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm2;A9VrhoT;A2Sc0S86VrhoT;VSF;S74S71S153A1S17eVtr;S17fVmsF;Vmd;A2A4M0A4VK;Vtr;Vmd;A2S0S70S19eVSF;VdsT;A2S72A3S0S71SbbA1ScfVSF;A1M1S6fSbbS158Vstk;A1S85SbbG1A2A3A3S4bS81S4bR1VdsT;A3M2S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9M3S81S4bR2VdsCT;A3A2F_;Fd;S4bS81S4bR1VP;A3S4G3S81S4bR2VdsCP;A3A2F_;Fd;S4bG2S111S4bS147Vs;VL;Vg;Vam;R2A5VP;A3F_;Fd;S4bS81S4bR1S75S4bVdsCT;VdsCP;A3A3M4S1S81S4bR2S75S4bVdsT;VP;A3A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcR2AaS157R2A1A2A2F_;Fd;S9cS81S9cR1S107A3S3S4bS4bS1G4S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M5A2S8dG5S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;S1a2S86S87Vrho;S18cS86S115S18aVX;VU;S192Vsr;VL;A2VKc;A7G0A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs.
  intros RID HagT HsmT HK' HOK Hobjs HentT HentP Hdisj HokC Hlocs.
  destruct (HKc _ _ HK') as (HKc' & _ & _).
  destruct (leaf_okb_sound SF dsT HOK) as (_ & Hmatch & Hvars & HDS & Hpc & Hregs & Hfregs & Hfcsr & Hresv & Hnx & HwfT).
  pose proof RID as (RS & RPW & RV & RH & RM & HwfP).
  assert (HcondT : forall d, In d dsT -> dcond d).
  { intros d Hd. destruct (HentT d Hd) as [[[_ C] _]|C]; [exact C|]. destruct (HokC d ltac:(apply in_app_iff; left; exact C)) as (_ & Hok' & Hchg').
    destruct d; cbn [U.Mal_nt__G1.Mal_nt_D.dcond]; try exact I; try (destruct Hchg'; fail); cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at] in Hok'; exact (proj1 Hok'). }
  destruct (carve_back P m2 rhoT SF tr msF md stk (tl (ss_objs SF)) dsT RID HagT HsmT Hobjs Hmatch HDS HcondT Hdisj Hnx HwfP) as [HSM' Hout].
  set (SF' := mkSS (ss_pc SF) (ss_regs SF) (ss_fregs SF) (ss_fcsr SF) (ss_resv SF) (ss_objs SF ++ map obj_of P) (ss_facts SF) (ss_next SF) (ss_lenient SF)) in *.
  pose proof (restore_rm segsU rhoT SF' (tr, mkCfg msF md) mW HSM' Hout) as HsmF.
  set (rhoF := set_rm rhoT mW) in *.
  assert (HagF : agrees rhoW rhoF) by (subst rhoF; apply agrees_of_V; exact (agreesV_of m2 rhoT HagT)).
  pose proof nf_m as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (res_regs SF rhoF HagF Hregs) as (Hcs & Ra0 & Ra1).
  destruct post_region3 as (kr & rg & R1 & R2 & R3 & R4 & R5 & Hno & Hres_m). pose proof R_all as R. pose proof len_range3 as LR.
  assert (Hobjs' : ss_objs SF' = oStkF stk :: (tl (ss_objs SF) ++ map obj_of P)) by (subst SF'; cbn [ss_objs]; rewrite Hobjs at 1; reflexivity).
  assert (Hmatch' : objs_matchb (tl (ss_objs SF) ++ map obj_of P) (map obj_of (dsT ++ P)) = true) by (rewrite map_app; apply objs_matchb_app; [exact Hmatch | apply objs_matchb_refl]).
  assert (Hvars' : forallb (obj_vars_all below200) (map obj_of (dsT ++ P)) = true) by (rewrite map_app, forallb_app, Hvars, RV; reflexivity).
  assert (HDS' : forallb ds_checkb (dsT ++ P) = true).
  { rewrite forallb_app, HDS. cbn [andb]. apply forallb_forall. intros d Hd. exact (proj1 (proj1 (Forall_forall _ _) RS d Hd)). }
  assert (Hcond' : forall d, In d (dsT ++ P) -> dcond d).
  { intros d Hd. apply in_app_iff in Hd as [Hd|Hd]; [exact (HcondT d Hd) | exact (proj2 (proj1 (Forall_forall _ _) RS d Hd))]. }
  assert (Hent' : forall d, In d (dsT ++ P) -> od_ok d \/ In d (dsCT ++ dsCP)).
  { intros d Hd. apply in_app_iff in Hd as [Hd|Hd].
    - destruct (HentT d Hd) as [X0|X0]; [left; exact X0 | right; apply in_app_iff; left; exact X0].
    - destruct (HentP d Hd) as [X0|X0]; [left; exact X0 | right; apply in_app_iff; right; exact X0]. }
  exact (post_ok_map tr md msF rhoF EmW Evm HagF SF' stk (tl (ss_objs SF) ++ map obj_of P) (dsT ++ P) (dsCT ++ dsCP) Hobjs' Hmatch' HsmF HDS' Hcond' Hent' s_m LOCS HI' xraw_m deltaU_m bounded_m HokC Hlocs
           Hpc Hcs Hfregs Hfcsr Hresv Hsm_pre Kc HKc' zM (4096 * am_maplen am) kr rg Ra0 Ra1 ltac:(unfold zM, U.Mal_nt__G1.Mal_nt_I.zM in *; lia) LR
           (conj R1 (conj R2 (conj R3 (conj R4 R5)))) Hno hosts_m
           (fgm_post sr g am) (fgm_res am) real_m Hres_m).
Qed.

Definition fshape : nat := ltac2:(tb__ "0|0|
S6cS8A1S73Lx;SfVs;A1S8S70S73L_;S1aSe3Vs;Vg;A2Se1Vs;Vg;A2A2U1U2X70x2Ls0;U0X6cx2").
Definition ds_t2new (f : nat) : list od := ltac2:(tb__ "0|5|
S73S71S4bA1M0Lf;Vf;S6fS4bS52SbdZ0A1A1S78S4bA1M1A3S73S73G0Ln;R1S6fS4bS52Sd8Pa0A1M2A1M3S6fS4bS4eS50S77G2Sd8Pa2A1M4A4G1A3A3S73S6fS4bG3S6fS4bS4eS50S77Sd8Pa1A1G4A4S6fS4bS4eS59S77Sd8Pa3A1Sd8Pa4A1A4G1A3A3A3Ln0;X73x2Ln;X73x2").
Definition dsT (f : nat) : list od := ltac2:(tb__ "0|5|
S73S71S4bA1M0Lf;Vf;S6fS4bS4eS51S72Sd8PcA1M1G1A4S6fS4bS55S6fS4bS52G1A1S78S4bA1M2A3A3A3S73S73G0Ln;R1S6fS4bS4eS51S72Sd8Pa0A1M3G3A4S6fS4bS55S6fS4bS52G3A1M4S6fS4bS4eS50S77G1G1A4G2A3A3A3A3S73S6fS4bS4eS51S72Sd8Pa1A1G3A4S6fS4bS55S6fS4bG4S6fS4bS4eS50S77G1Sd8Pa2A1A4S6fS4bS4eS59S77Sd8Pa3A1G1A4G2A3A3A3A3A3Ln0;X73x2Ln;X73x2").
Definition dsCT (f : nat) : list od := ltac2:(tb__ "0|4|
S73S71S4bA1M0Lf;Vf;S6fS4bS4eS51S72Sd8PcA1M1G1A4S6fS4bS52G1A1S78S4bA1M2A3A3S73S73G0Ln;R1S6fS4bS4eS51S72Sd8Pa0A1M3G3A4S6fS4bS4eS50S77G1G1A4G2A3A3S73S6fS4bS4eS51S72Sd8Pa1A1G3A4S6fS4bS4eS50S77G1Sd8Pa2A1A4S6fS4bS4eS59S77Sd8Pa3A1G1A4G2A3A3A3Ln0;X73x2Ln;X73x2").

Lemma T2cert0 : ltac2:(tb__ "0|a|
S0S70S76S76S76S76S76S76S76S76S76S76S193SffU0M0A1M1S16bSd8P8cA1M2SbdZ0A1M3G0A3M4A2S15aS75SbbS6fSbbS16dS6fSbbS16cG2G3A2S6fSbbS16fS78SbbA1A3M5A3A3S112S4bSbbS4fSfeG0A1M6A4M7A3S16eG2G3G0A3A2A2SbfG4A1A2S193G1S16bG3G3G0A3M8A2A2S15aS75SbbS6fSbbS16dS6fSbbS16cG3G3A2G5A3A3G7A3S16eG3G3G0A3A2A2SbfG8A1A2S82SbbSc6Pc8A1G7A3A2S82S4bS53G6A3A2S82SbbS1a3S11fA1G7A3A2S82SbcS10eS172G0A1M9A3A2S82SbcS1a1S11fA1G9A3A2S72A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma T2cert1 : ltac2:(tb__ "0|a|
S0S70S76S76S76S76S76S76S76S76S76S76S193SffU1M0A1M1S16bSd8P8cA1M2SbdZ0A1M3G0A3M4A2S15aS75SbbS6fSbbS16dS6fSbbS16cG2G3A2S6fSbbS16fS78SbbA1A3M5A3A3S112S4bSbbS4fSfeG0A1M6A4M7A3S16eG2G3G0A3A2A2SbfG4A1A2S193G1S16bG3G3G0A3M8A2A2S15aS75SbbS6fSbbS16dS6fSbbS16cG3G3A2G5A3A3G7A3S16eG3G3G0A3A2A2SbfG8A1A2S82SbbSc6Pc8A1G7A3A2S82S4bS53G6A3A2S82SbbS1a3S11fA1G7A3A2S82SbcS10eS172G0A1M9A3A2S82SbcS1a1S11fA1G9A3A2S72A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma T2cert2 : ltac2:(tb__ "0|a|
S0S70S76S76S76S76S76S76S76S76S76S76S193SffU2M0A1M1S16bSd8P8cA1M2SbdZ0A1M3G0A3M4A2S15aS75SbbS6fSbbS16dS6fSbbS16cG2G3A2S6fSbbS16fS78SbbA1A3M5A3A3S112S4bSbbS4fSfeG0A1M6A4M7A3S16eG2G3G0A3A2A2SbfG4A1A2S193G1S16bG3G3G0A3M8A2A2S15aS75SbbS6fSbbS16dS6fSbbS16cG3G3A2G5A3A3G7A3S16eG3G3G0A3A2A2SbfG8A1A2S82SbbSc6Pc8A1G7A3A2S82S4bS53G6A3A2S82SbbS1a3S11fA1G7A3A2S82SbcS10eS172G0A1M9A3A2S82SbcS1a1S11fA1G9A3A2S72A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Definition T2PACK (f : nat) : Prop := ltac2:(tb__ "0|4|
S1SbaSbaS81S6eSbaSbaA2S74SbaSbaR2R1A4S170A3S1S0S70S193SffVf;A1S16bR3R2Vf;A3M0A2S72A3S1S0S70S15aS75SbbS6fSbbS16dS6fSbbS16cR3R2A2S6fSbbS16fS78SbbA1A3A3A3S112S4bSbbS4fSfeVf;A1M1A4M2A3S16eR3R2Vf;A3A2S72A3S0S70SbfG0A1S72A3A2A2F_;Fnv;Fpv;S1S0S70S82SbbSc6Pc8A1G2A3S72A3S1S0S70S82S4bS53G1A3S72A3S1S0S70S82SbbS1a3S11fA1G2A3S72A3S1S0S70S82SbcS10eS172Vf;A1M3A3S72A3S0S70S82SbcS1a1S11fA1G3A3S72A3A2A2A2A2A2").
Local Ltac t2pack C :=
  let X := fresh "CX" in pose proof C as X;
  let Fs := fresh "Fs" in let Fv := fresh "Fv" in let Nv := fresh "Nv" in let Nds := fresh "Nds" in let Nwf := fresh "Nwf" in
  let A1 := fresh "A" in let A2 := fresh "A" in let A3 := fresh "A" in let B1 := fresh "B" in let B2 := fresh "B" in let B3 := fresh "B" in
  apply andb_prop in X as [X Fs]; apply andb_prop in X as [X Fv]; apply andb_prop in X as [X Nv]; apply andb_prop in X as [X Nds]; apply andb_prop in X as [X Nwf];
  apply andb_prop in X as [X B3]; apply andb_prop in X as [X B2]; apply andb_prop in X as [X B1];
  apply andb_prop in X as [X A3]; apply andb_prop in X as [A1 A2];
  split; [intros pv nv [E|[E|[]]]; injection E as <- <-; [exact (conj A1 (conj A2 A3)) | exact (conj B1 (conj B2 B3))] | repeat split; assumption].
Lemma T2pack0 : T2PACK 0. Proof using . t2pack T2cert0. Qed.
Lemma T2pack1 : T2PACK 1. Proof using . t2pack T2cert1. Qed.
Lemma T2pack2 : T2PACK 2. Proof using . t2pack T2cert2. Qed.
Lemma fshape_le : (fshape <= 2)%nat. Proof using Hgd Hsc48 rho. unfold fshape. destruct (st_free_meta_head s); [destruct (sptr_eqb _ _)|]; lia. Qed.
Lemma T2pack_fs : T2PACK fshape.
Proof using . unfold fshape. destruct (st_free_meta_head s); [destruct (sptr_eqb _ _)|]; [exact T2pack1 | exact T2pack2 | exact T2pack0]. Qed.

Lemma ds_t2new_ok : Forall od_ok (ds_t2new fshape).
Proof using HMI Hgd Hsc48 Hu.
  unfold fshape. destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - assert (Hfh' : st_free_meta_head s <> None) by (rewrite Hfh; discriminate).
    destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & _ & _ & _ & _ & EL & EL2 & _).
    destruct (sptr_eqb ftQ fmQ) eqn:Es.
    + apply sptr_eqb_eq in Es. constructor; [apply od_ok_fmh_entry; [reflexivity | apply ze160]|]. constructor; [|constructor].
      apply (od_ok_fm_entry (v 160) Hfh' eq_refl). rewrite ze160. unfold zF, zFp, U.Mal_nt__G1.Mal_nt_I.zF, U.Mal_nt__G1.Mal_nt_I.zFp. rewrite Hfh.
      change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL. rewrite EL. cbn [optrA fst]. rewrite <- Eft, Es, Efm. reflexivity.
    + constructor; [apply od_ok_fmh_entry; [reflexivity | apply ze160]|]. constructor; [apply (od_ok_fm_entry (v 161) Hfh' eq_refl ze161)|].
      constructor; [apply (od_ok_ft_entry Hfh') | constructor].
  - constructor; [|constructor]. apply od_ok_fmh_entry; [reflexivity|]. rewrite ze_lit. unfold zF, U.Mal_nt__G1.Mal_nt_I.zF. rewrite Hfh. reflexivity.
Qed.

Lemma facts_t2_hold : ltac2:(tb__ "0|0|
S111SbcS10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S172SfdA1A3").
Proof using HMI HP12 Hdepth Hgd Hsp Hu.
  unfold fshape. destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - assert (Hfh' : st_free_meta_head s <> None) by (rewrite Hfh; discriminate).
    destruct (sptr_eqb ftQ fmQ) eqn:Es.
    + cbn [facts_t2]. constructor; [apply (ZF_fmN0 Hfh')|]. apply ZF_base.
    + cbn [facts_t2]. constructor; [apply (ZF_fmN0 Hfh')|]. constructor; [apply (ZF_fm_ne_ft Hfh'); intros E; rewrite E, sptr_eqb_refl in Es; discriminate|]. apply ZF_base.
  - cbn [facts_t2]. apply ZF_base.
Qed.

Lemma ds_t2new_pw : od_pairwise (ds_t2new fshape).
Proof using .
  clear HKc Hsm_pre EmW Evm. unfold fshape. destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - assert (Hfh' : st_free_meta_head s <> None) by (rewrite Hfh; discriminate).
    destruct (sptr_eqb ftQ fmQ) eqn:Es; cbn; od_pw; try exact Hfh'.
    intros E. rewrite E, sptr_eqb_refl in Es. discriminate Es.
  - cbn; od_pw.
Qed.
Lemma ds_t2new_disj_live pv nv : ltac2:(tb__ "0|0|
S4bS81S4bR1S6fS4bS57S5cVpv;Vnv;Sd8P85A1Sd8P86A1A5S6fS4bS55S78S4bA1A3A3A3S111S4bS147Vs;VL;Vg;Vam;R2A5SfeSfdA1A3F_;Fd;").
Proof using HMI Hgd Hsc48 Hu rho.
  clear HKc Hsm_pre EmW Evm. intros d Hd. unfold fshape.
  destruct Hd as [<-|[<-|[]]]; (destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|]); cbn; od_pw;
    try (rewrite Hfh; discriminate).
  all: try (unfold fmQ, U.Mal_nt__G1.Mal_nt_I.fmQ; rewrite Hfh; destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & _ & _ & NEf & NEh & _); intros E; apply NEf; symmetry; exact E).
  all: try (destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & _ & _ & NEf & NEh & _); rewrite Eft; intros E; apply NEh; symmetry; exact E).
Qed.

Lemma link2 (pv nv : sv) (P : list od) m2 rhoX Lfacts nx tr0 msL md0 : ltac2:(tb__ "0|4|
S81S6eSbaSbaA2S74SbaSbaVpv;Vnv;A4S170A3S194Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VP;Vm2;AcS11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm2;A9VrhoX;A2S4bS81S4bR1SfeSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP;A3F_;Fd;S1b1Pc8Vnx;A2Sc0S86VrhoX;Sd4Z20b30S17cS89Sd2S79SbaA1S6fSbbS16dS6fSbbS16cVpv;Vnv;A2S6fSbbS16fS78SbbA1A3A3M0A3VLfacts;Vnx;S77A9S74S71S153A1S17eVtr0;S17fVmsL;Vmd0;A2A4M1A4S5bVam;S57S5cVpv;Vnv;Sd8P85A1Sd8P86A1A5M2A2S0S70S82S4bS53S6fS4bG2S6fS4bS55S78S4bA1A3A3M3A3S72A3S0S70S15aG0S112S4bSbbS4fG3A4A2S72A3Sc0S86VrhoX;S16bVpv;Vnv;SfdA3G1A4F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsc48 Hsp Hsp_high Hu.
  intros Hpv RID Hag HX Hnx Hsm Cg Hdsl Hdsm.
  destruct T2pack_fs as (Cq & Nwf & Nds & Nv & Fv & Fs). destruct (Cq pv nv Hpv) as (_ & Hm2 & Hwf2).
  assert (DSL : Forall DS [OD_meta KG pv nv (v 133) (v 134); OD_guard]).
  { apply Forall_forall. intros d Hd. split; [exact (proj1 (forallb_forall _ _) Hdsl d Hd)|]. destruct Hd as [<-|[<-|[]]]; [exact Cg | exact I]. }
  assert (DSN : Forall DS (ds_t2new fshape)).
  { apply Forall_forall. intros d Hd. exact (proj1 (proj1 (Forall_forall _ _) ds_t2new_ok d Hd)). }
  pose proof (carve_on (ds_t2new fshape) m2 rhoX _ tr0 msL md0 (ob_cells o_stk_saved) [o_gmeta pv nv; O_guard_] [OD_meta KG pv nv (v 133) (v 134); OD_guard]
                Hag Hsm eq_refl Hdsm DSL DSN ds_t2new_pw Nv
                ltac:(intros d Hd; apply (od_hold_m P m2 d RID (proj1 (Forall_forall _ _) ds_t2new_ok d Hd) (HX d Hd)))
                (ds_t2new_disj_live pv nv) Hnx Nwf) as Hsm4.
  cbn zeta in Hsm4.
  apply (smatch_canon rhoX _ (S_t2_of pv nv fshape) tr0 msL md0 Hsm4); try reflexivity.
  - exact Hwf2.
  - exact Hm2.
  - cbn [ss_facts S_t2_of]. apply (ZF_holdsm m2 rhoX (facts_t2 fshape) Hag Fs Fv facts_t2_hold).
Qed.

Lemma locs_meta_of (q : sptr) (d : od) (dsC : list od) l : ltac2:(tb__ "0|2|
S81S4bVd;VdsC;A3S0S6aS4cVs;VL;Vg;Vam;Vd;A5S116VL;Vq;A2M0A3S0S6aS4dVs;VL;Vg;Vam;Vd;A5S8cG0Z28A2A3S81S9cVl;S11bVq;A1A3S3S4bS4bS1S81S4bR1VdsC;A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;Vl;A2M1A2S8dG1S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld';A2F_;F_;F_;F_;").
Proof using Hgd Hsc48 rho.
  intros Hd E1 E2 Hl. exists d. split; [exact Hd|]. rewrite E1, E2.
  assert (AG : forall dd, loc_addr L (LMem (padd q dd)) = addr_of L q + dd) by (intros dd; unfold addr_of, loc_addr; destruct q; cbn [padd]; lia).
  unfold meta_locs, META_prev, META_next, META_mem, META_avail, META_freed, META_bits in Hl.
  destruct Hl as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; rewrite AG; lia.
Qed.
Lemma okC_T : ltac2:(tb__ "0|0|
S4bS81S4bR1S103SfdA1A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcR2AaS157R2A1A2F_;Fd;").
Proof using Erd Ewok HIr HMI HP12 HP13 HP13w Hgd Hgd_holds Hsc48 Hu mW.
  clear HKc Hsm_pre EmW Evm. intros d Hd. pose proof MT_m_g as MG. pose proof head_m as HM. unfold fshape in Hd.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & Kf & Kh & Kn & Kp & EL & EL2 & _).
    assert (Hfh' : st_free_meta_head s <> None) by (rewrite Hfh; discriminate).
    pose proof (MT_m_fm fm Hfh) as MF.
    destruct (sptr_eqb ftQ fmQ) eqn:Es.
    + apply sptr_eqb_eq in Es. destruct Hd as [<-|[<-|[]]].
      * split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
        exists (Some ftQ), (Some fmQ). split; [exact MG|]. rewrite Es, Efm.
        split; [intros p Hp; injection Hp as <-; exact Kf|]. split; [intros p Hp; injection Hp as <-; exact Kf|].
        rewrite ze160. unfold zF, U.Mal_nt__G1.Mal_nt_I.zF. rewrite Hfh. split; reflexivity.
      * split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
        exists (Some g), (Some g). rewrite Es, sptr_eqb_refl in MF. split; [exact MF|].
        split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze12. split; reflexivity.
    + assert (Hne : ftQ <> fmQ) by (intros E; rewrite E, sptr_eqb_refl in Es; discriminate).
      replace (sptr_eqb fmQ ftQ) with false in MF by (symmetry; apply sptr_eqb_neq; intros E; exact (Hne (eq_sym E))).
      pose proof (MT_m_ft fm Hfh Hne) as MH.
      destruct Hd as [<-|[<-|[<-|[]]]].
      * split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
        exists (Some ftQ), (Some fmQ). split; [exact MG|]. rewrite Eft, Efm.
        split; [intros p Hp; injection Hp as <-; exact Kh|]. split; [intros p Hp; injection Hp as <-; exact Kf|].
        rewrite ze161, ze160. unfold zF, zFp, U.Mal_nt__G1.Mal_nt_I.zF, U.Mal_nt__G1.Mal_nt_I.zFp. rewrite Hfh. change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL. rewrite EL. split; reflexivity.
      * split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
        exists (Some g), (snd fmL). split; [exact MF|]. rewrite EL. cbn [snd].
        split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact Kn|]. rewrite ze12, ze162. unfold zFn, U.Mal_nt__G1.Mal_nt_I.zFn. change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL. rewrite EL. split; reflexivity.
      * split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact Hfh'|].
        exists (fst ftL), (Some g). split; [exact MH|]. rewrite EL2. cbn [fst].
        split; [intros p Hp; injection Hp as <-; exact Kp|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze163, ze12. unfold zTTp, U.Mal_nt__G1.Mal_nt_I.zTTp. change (U.Mal_nt__G1.Mal_nt_I.ftL s g) with ftL. rewrite EL2. split; reflexivity.
  - destruct (head_none_facts Hfh) as (E1 & E2 & E3). destruct Hd as [<-|[<-|[]]].
    + split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G1.Mal_nt_D.fptr]. split; [exact I|].
      exists (Some ftQ), (Some fmQ). split; [exact MG|]. rewrite E1, E2.
      split; [intros p Hp; injection Hp as <-; exact g_key|]. split; [intros p Hp; injection Hp as <-; exact g_key|]. rewrite ze12. split; reflexivity.
    + split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. rewrite HM, E1, ze12. reflexivity.
Qed.
Lemma ent_T : ltac2:(tb__ "0|0|
S4bS81S4bR1SffSfdA1A3S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S81S4bR2S103SfdA1A3A2F_;Fd;").
Proof using HMI Hgd Hu.
  clear HKc Hsm_pre EmW Evm. intros d Hd. unfold fshape in *.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|].
  - destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; [right; left; reflexivity | left; apply od_ok_guard | left; apply od_ok_fmh_entry; [reflexivity | apply ze160] | right; right; left; reflexivity].
  - destruct Hd as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [right; left; reflexivity | left; apply od_ok_guard | left; apply od_ok_fmh_entry; [reflexivity | apply ze160] | right; right; left; reflexivity | right; right; right; left; reflexivity].
  - destruct Hd as [<-|[<-|[<-|[]]]]; [right; left; reflexivity | left; apply od_ok_guard | right; right; left; reflexivity].
Qed.
Lemma locs_T : ltac2:(tb__ "0|1|
S9cS81S9cR1S75S9cS11bVg;A1S109A3A3S3S4bS4bS1S81S4bR1S103SfdA1A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M0A2S8dG0S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hgd Hsc48 Hu Kc md rho tr.
  clear HKc Hsm_pre EmW Evm. intros l Hl. pose proof Hctx as HCX. unfold fq_locs, fshape in *.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh.
  - destruct (ring_some fm Hfh) as (hp & nx & pr2 & nx2 & Efm & Eft & _ & _ & _ & _ & M & M2 & NEf & NEh & Kf & Kh & Kn & Kp & EL & EL2 & _).
    assert (MG : forall pv nv rest, In l (meta_locs g) -> exists d, In d (OD_free FG true pv nv :: rest) /\ dlo d <= loc_addr L l < dhi d).
    { intros pv nv rest Hm. apply (locs_meta_of g (OD_free FG true pv nv)); [left; reflexivity | reflexivity | reflexivity | exact Hm]. }
    assert (MF : forall d0 nv rest, In l (meta_locs fmQ) -> exists d, In d (d0 :: OD_free FM false (v 12) nv :: rest) /\ dlo d <= loc_addr L l < dhi d).
    { intros d0 nv rest Hm. apply (locs_meta_of fmQ (OD_free FM false (v 12) nv)); [right; left; reflexivity | | | exact Hm];
        unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.flo]; unfold zF, U.Mal_nt__G1.Mal_nt_I.zF; rewrite Hfh, Efm; reflexivity. }
    destruct (sptr_eqb ftQ fmQ) eqn:Es.
    + apply sptr_eqb_eq in Es. rewrite Es in Hl.
      apply in_app_iff in Hl as [Hl|Hl]; [exact (MG _ _ _ Hl)|]. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [exact (MG _ _ _ Hl) | exact (MF _ _ _ Hl)] | exact (MF _ _ _ Hl)].
    + apply in_app_iff in Hl as [Hl|Hl]; [exact (MG _ _ _ Hl)|]. apply in_app_iff in Hl as [Hl|Hl]; [apply in_app_iff in Hl as [Hl|Hl]; [exact (MG _ _ _ Hl) |] | exact (MF _ _ _ Hl)].
      apply (locs_meta_of ftQ (OD_free FT false (v 163) (v 12))); [right; right; left; reflexivity | | | exact Hl];
        unfold U.Mal_nt__G1.Mal_nt_D.dhi; cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.flo]; unfold zFp, U.Mal_nt__G1.Mal_nt_I.zFp; change (U.Mal_nt__G1.Mal_nt_I.fmL s g) with fmL; rewrite EL, Eft; reflexivity.
  - destruct (head_none_facts Hfh) as (E1 & E2 & E3).
    assert (MG : In l (meta_locs g) -> exists d, In d (dsCT 0) /\ dlo d <= loc_addr L l < dhi d).
    { intros Hm. apply (locs_meta_of g (OD_free FG true (v 12) (v 12))); [left; reflexivity | reflexivity | reflexivity | exact Hm]. }
    apply in_app_iff in Hl as [Hl|Hl]; [exact (MG Hl)|]. apply in_app_iff in Hl as [Hl|Hl]; [exact (MG Hl)|].
    destruct Hl as [<-|[]]. exists (OD_fmh (v 12)). split; [right; left; reflexivity|].
    unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_free_meta_head. lia.
Qed.

Lemma le_byte_narrow z (w : nat) (k : nat) : ltac2:(tb__ "0|0|
S163Vk;Vw;A2S8bZ0Vz;A2S0S6aSabVz;Vw;Vk;A3S90S94Vz;S8eZ2S8fZ8S91Vk;A1A2A2A2Z100A2A3F_;F_;").
Proof using Hgd Hsc48 Hsp.
  intros Hk Hz. unfold le_byte. rewrite Z.shiftr_div_pow2 by lia.
  set (M := 2 ^ (8 * Z.of_nat k)). set (W := 2 ^ (8 * Z.of_nat w)).
  assert (HM : 0 < M) by (subst M; apply Z.pow_pos_nonneg; lia).
  assert (HWM : W = M * (2 ^ (8 * (Z.of_nat w - Z.of_nat k - 1)) * 256)).
  { subst W M. change 256 with (2 ^ 8). rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
  set (R := 2 ^ (8 * (Z.of_nat w - Z.of_nat k - 1))) in HWM.
  assert (HR : 0 < R) by (subst R; apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod z W ltac:(lia)) as E. pose proof (Z.mod_pos_bound z W ltac:(lia)) as B.
  assert (E' : z mod W = z + (- (z / W) * (R * 256)) * M) by lia.
  rewrite E'. rewrite Z.div_add by lia.
  replace (- (z / W) * (R * 256)) with ((- (z / W) * R) * 256) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma le_byte_shift z (sh : Z) (w : nat) (j : nat) : ltac2:(tb__ "0|3|
S8bZ0M0Vz;A2S8bG0Vsh;A2S0S6aS90Vsh;Z8M1A2G0A3S163Vj;Vw;A2S0S6aSabS94Vz;S8eZ2M2Vsh;A2A2Vw;Vj;A3S90S94Vz;S8eG2S8fG1S8cS94Vsh;G1A2S91Vj;A1A2A2A2A2Z100A2A3F_;F_;F_;F_;").
Proof using Hgd Hsc48 Hsp.
  intros Hz Hsh Hm Hj. rewrite (le_byte_narrow _ w j Hj) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  rewrite Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.lt_le_incl, Z.pow_pos_nonneg; lia).
  rewrite <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. pose proof (Z.div_mod sh 8 ltac:(lia)). lia.
Qed.
Lemma nth_byte_of_dw (q : nat) (t : nat) : ltac2:(tb__ "0|2|
S163Vt;U8M0A2S0S6aS90S94Sf6S1fVs;A1M1Vq;A2S8eZ2S8fZ8S91Vt;A1A2A2A2Z100A2S113S6aS1aeS1afG0Vq;A2Vt;A2G1Z0A4A3F_;").
Proof using HMI Hgd Hsc48 Hsp.
  intros Ht. rewrite <- (udw_byte (st_unmap_seq s) q t Ht ltac:(pose proof (useq_byte (8 * q + t)%nat); lia)).
  symmetry. apply le_byte_narrow; [exact Ht | pose proof (udw_range (st_unmap_seq s) q); lia].
Qed.

Definition CREL (c : Z) : Prop := ltac2:(tb__ "0|2|
S4S1S1S8bZ7M0SdcVam;A1M1A2S8bG1Z26A2A2S0S6aVc;G1A3A2S4S1S8dG1G0A2S0S6aVc;Z0A3A2S1S8bZ27G1A2S0S6aVc;Z2fA3A2A2A2").
Lemma ze_seq8 : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sc3S77Q8Sd8P98A1A3A3SfbVs;A1A3").
Proof using HMI Hgd Hsc48. rewrite ze_ext, ze152. change (Z.of_N 8) with 8. pose proof seq_range. apply Z.mod_small. lia. Qed.
Lemma seq_b_of (b : bool) : ltac2:(tb__ "0|0|
S10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S70SbcLb;Vb;S19aS19bX70x2A3S0S70S93S18Vs;A1ZffA2Vb;A3F_;").
Proof using HMI Hgd Hsc48.
  unfold F_seq_eq, F_seq_ne. destruct b; cbn [zholds zcond]; rewrite ze_seq8, ze_lit; change (255 mod 2 ^ 64) with 255; unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq; intros H.
  - destruct (st_seq s =? 255); [reflexivity | exfalso; apply H; reflexivity].
  - apply Bool.negb_true_iff in H. exact H.
Qed.
Lemma seq_ok_m (b : bool) : ltac2:(tb__ "0|1|
S0S70S93S18Vs;A1ZffA2Vb;A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS63S199Vb;A1A1M0AaS157G0A1A2F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 mW.
  intros Hb. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. rewrite (proj1 seq_of_m), (proj1 (seq_post_seq s)), Hb.
  pose proof seq_range as SR. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq in SR.
  destruct b; cbn [E_seq'].
  - rewrite ze_lit. reflexivity.
  - unfold E_seq1. rewrite ze_alu, ze_seq8, ze_lit. cbn [zalu]. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq in *.
    apply Z.eqb_neq in Hb. change (1 mod 2 ^ 64) with 1. rewrite (Z.mod_small _ (2 ^ 64)) by lia. reflexivity.
Qed.
Lemma useqL_ok_m (b : bool) (c : Z) (cs : list (Z * nat * sv)) : ltac2:(tb__ "0|1|
S0S70S93S18Vs;A1ZffA2Vb;A3S104Vc;A1S0S70S60Vcs;A1S72A3S0S70S82S6eS6eS6aS73A2SbaA2S198Vc;Vb;A2Vcs;A3S72A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS64Vcs;A1M0AaS157G0A1A2F_;F_;F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hsc48 Hsp mW.
  intros Hb HC Huok Hcells. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at].
  pose proof (proj2 seq_of_m) as EU. pose proof (seq_post_seq s) as [ES EU0]. rewrite Hb in ES, EU0.
  pose proof seq_range as SR. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq in SR. pose proof useq_len as UL. pose proof Hsc48' as SC.
  set (seq' := st_seq (seq_post s)) in *. set (useq' := st_unmap_seq (seq_post s)) in *.
  assert (Hseq' : 0 <= seq' <= 255) by (subst seq'; rewrite ES; destruct b; [lia | apply Z.eqb_neq in Hb; lia]).
  assert (UL' : length useq' = 32%nat) by (subst useq'; rewrite EU0; destruct b; [rewrite repeat_length; reflexivity | exact UL]).
  assert (UB' : forall k, 0 <= nth k useq' 0 <= 255).
  { intros k. subst useq'. rewrite EU0. destruct b; [|apply useq_byte]. destruct (Nat.lt_ge_cases k 32) as [Hk|Hk]; [rewrite nth_repeat_lt by exact Hk | rewrite nth_overflow by (rewrite repeat_length; exact Hk)]; lia. }

  assert (NTH : forall k, nth k (st_unmap_seq s_m) 0 = if ((7 <=? sc) && (sc <? 39) && (Z.of_nat k =? sc - 7))%bool then seq' else nth k useq' 0).
  { intros k. rewrite EU. unfold bounce_idx. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc. destruct ((7 <=? am_sc am) && (am_sc am <? 39))%bool eqn:E; cbn [andb].
    - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      unfold zset. rewrite nth_zupd, UL'. replace (Nat.ltb (Z.to_nat (am_sc am - 7)) 32) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite andb_true_r. destruct (Nat.eqb k (Z.to_nat (am_sc am - 7))) eqn:EK.
      + apply Nat.eqb_eq in EK. replace (Z.of_nat k =? am_sc am - 7) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      + apply Nat.eqb_neq in EK. replace (Z.of_nat k =? am_sc am - 7) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - reflexivity. }
  split.
  { split; [rewrite EU; unfold bounce_idx; destruct ((7 <=? sc) && (sc <? 39))%bool; [unfold zset; rewrite length_zupd|]; exact UL'|].
    intros u Hux. destruct (In_nth _ _ 0 Hux) as (k & Hk & <-). rewrite NTH. destruct ((7 <=? sc) && (sc <? 39) && (Z.of_nat k =? sc - 7))%bool; [exact Hseq' | apply UB']. }
  intros off w e Hin j Hj.
  pose proof (useq_okb_cell cs off w e Huok Hin) as (O1 & O2 & O3).
  pose proof (proj1 (forallb_forall _ _) Hcells _ Hin) as CK. unfold useq_cell_okb in CK.
  replace (Z.to_nat off + j)%nat with (Z.to_nat (off + Z.of_nat j)) by lia. rewrite NTH.
  destruct (off =? c - 7) eqn:Eoff.
  -
    apply Z.eqb_eq in Eoff. apply andb_prop in CK as [W1 W2]. apply Nat.eqb_eq in W1. apply sv_eqb_sound in W2. subst w e.
    assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r.
    destruct HC as [[R1 R2]|[[R1 R2]|[R1 R2]]]; [|exfalso; lia|exfalso; lia].
    replace ((7 <=? sc) && (sc <? 39) && (Z.of_nat (Z.to_nat off) =? sc - 7))%bool with true
      by (symmetry; apply andb_true_intro; split; [apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia | apply Z.eqb_eq; lia]).
    subst seq'. rewrite ES. destruct b; cbn [E_seq'].
    + rewrite ze_lit. reflexivity.
    + unfold E_seq1. rewrite ze_alu, ze_seq8, ze_lit. cbn [zalu]. unfold zSeq, U.Mal_nt__G1.Mal_nt_I.zSeq in *.
      apply Z.eqb_neq in Hb. change (1 mod 2 ^ 64) with 1. rewrite (Z.mod_small _ (2 ^ 64)) by lia.
      unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
  -
    apply andb_prop in CK as [NO CK]. apply Bool.negb_true_iff in NO.
    assert (NOT : ((7 <=? sc) && (sc <? 39) && (Z.of_nat (Z.to_nat (off + Z.of_nat j)) =? sc - 7))%bool = false).
    { destruct ((7 <=? sc) && (sc <? 39))%bool eqn:E; [|reflexivity]. cbn [andb]. apply Z.eqb_neq. intros EE.
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct HC as [[R1 R2]|[[R1 R2]|[R1 R2]]]; try lia;
        (subst c; apply Bool.andb_false_iff in NO; destruct NO as [NO|NO]; [apply Z.leb_gt in NO | apply Z.ltb_ge in NO]; lia). }
    rewrite NOT. subst useq'. rewrite EU0. destruct b.
    + apply sv_eqb_sound in CK. subst e. rewrite ze_lit. change (0 mod 2 ^ 64) with 0. rewrite le_byte_0.
      destruct (Nat.lt_ge_cases (Z.to_nat (off + Z.of_nat j)) 32) as [Hk|Hk]; [rewrite nth_repeat_lt by exact Hk | rewrite nth_overflow by (rewrite repeat_length; exact Hk)]; reflexivity.
    + destruct e as [z|x|op e1 e2|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try discriminate.
      *
        apply andb_prop in CK as [CK W8]. apply andb_prop in CK as [CK EO]. apply andb_prop in CK as [X1 X2].
        apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in EO. apply Nat.leb_le in W8.
        set (q := Z.to_nat (Z.pos x - 116)).
        assert (EZ : zeval zr1 zl1 (SVar x) = udw (st_unmap_seq s) q).
        { assert (HX : (x = 116 \/ x = 117 \/ x = 118 \/ x = 119)%positive) by lia.
          subst q. destruct HX as [-> |[-> |[-> | ->]]]; [exact ze116 | exact ze117 | exact ze118 | exact ze119]. }
        rewrite EZ. rewrite (le_byte_narrow _ w j Hj) by (pose proof (udw_range (st_unmap_seq s) q); lia).
        rewrite (nth_byte_of_dw q j ltac:(lia)). f_equal. lia.
      *
        destruct op; try discriminate. destruct e1 as [?|x|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try discriminate. destruct e2 as [sh|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try discriminate.
        apply andb_prop in CK as [CK W8]. apply andb_prop in CK as [CK EO]. apply andb_prop in CK as [CK SM]. apply andb_prop in CK as [CK S0]. apply andb_prop in CK as [X1 X2].
        apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in EO. apply Z.leb_le in W8. apply Z.ltb_lt in S0. apply Z.eqb_eq in SM.
        set (q := Z.to_nat (Z.pos x - 116)).
        assert (EZ : zeval zr1 zl1 (SVar x) = udw (st_unmap_seq s) q).
        { assert (HX : (x = 116 \/ x = 117 \/ x = 118 \/ x = 119)%positive) by lia.
          subst q. destruct HX as [-> |[-> |[-> | ->]]]; [exact ze116 | exact ze117 | exact ze118 | exact ze119]. }
        pose proof (udw_range (st_unmap_seq s) q) as UR.
        assert (Hsh : sh < 64) by (pose proof (Z.div_mod sh 8 ltac:(lia)); lia).
        rewrite ze_alu, EZ, ze_lit. cbn [zalu]. rewrite (Z.mod_small _ _ UR).
        assert (S64 : 0 <= sh < 2 ^ 64) by lia. rewrite (Z.mod_small _ _ S64). assert (S6 : 0 <= sh < 64) by lia. rewrite (Z.mod_small _ _ S6).
        rewrite Z.shiftr_div_pow2 by lia. rewrite (le_byte_shift (udw (st_unmap_seq s) q) sh w j ltac:(lia) ltac:(lia) SM Hj).
        assert (T8 : (Z.to_nat (sh / 8 + Z.of_nat j) < 8)%nat) by (pose proof (Z.div_mod sh 8 ltac:(lia)); lia).
        replace (8 * (sh / 8 + Z.of_nat j)) with (8 * Z.of_nat (Z.to_nat (sh / 8 + Z.of_nat j))) by (pose proof (Z.div_pos sh 8); lia).
        rewrite (nth_byte_of_dw q _ T8). f_equal. pose proof (Z.div_mod sh 8 ltac:(lia)). pose proof (Z.div_pos sh 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma ZF_t1lo : ltac2:(tb__ "0|0|
S8dSdcVam;A1Z7A2S111SbcS10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S175A3F_;").
Proof using HMI Hgd Hsc48 Hu. intros Hr. pose proof Hsc48' as SC. unfold F_t1lo. fold nt_sc. constructor; [|constructor]. cbn [zholds zcond]. rewrite ze_sc, ze_lit. change (7 mod 2 ^ 64) with 7. apply Z.ltb_lt. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Hr. lia. Qed.
Lemma ZF_t1hi : ltac2:(tb__ "0|0|
S8bZ27SdcVam;A1A2S111SbcS10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2S174A3F_;").
Proof using HMI Hgd Hsc48 Hu.
  intros Hr. pose proof Hsc48' as SC. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in Hr. unfold F_t1hi. fold nt_sc. constructor; [|constructor; [|constructor]]; cbn [zholds zcond]; rewrite ze_sc, ze_lit.
  - change (38 mod 2 ^ 64) with 38. apply Z.ltb_lt. lia.
  - change (48 mod 2 ^ 64) with 48. apply Z.ltb_lt. lia.
Qed.

Lemma t1_refacts pv nv a1 fs m rhoX tr0 msL md0 : ltac2:(tb__ "0|2|
S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S111SbcS10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2Vfs;A3S0S70S82SbcS1a1S11fA1Vfs;A3S72A3S0S70S82SbcS10eVfs;A3S72A3S0S70SbfS16aVpv;Vnv;Va1;Vfs;A4M0A1S72A3Sc0S86VrhoX;S16aVpv;Vnv;Va1;S78SbcA1A4S74S71S153A1S17eVtr0;S17fVmsL;Vmd0;A2A4M1A4Sc0S86VrhoX;G0G1A4F_;F_;F_;F_;F_;F_;").
Proof using .
  intros Hag ZF Hv Hs Hwf Hsm. apply (smatch_canon rhoX (S_t1_of pv nv a1 []) (S_t1_of pv nv a1 fs) tr0 msL md0 Hsm Hwf eq_refl eq_refl eq_refl eq_refl eq_refl).
  - apply objs_matchb_refl'. cbn [ss_objs S_t1_of objs_t1]. repeat constructor.
  - cbn [ss_facts S_t1_of]. apply Forall_app. split; [exact (ZF_holdsm m rhoX fs Hag Hv Hs ZF)|].
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsm))))))))))) as HF. cbn [ss_facts S_t1_of app] in HF. exact HF.
Qed.
Lemma t1_literalize pv nv fs m rhoX tr0 msL md0 : ltac2:(tb__ "0|2|
S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm;A9VrhoX;A2S0S70SbfS16aVpv;Vnv;SbdSdcVam;A1A1Vfs;A4M0A1S72A3Sc0S86VrhoX;S16aVpv;Vnv;S171Vfs;A4S74S71S153A1S17eVtr0;S17fVmsL;Vmd0;A2A4M1A4Sc0S86VrhoX;G0G1A4F_;F_;F_;").
Proof using HMI Hgd Hsc48 Hsp Hu.
  intros Hag Hwf Hsm. pose proof Hsc48' as SC.
  destruct Hsm as (_ & Hpc0 & Hpend & Hhalt & Hrom0 & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  split; [exact Hwf|]. split; [exact Hpc0|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom0|]. split; [exact Hro|].
  split; [|exact (conj Hf (conj Hc (conj Hv (conj Hm Hfa))))].
  intros r Hr0. cbn [fst snd cfg_ms cfg_model]. rewrite (Hr r Hr0). unfold reg_sv.
  replace (bv_unsigned r =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). cbn [ss_regs S_t1_of].
  assert (E11 : eval rhoX nt_sc = eval rhoX (SLit sc)).
  { rewrite (EVq m rhoX nt_sc Hag eq_refl eq_refl), ze_sc. cbn [eval]. reflexivity. }
  pose proof (bv_unsigned_in_range 5 r) as RR. change (bv_modulus 5%N) with 32 in RR.
  set (k := Z.to_nat (bv_unsigned r)). assert (Hk : (k < 32)%nat) by lia.
  unfold regs_t1.
  do 11 (destruct k as [|k]; [reflexivity|]). destruct k as [|k]; [cbn [nth]; first [exact E11 | symmetry; exact E11]|]. reflexivity.
Qed.

Lemma pvnv_facts pv nv : ltac2:(tb__ "0|2|
S81S6eSbaSbaA2S74SbaSbaVpv;Vnv;A4S170A3S1S0S70S82S4bS53S6fS4bS57S5cVpv;Vnv;Sd8P85A1Sd8P86A1A5M0S6fS4bS55S78S4bA1A3A3M1A3S72A3S1S0S70S15aS6fSbbS16cVpv;Vnv;A2S6fSbbS16fS78SbbA1A3A3S112S4bSbbS4fG1A4A2S72A3S1S5bVam;G0A2S1S0S70SbfS16aVpv;Vnv;SbdSdcVam;A1A1S78SbcA1A4A1S72A3S1S0S70SbfS16aVpv;Vnv;S171S175A4A1S72A3S0S70SbfS16aVpv;Vnv;S171S174A4A1S72A3A2A2A2A2A2F_;").
Proof using .
  intros [E|[E|[]]]; injection E as <- <-; (split; [reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [exact I|]);
    (split; [|split; vm_compute; reflexivity]).
  all: unfold S_t1_of, swf; cbn -[sc]; reflexivity.
Qed.

Section Mid.
Variables (P1 dsCP1 : list od).
Hypothesis P1_ent : ltac2:(tb__ "0|0|
S4bS81S4bR1VP1;A3S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S81S4bR2VdsCP1;A3A2F_;Fd;").
Hypothesis P1_okC : ltac2:(tb__ "0|0|
S4bS81S4bR1VdsCP1;A3S1S81S4bR2VP1;A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcR2AaS157R2A1A2A2F_;Fd;").
Hypothesis P1_locs : ltac2:(tb__ "0|1|
S9cS81S9cR1S75S9cS100S6fS9cSa3S8cSa8S8fZ8SdcVam;A1A2A2A1S78S9cA1A3A3A3S4S81S9cR2S11bVg;A1A3S3S4bS4bS1S81S4bR1VdsCP1;A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M0A2S8dG0S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;").
Hypothesis P1_X2 : ltac2:(tb__ "0|0|
S70S71S6eS6eS6aS73A2SbaA2A1S4bS81S4bR1S195R3R2A2A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP1;A3F_;Fd;Fcs;Fb;").
Hypothesis P1_XT2n : ltac2:(tb__ "0|0|
S4bS81S4bR1SfeSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP1;A3F_;Fd;").
Hypothesis P1_XT : ltac2:(tb__ "0|0|
S4bS81S4bR1SffSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP1;A3F_;Fd;").

Definition Q2 (pv nv : sv) (c : Z) : assn := ltac2:(tb__ "0|3|
S10bS3S70S70S3S71S6eS6eS6aS73A2SbaA2M0A1M1G1S3Sd9Q40A1S6cSd9Q8A1A1F_;M2G2S3Sc2Sc2S1S194Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;S75S4bS195R4R3A2VP1;A3R2AcS1S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9R1A2S1S0S70S60R3A1S72A3S1S0S70S82G0S198Vc;R4A2R3A3S72A3S1S0S70S93S18Vs;A1ZffA2R4A3S159S86VK;S16bVpv;Vnv;SfdA3R1R5A5A2A2A2A2A2LrhoX;A2Lm2;A2Lcs;A2Lb;A2Lw;").

Lemma X_T2n_P2 b cs : ltac2:(tb__ "0|0|
S4bS81S4bR1SfeSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5S195Vb;Vcs;A2A3F_;Fd;").
Proof using Hgd Hsc48 Kc md rho tr.
  clear HKc Hsm_pre EmW Evm P1_ent P1_okC P1_locs P1_X2 P1_XT2n P1_XT. intros d Hd. unfold fshape in *.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|];
    cbn in Hd; (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; od_pw; try (rewrite Hfh; discriminate).
Qed.
Lemma X_T_P2 b cs : ltac2:(tb__ "0|0|
S4bS81S4bR1SffSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5S195Vb;Vcs;A2A3F_;Fd;").
Proof using Hgd Hsc48 Kc md rho tr.
  clear HKc Hsm_pre EmW Evm P1_ent P1_okC P1_locs P1_X2 P1_XT2n P1_XT. intros d Hd. unfold fshape in *.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|];
    cbn in Hd; (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; od_pw; try (rewrite Hfh; discriminate).
Qed.

Lemma Q2_triple pv nv c : ltac2:(tb__ "0|0|
S81S6eSbaSbaA2S74SbaSbaVpv;Vnv;A4S170A3S104Vc;A1VTR;S1d0Vpv;Vnv;Vc;A3S1a2S86S87Vrho;S18cS86S115S18aVX;VU;S192Vsr;VL;A2VKc;A7A4A2F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs P1_XT P1_ent P1_locs P1_okC TR_ex TR_pure.
  intros Hpv HC. unfold Q2.
  apply TR_ex; intros b. apply TR_ex; intros cs. apply TR_ex; intros m2. apply TR_ex; intros rhoX.
  apply TR_pure; intros RID. apply TR_pure; intros Hag. apply TR_pure; intros Huok. apply TR_pure; intros Hcell. apply TR_pure; intros Hb.
  destruct T2pack_fs as (Cq & Nwf & Nds & Nv & Fv & Fs). destruct (Cq pv nv Hpv) as (Hrun2 & Hm2 & Hwf2).
  refine (T2_seg (S_t2_of pv nv fshape) (dsT fshape) m2 Hrun2 eq_refl ltac:(unfold Pos.le; cbn; discriminate) _ _ rhoX Hag).
  intros SF rhoT tr0 msF md0 HagT HsmT HKw HOK.
  destruct (HKc _ _ HKw) as (HKc' & -> & ->).
  destruct (leaf_okb_sound SF (dsT fshape) HOK) as (Hobjs & _).
  apply (finish3 (t1_P2 b cs ++ P1) m2 rhoT SF _ (dsT fshape) (dsCT fshape) (t1_P2 b cs ++ dsCP1) msF RID HagT HsmT HKw HOK Hobjs ent_T).
  - intros d Hd. apply in_app_iff in Hd as [Hd|Hd]; [right; apply in_app_iff; left; exact Hd | ].
    destruct (P1_ent d Hd) as [X0|X0]; [left; exact X0 | right; apply in_app_iff; right; exact X0].
  - intros d Hd. apply Forall_app. split; [exact (X_T_P2 b cs d Hd) | exact (P1_XT d Hd)].
  - intros d Hd. apply in_app_iff in Hd as [Hd|Hd].
    + destruct (okC_T d Hd) as [A B]. split; [apply in_app_iff; left|split; [exact A | exact B]].

      clear - Hd. unfold fshape in *. destruct (st_free_meta_head s); [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd |- *; tauto.
    + apply in_app_iff in Hd as [Hd|Hd].
      * split; [apply in_app_iff; right; apply in_app_iff; left; exact Hd|].
        destruct Hd as [<-|[<-|[]]]; [exact (seq_ok_m b Hb) | exact (useqL_ok_m b c cs Hb HC Huok Hcell)].
      * destruct (P1_okC d Hd) as (A & B & C'). split; [apply in_app_iff; right; apply in_app_iff; right; exact A | split; [exact B | exact C']].
  - intros l Hl. unfold LOCS in Hl. pose proof Hctx as HCX.
    assert (IN2 : forall d, In d (t1_P2 b cs) -> In d (dsCT fshape ++ t1_P2 b cs ++ dsCP1)) by (intros d Hd; apply in_app_iff; right; apply in_app_iff; left; exact Hd).
    assert (IN1 : forall d, In d dsCP1 -> In d (dsCT fshape ++ t1_P2 b cs ++ dsCP1)) by (intros d Hd; apply in_app_iff; right; apply in_app_iff; right; exact Hd).
    assert (INT : forall d, In d (dsCT fshape) -> In d (dsCT fshape ++ t1_P2 b cs ++ dsCP1)) by (intros d Hd; apply in_app_iff; left; exact Hd).
    assert (USEQ : forall k, 0 <= k < 32 -> exists d, In d (dsCT fshape ++ t1_P2 b cs ++ dsCP1) /\ dlo d <= loc_addr L (LCtx (CTX_unmap_seq + k)) < dhi d).
    { intros k Hk. exists (OD_useqL cs). split; [apply IN2; right; left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_unmap_seq. lia. }
    apply in_app_iff in Hl as [Hl|Hl]; [|destruct (locs_T l ltac:(apply in_app_iff; right; exact Hl)) as (d & Hd & R); exists d; split; [exact (INT d Hd) | exact R]].
    apply in_app_iff in Hl as [Hl|Hl]; [|destruct (locs_T l ltac:(apply in_app_iff; left; exact Hl)) as (d & Hd & R); exists d; split; [exact (INT d Hd) | exact R]].
    apply in_app_iff in Hl as [Hl|Hl].
    + apply in_app_iff in Hl as [Hl|Hl].
      * destruct (P1_locs l Hl) as [Hg | (d & Hd & R)]; [|exists d; split; [exact (IN1 d Hd) | exact R]].
        destruct (locs_T l ltac:(apply in_app_iff; left; exact Hg)) as (d & Hd & R). exists d. split; [exact (INT d Hd) | exact R].
      * unfold seq_locs_b in Hl. destruct (st_seq s =? 255).
        -- unfold seq_locs in Hl. destruct Hl as [<-|Hl].
           ++ exists (OD_seq (E_seq' b)). split; [apply IN2; left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_seq. lia.
           ++ apply in_map_iff in Hl as (k & <- & Hk). apply in_seq in Hk. apply USEQ. lia.
        -- destruct Hl as [<-|[]]. exists (OD_seq (E_seq' b)). split; [apply IN2; left; reflexivity|]. unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_seq. lia.
    + unfold rec_locs in Hl. unfold bounce_idx in Hl. destruct ((7 <=? am_sc am) && (am_sc am <? 39))%bool eqn:E; [|destruct Hl].
      apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct Hl as [<-|[]]. apply USEQ. lia.
Qed.

Theorem mid_triple pv nv m1 rhoB : ltac2:(tb__ "0|0|
S81S6eSbaSbaA2S74SbaSbaVpv;Vnv;A4S170A3S194Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VP1;Vm1;AcS11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vm1;A9VrhoB;A2VTR;S159S86VK;S16aVpv;Vnv;S171S78SbcA1A4VrhoB;A4S1a2S86S87Vrho;S18cS86S115S18aVX;VU;S192Vsr;VL;A2VKc;A7A4A2F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs P1_X2 P1_XT P1_XT2n P1_ent P1_locs P1_okC TR_conseq TR_ex TR_pure TR_seq.
  intros Hpv RID Hag. pose proof Hsc48' as SC.
  destruct (pvnv_facts pv nv Hpv) as (Hdsl & Hdsm & Cg & Wlit & Wlo & Whi).
  destruct (T1pack pv nv Hpv) as (Rlit & Rlo & Rhi).

  assert (CASE : exists c S1, CREL c /\ t1_run_okb pv nv c S1 = true /\ ss_lenient S1 = false /\ (200 <= ss_next S1)%positive /\
            forall tr0 msL md0, smatch segsU rhoB (S_t1_of pv nv nt_sc []) (tr0, mkCfg msL md0) -> smatch segsU rhoB S1 (tr0, mkCfg msL md0)).
  { assert (NX : forall a fs, (200 <= ss_next (S_t1_of pv nv a fs))%positive) by (intros; cbn [ss_next S_t1_of]; unfold NXA, Pos.le; cbn; discriminate).
    destruct (Z.lt_ge_cases sc 7) as [Hlo|Hge].
    - exists 0, (S_t1_of pv nv nt_sc F_t1lo). split; [right; left; split; [exact Hlo | reflexivity]|]. split; [exact Rlo|]. split; [reflexivity|]. split; [apply NX|].
      intros tr0 msL md0 Hsm. exact (t1_refacts pv nv nt_sc F_t1lo m1 rhoB tr0 msL md0 Hag (ZF_t1lo Hlo) eq_refl eq_refl Wlo Hsm).
    - destruct (Z.lt_ge_cases sc 39) as [Hmid|Hhi].
      + assert (RG : 7 <= sc <= 38) by (clear Rlit Rlo Rhi; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *; lia).
        exists sc, (S_t1_of pv nv (SLit sc) []). split; [left; split; [exact RG | reflexivity]|]. split; [exact (Rlit sc RG)|]. split; [reflexivity|]. split; [apply NX|].
        intros tr0 msL md0 Hsm. exact (t1_literalize pv nv [] m1 rhoB tr0 msL md0 Hag Wlit Hsm).
      + exists 47, (S_t1_of pv nv nt_sc F_t1hi). split; [right; right; split; [exact Hhi | reflexivity]|]. split; [exact Rhi|]. split; [reflexivity|]. split; [apply NX|].
        intros tr0 msL md0 Hsm. exact (t1_refacts pv nv nt_sc F_t1hi m1 rhoB tr0 msL md0 Hag (ZF_t1hi Hhi) eq_refl eq_refl Whi Hsm). }
  destruct CASE as (c & S1 & HC & Hrun & HS1l & HS1n & RESTATE).
  eapply TR_conseq; [| intros w Hw; exact Hw | ].
  { intros [tr0 [msL md0]] [Hsm HKw]. exact (conj (RESTATE tr0 msL md0 Hsm) HKw : SymSoundR.SP segsU K S1 rhoB (tr0, mkCfg msL md0)). }
  eapply TR_seq; [|exact (Q2_triple pv nv c Hpv HC)].
  apply (T1_seg pv nv c S1 P1 m1 Hrun HS1l HS1n RID (P1_X2) (Q2 pv nv c)); [|exact Hag].

  intros b cs m2 rhoX Lfacts nx tr0 msL md0 RID2 Hag2 Huok Hcell Hsem Hbz Hnx Hsm2 HKw.
  exists b, cs, m2, rhoX. split; [exact RID2|]. split; [exact Hag2|]. split; [exact Huok|]. split; [exact Hcell|]. split; [exact (seq_b_of b Hbz)|].
  split; [|exact HKw].
  apply (link2 pv nv (t1_P2 b cs ++ P1) m2 rhoX Lfacts nx tr0 msL md0 Hpv RID2 Hag2
           (fun d Hd => proj2 (Forall_app _ _ _) (conj (X_T2n_P2 b cs d Hd) (P1_XT2n d Hd))) Hnx Hsm2 Cg Hdsl Hdsm).
Qed.
End Mid.

Definition E_usage : sv := ltac2:(tb__ "0|0|
SbeS1a4Sd8P97A1SbeS1a9SbeS1acSd8P87A1SbdZffffffffffffffffA1A3SbdZffffffffffffffe0A1A3A3").
Lemma ze_usage : ltac2:(tb__ "0|0|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S102A3S92Sf4Vs;Vam;A2S8cScVam;A1Z1A2A2A3").
Proof using HMI HU Hgd Hml Hsc48 Hsp Hu.
  unfold E_usage. rewrite !ze_alu, ze151, ze135, !ze_lit. cbn [zalu].
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
Lemma okC_usage : ltac2:(tb__ "0|1|
S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS5fS102A1M0AaS157G0A1A2").
Proof using Erd Ewok HIr HMI HP13 HP13w HU Hgd Hgd_holds Hml Hsc48 Hsp Hu mW. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|]. rewrite ze_usage, (usage_of_m sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)). rewrite Z.eqb_refl. reflexivity. Qed.
Lemma locs_usage rest : ltac2:(tb__ "0|1|
S9cS81S9cR1S6fS9cSa3S8cSa8S8fZ8SdcVam;A1A2A2A1S78S9cA1A3A3S3S4bS4bS1S81S4bR1S6fS4bS5fS102A1Vrest;A3A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M0A2S8dG0S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fl;").
Proof using HMI Hgd Hsc48 rho.
  intros l [<-|[]]. exists (OD_usage E_usage). split; [left; reflexivity|]. pose proof Hctx as HCX.
  unfold U.Mal_nt__G1.Mal_nt_D.dhi. cbn [U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.dsz loc_addr]. rewrite HCX. unfold CTX_usage. lia.
Qed.

Lemma ZF_pre (extra : list sprop) : ltac2:(tb__ "0|2|
S111SbcS10dSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8A2M0Vextra;A3S111SbcG0S75SbcS75SbcS6fSbcS179S6fSbcS177S78SbcA1M1A3A3S75SbcS17aS6fSbcSc4Sc5S1adS17bSbdZ0A1A3A1G1A3A3A3S75SbcVextra;S178A3A3A3F_;").
Proof using HMI HP12 Hall Hdepth Hgd Hml Hsc48 Hsp Hu.
  intros HE. apply Forall_app. split; [|apply Forall_app; split; [exact HE | apply ZF_base]].
  constructor; [apply ZF_freeable|]. constructor; [apply (ZF_all Hall)|]. apply Forall_app. split; [apply (ZF_sc48 Hsc48)|].
  constructor; [apply (ZF_maplenN0 Hml) | constructor].
Qed.

Lemma Xlive_new Lf : ltac2:(tb__ "0|0|
S4bS81S4bR1S19cVLf;A1A3S111S4bS147Vs;VL;Vg;Vam;R2A5S197A3F_;Fd;").
Proof using . clear HKc Hsm_pre EmW Evm. intros d [<-|[<-|[]]]; cbn; od_pw. Qed.

Definition Q1 (dsP : list od) : assn := ltac2:(tb__ "0|1|
S10bS3SbaSbaS3SbaSbaS3Sd9Q40A1S6cSd9Q8A1A1F_;M0G0S3Sc2Sc2S1S81S6eSbaSbaA2S74SbaSbaR4R3A4S170A3S1S194Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vms;VmW;VdsP;R2AcS1S11eSe7Vs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9R1A2S159S86VK;S16aR4R3S171S78SbcA1A4R1R5A5A2A2A2LrhoB;A2Lm1;A2Lnv;A2Lpv;A2Lw;").

Lemma nr_t2new : ltac2:(tb__ "0|0|
S4bS81S4bR1SfeSfdA1A3S148Vs;Vam;R2A3F_;Fd;").
Proof using .
  clear HKc Hsm_pre EmW Evm. intros d Hd. unfold fshape in Hd.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd;
    (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; try exact I; rewrite Hfh; discriminate.
Qed.
Lemma nr_T : ltac2:(tb__ "0|0|
S4bS81S4bR1SffSfdA1A3S148Vs;Vam;R2A3F_;Fd;").
Proof using .
  clear HKc Hsm_pre EmW Evm. intros d Hd. unfold fshape in Hd.
  destruct (st_free_meta_head s) as [fm|] eqn:Hfh; [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd;
    (repeat (destruct Hd as [<-|Hd])); try destruct Hd; cbn; try exact I; rewrite Hfh; discriminate.
Qed.
Lemma X_generic_t2new (P : list od) : ltac2:(tb__ "0|2|
S4bS4bS81S4bR2S6fS4bS52SbdZ0A1A1S6fS4bS52Sd8Pa0A1M0A1S6fS4bS4eS50S77G0Sd8Pa2A1M1A4S6fS4bS4eS50S77Sd8Pa1A1G1A4S6fS4bS4eS59S77Sd8Pa3A1Sd8Pa4A1A4S78S4bA1A3A3A3A3A3A3S148Vs;Vam;R3A3S81S4bR3VP;A3S147Vs;VL;Vg;Vam;R5R4A6F_;F_;F_;Fe;Fd;S4bS81S4bR1SfeSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP;A3F_;Fd;F_;").
Proof using Hdepth Hgd Hsc48 Hsp.
  intros H d Hd. apply Forall_forall. intros e He. apply H; [| exact (nr_t2new d Hd) | exact He].
  unfold fshape in Hd. destruct (st_free_meta_head s); [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd; cbn; tauto.
Qed.
Lemma X_generic_T (P : list od) : ltac2:(tb__ "0|2|
S4bS4bS81S4bR2S6fS4bS4eS51S72Sd8PcA1M0G0A4S6fS4bS55S6fS4bS52G0A1S6fS4bS4eS51S72Sd8Pa0A1M1G1A4S6fS4bS52G1A1S6fS4bS4eS50S77G0G0A4S6fS4bS4eS51S72Sd8Pa1A1G1A4S6fS4bS4eS50S77G0Sd8Pa2A1A4S6fS4bS4eS59S77Sd8Pa3A1G0A4S78S4bA1A3A3A3A3A3A3A3A3A3A3S148Vs;Vam;R3A3S81S4bR3VP;A3S147Vs;VL;Vg;Vam;R5R4A6F_;F_;F_;Fe;Fd;S4bS81S4bR1SffSfdA1A3S111S4bS147Vs;VL;Vg;Vam;R2A5VP;A3F_;Fd;F_;").
Proof using Hdepth Hgd Hsc48 Hsp.
  intros H d Hd. apply Forall_forall. intros e He. apply H; [| exact (nr_T d Hd) | exact He].
  unfold fshape in Hd. destruct (st_free_meta_head s); [destruct (sptr_eqb ftQ fmQ)|]; cbn in Hd; cbn; tauto.
Qed.

Lemma variant_generic (S0 : sstate) (L0 : list leaf) (dsP1 dsCP1 : list od) : ltac2:(tb__ "0|5|
S0S70S82S165S165S168S70Lx;S169R1A1S77S1a0VdsP1;S166R1A1A2S77S77S77S77S77X168x7Llf;VL0;A3S72A3S0S70S82S4bS53VdsP1;A3S72A3S4bS81S4bR1VdsP1;A3M0S5bVam;R2A2F_;Fd;S14cVs;VL;Vg;Vam;VdsP1;A5S4bS81S4bR1S197A3S111S4bS147Vs;VL;Vg;Vam;R2A5VdsP1;A3M1F_;Fd;S0S70Sc9VS0;A1S77A3S1b1Pc8ScaVS0;A1A2S0S6cS71S165A1M2A1S167S86U258S176VS0;S72A5S6dG2VL0;A2A3S4bG0S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S81S4bR2VdsCP1;A3A2F_;Fd;S4bS81S4bR1VdsCP1;A3M3S1S81S4bR2VdsP1;A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcR2AaS157R2A1A2A2F_;Fd;S9cS81S9cR1S75S9cS100S6fS9cSa3S8cSa8S8fZ8SdcVam;A1A2A2A1S78S9cA1A3A3A3S4S81S9cR2S11bVg;A1A3S3S4bS4bS1G3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M4A2S8dG4S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2A2F_;Fl;S70S71S6eS6eS6aS73A2SbaA2A1S4bS81S4bR1S195R3R2A2A3G1F_;Fd;Fcs;Fb;S4bS81S4bR1SfeSfdA1A3G1F_;Fd;S4bS81S4bR1SffSfdA1A3G1F_;Fd;VTR;S159S86VK;VS0;VrhoW;A4S1a2S86S87Vrho;S18cS86S115S18aVX;VU;S192Vsr;VL;A2VKc;A7A4A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hall Hdepth Hgd Hgd_holds Hm_sct Hml Hok Hreach Hrom Hsc48 Hsm_pre Hsp Hsp_high Hu Hzs TR_conseq TR_ex TR_pure TR_seq.
  intros C Hds Hcond Hpw Xnew Hlen Hnx Hrun Hent HokC Hlocs X2 XT2n XT.
  assert (DSP : Forall DS dsP1) by (apply Forall_forall; intros d Hd; split; [exact (proj1 (forallb_forall _ _) Hds d Hd) | exact (Hcond d Hd)]).
  eapply TR_seq.
  - apply (segRm mW CUTSP 600 S0 L0 (Q1 dsP1) rhoW Hlen Hnx Hrun (agrees_refl rhoW)).
    intros Lf rho'' [tr0 [msL md0]] Hin Hag HSP.
    pose proof (proj1 (forallb_forall _ _) C Lf Hin) as CL. cbn beta in CL.
    destruct (lf_reason Lf); try discriminate CL.
    destruct (prefix_link dsP1 (lf_state Lf) rho'' tr0 msL md0 CL DSP Hpw Hcond Xnew (Xlive_new (lf_state Lf)) I Hag HSP)
      as (m1 & rhoB & RID & HagB & HSPB).
    unfold prefix_leaf_okb in CL.
    exists (gl_pv (lf_state Lf)), (gl_nv (lf_state Lf)), m1, rhoB. split; [|split; [exact RID | split; [exact HagB | exact HSPB]]].
    repeat (apply andb_prop in CL as [CL ?X]). apply pvnv_okb_sound. assumption.
  - unfold Q1. apply TR_ex; intros pv. apply TR_ex; intros nv. apply TR_ex; intros m1. apply TR_ex; intros rhoB.
    apply TR_pure; intros Hpv. apply TR_pure; intros RID. apply TR_pure; intros HagB.
    exact (mid_triple dsP1 dsCP1 Hent HokC Hlocs X2 XT2n XT pv nv m1 rhoB Hpv RID HagB).
Qed.

Lemma aidx_range_n : ltac2:(tb__ "0|1|
S1S8bZ0S15Se5Vs;Vg;Vam;A3A1M0A2S8bG0Z1fA2A2").
Proof using HMI Hgd Hsc48 Hsp Hu. pose proof (inv_groups HI nQ anQ nQ_used) as ((M1 & M2 & _) & _). lia. Qed.
Lemma zA8_aidx : ltac2:(tb__ "0|0|
S0S6aS90Sf7Vs;VL;Vg;Vam;Vrd0;A5Z20A2S15Se5Vs;Vg;Vam;A3A1A3").
Proof using Erd Ewok HMI HXz Hgd Hsc48 Hsp Hu bv0.
  pose proof (aidx_cell_In X (Some (g, i)) U s HI HXr nQ anQ nQ_used) as CI.
  assert (CH : MallocInv.cell_holds L bv0 (Zones2.aidx_cell anQ)) by exact (proj1 (Forall_forall _ _) (proj1 (proj2 (proj1 HreprO))) _ CI).
  destruct grp_byte_rd as [W R]. pose proof aidx_range_n as AR. pose proof zA8_range as A8.
  assert (AD : loc_addr L (LMem (padd (am_mem anQ) 8)) = zNm + 8) by (unfold zNm, U.Mal_nt__G1.Mal_nt_I.zNm, addr_of, loc_addr; destruct (am_mem anQ); cbn [padd]; lia).
  assert (BV : bv0 (zNm + 8) = Some zA8).
  { unfold bv0, byteview_of. pose proof RN as R'. pose proof (ceiling_small L).
    replace ((0 <=? zNm + 8) && (zNm + 8 <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite W, R. cbn. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8%N) with 256. lia. }
  unfold Zones2.aidx_cell, MallocInv.cell_holds in CH. destruct (am_maplen anQ =? 0); cbn [mc_loc mc_val mc_w] in CH; rewrite AD in CH.
  - destruct CH as (b & Hb & Eb). rewrite BV in Hb. injection Hb as <-. exact Eb.
  - specialize (CH 0%nat ltac:(lia)). cbn [Z.of_nat] in CH. rewrite Z.add_0_r, BV in CH. injection CH as ->.
    cbn [sval_num]. unfold le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite !Z.mod_small; lia.
Qed.
Definition E_act : sv := ltac2:(tb__ "0|0|
ScbS1a5SbdZ2A1Sc3S77Q8Sd8P9eA1A3A3").
Definition E_avN : sv := ltac2:(tb__ "0|0|
SbeS1a6Sc3S72Q20Sd8P9bA1A3SbeS1a4S101SbdN1A1A3A3").
Definition E_frN : sv := ltac2:(tb__ "0|0|
SbeS1a6Sc3S72Q20Sd8P9bA1A3ScbS1abSbdZ0A1S101A3A3").
Lemma ze_act : ltac2:(tb__ "0|1|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S101A3S110S90S8eZ2M0S8cS15Se5Vs;Vg;Vam;A3A1Z1A2A2S8eG0Z20A2A2A1A3").
Proof using Erd Ewok HMI HXz Hgd Hsc48 Hsp Hu bv0.
  unfold E_act. rewrite ze_aluw, ze_lit, ze_ext, ze158. change (Z.of_N 8) with 8. pose proof zA8_range as A8. pose proof aidx_range_n as AR.
  rewrite (Z.mod_small zA8 (2 ^ 8)) by lia. cbn [zalu]. change ((2 mod 2 ^ 64) mod 2 ^ 32) with 2.
  rewrite (Z.mod_small zA8 (2 ^ 32)) by lia. rewrite zA8_aidx. rewrite Z.shiftl_mul_pow2 by lia. f_equal. f_equal. change 2 with (2 ^ 1) at 1. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma ze_sx155 : ltac2:(tb__ "0|1|
S1S8bZ0S10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Sc3S72Q20Sd8P9bA1A3A3M0A2S0S6aS90G0S8eZ2Z20A2A2S17Se5Vs;Vg;Vam;A3A1A3A2").
Proof using HMI Hgd Hsc48 Hu. rewrite ze_ext, ze155. change (Z.of_N 32) with 32. pose proof RN as R'. fold (sx32 (am_freed anQ)). split; [apply sx32_range; lia | apply sx32_mod32; lia]. Qed.
Lemma ze_avN : ltac2:(tb__ "0|1|
S0S6aS90S10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S105A3S8eZ2Z20A2A2S99S17Se5Vs;Vg;Vam;A3M0A1S19S15G0A1A1A2A3").
Proof using Erd Ewok HMI HXz Hgd Hsc48 Hsp Hu bv0.
  unfold E_avN. rewrite ze_alu. cbn [zalu]. rewrite ze_alu, ze_act, ze_lit. cbn [zalu]. pose proof RN as R'. pose proof aidx_range_n as AR. destruct ze_sx155 as [S0 S1].
  pose proof (Z.mod_pos_bound (2 ^ (am_aidx anQ + 1)) (2 ^ 32) ltac:(lia)) as MB.
  rewrite (Z.mod_mod _ (2 ^ 64)) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
  rewrite (Z.mod_small (zeval _ _ _) (2 ^ 64)) by (split; [exact S0 | apply zeval_range; reflexivity]).
  unfold ones. exact (act_avail_val (am_freed anQ) (am_aidx anQ) _ ltac:(lia) AR S0 S1).
Qed.
Lemma ze_frN : ltac2:(tb__ "0|1|
S0S6aS90S10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8S106A3S8eZ2Z20A2A2S9aS17Se5Vs;Vg;Vam;A3M0A1S19S15G0A1A1A2A3").
Proof using Erd Ewok HMI HXz Hgd Hsc48 Hsp Hu bv0.
  unfold E_frN. rewrite ze_alu. cbn [zalu]. rewrite ze_aluw, ze_act, ze_lit. cbn [zalu]. pose proof RN as R'. pose proof aidx_range_n as AR. destruct ze_sx155 as [S0 S1].
  change ((0 mod 2 ^ 64) mod 2 ^ 32) with 0.
  rewrite (Z.mod_small (zeval _ _ _) (2 ^ 64)) by (split; [exact S0 | apply zeval_range; reflexivity]).
  rewrite (Z.mod_small (sx32 (_ mod 2 ^ 32)) (2 ^ 64)) by (apply sx32_range; apply Z.mod_pos_bound; lia).
  unfold ones. exact (act_freed_val (am_freed anQ) (am_aidx anQ) _ ltac:(lia) AR S0 S1).
Qed.

Section RingGen.
Hypothesis HnS : ltac2:(tb__ "0|0|
S3S8S8S1S0S6cS8A1SbVam;A1S6dS8R1A2A3S2S0S8R1Vg;A3A1A2Ln;A2").
Lemma RG : ltac2:(tb__ "0|3|
S3S8S8S3S8S8S3SaSaS3SaSaS1S0S6cS8A1M0SbVam;A1S6dS8R3A2A3S1S2S0S8R3Vg;A3A1S1S0G0S13Vam;A1S6dS8R4A2A3S1S2S0S8R4Vg;A3A1S1Sa1VX;Vs;R4R2A4S1Sa1VX;Vs;R3R1A4S1S0S6aSeR1A1SdcVam;A1M1A3S1S0S6aSeR2A1G1A3S1S0S6cS9A1M2S9dVs;R4A2S6dS9S10R2A1A2A3S1S0G2S9dVs;R3A2S6dS9S10R1A1A2A3S1S0S8SdfVg;Vam;A2R3A3S1S0S8Se0Vg;Vam;A2R4A3S1S0SaSe5Vs;Vg;Vam;A3R1A3S0SaSeaVs;Vg;Vam;A3R2A3A2A2A2A2A2A2A2A2A2A2A2A2A2Lan;A2Lap;A2Ln;A2Lp;A2").
Proof using HMI Hgd HnS Hu rho. destruct HnS as (n & En & Hng). destruct (next_facts n En Hng) as (p & ap & an & R). exists p, n, ap, an. split; [exact En|]. split; [exact Hng|]. exact R. Qed.
Lemma HnN : am_next am <> None. Proof using HnS. destruct HnS as (n & En & _). rewrite En. discriminate. Qed.
Lemma HpN : am_prev am <> None. Proof using HMI Hgd HnS Hu rho. destruct RG as (p & n & ap & an & _ & _ & Ep & _). rewrite Ep. discriminate. Qed.
Lemma nQ_ng : nQ <> g. Proof using HMI Hgd HnS Hu rho. destruct RG as (p & n & ap & an & En & Hng & _ & _ & _ & _ & _ & _ & _ & _ & EnQ & _). rewrite EnQ. exact Hng. Qed.
Lemma pQ_ng : pQ <> g. Proof using HMI Hgd HnS Hu rho. destruct RG as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & _ & _ & _ & EpQ & _). rewrite EpQ. exact Hpg. Qed.
Lemma zNx_n : ltac2:(tb__ "0|0|
S0S6aSf8VL;Vam;A2S116VL;SdfVg;Vam;A2A2A3"). Proof using HMI Hgd HnS Hu rho. destruct RG as (p & n & ap & an & En & _ & _ & _ & _ & _ & _ & _ & _ & _ & EnQ & _). rewrite EnQ. exact (zNx_eq n En). Qed.
Lemma zPv_p : ltac2:(tb__ "0|0|
S0S6aSfaVL;Vam;A2S116VL;Se0Vg;Vam;A2A2A3"). Proof using HMI Hgd HnS Hu rho. destruct RG as (p & n & ap & an & _ & _ & Ep & _ & _ & _ & _ & _ & _ & _ & _ & EpQ & _). rewrite EpQ. exact (zPv_eq p Ep). Qed.
Lemma nQ_not_fq : ltac2:(tb__ "0|1|
S1S2S0S8Se1Vs;Vg;A2SdfVg;Vam;A2M0A3A1S2S0S8Se3Vs;Vg;A2G0A3A1A2").
Proof using HMI Hgd HnS Hsc48 Hu rho. destruct (used_not_fq nQ anQ nQ_used nQ_ng) as [A B]. split; intros E; [apply A | apply B]; symmetry; exact E. Qed.
Lemma pQ_not_fq : ltac2:(tb__ "0|1|
S1S2S0S8Se1Vs;Vg;A2Se0Vg;Vam;A2M0A3A1S2S0S8Se3Vs;Vg;A2G0A3A1A2").
Proof using HMI Hgd HnS Hsc48 Hu rho. destruct (used_not_fq pQ apQ pQ_used pQ_ng) as [A B]. split; intros E; [apply A | apply B]; symmetry; exact E. Qed.

Definition an2 : ameta := ltac2:(tb__ "0|6|
S25S6dS8Se0Vg;Vam;A2M0A2S70S6cS8A1L_;S1aSdfVg;Vam;A2M1G0A2M2S6dS8G1A2M3SbSe5Vs;Vg;Vam;A3M4A1X70x2S70SaL_;G2S25S13SeaVs;Vg;Vam;A3M5A1G3G5A3G4X70x2A3").
Lemma MT_dq_nQ : ltac2:(tb__ "0|0|
S0S6cS9A1S9dS180Vs;Vg;Vam;A3SdfVg;Vam;A2A2S6dS9S10S17dA1A2A3").
Proof using HMI Hgd HnS Hu rho.
  destruct RG as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & _ & _ & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
  unfold an2. rewrite EnQ, EpQ, EanQ, EapQ. rewrite (MT_dq_n s g am p n ap an Ep En Hng Mp Mn). unfold an1.
  destruct (sptr_eqb n p); reflexivity.
Qed.
Lemma an2_fields : ltac2:(tb__ "0|4|
S1S0S8S16S17dA1S16Se5Vs;Vg;Vam;A3M0A1A3S1S0S6aSb0S17dA1Sb0G0A1A3S1S0S6aS22S17dA1S22G0A1A3S1S0S6aS17S17dA1S17G0A1A3S1S0S6aS15S17dA1S15G0A1A3S1S0S6cS8A1M1S13S17dA1S6dS8Se0Vg;Vam;A2M2A2A3S0G1SbS17dA1S70G1L_;S1aSdfVg;Vam;A2M3G2A2S6dS8G3A2SbG0A1X70x2A3A2A2A2A2A2A2").
Proof using HMI Hgd HnS Hu rho.
  destruct RG as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & _ & _ & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
  unfold an2. destruct (sptr_eqb nQ pQ) eqn:E.
  - apply sptr_eqb_eq in E. assert (EA : apQ = anQ). { rewrite EanQ, EapQ. rewrite EnQ, EpQ in E. rewrite <- E in Mp. rewrite Mn in Mp. injection Mp as ->. reflexivity. }
    rewrite EA. repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.

Lemma MT_m_pQ : ltac2:(tb__ "0|3|
S2S0S8Se0Vg;Vam;A2M0SdfVg;Vam;A2M1A3A1S0S6cS9A1S9dSfcG0A2S6dS9S10S25S13SeaVs;Vg;Vam;A3M2A1S6dS8G1A2G2A3A1A2A3F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds HnS Hsc48 Hu mW.
  intros Hpn. destruct RG as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & _ & _ & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
  destruct (used_not_fq pQ apQ pQ_used pQ_ng) as [F1 F2].
  rewrite (MT_m_keep pQ pQ_ng F1 F2). rewrite EnQ, EpQ, EapQ in *. unfold fgm_s1, act_post. rewrite En.
  assert (MP : MT (dq_post s g am) p = Some (MUsed (am_set_links (am_prev ap) (Some n) ap))) by (apply (MT_dq_p s g am p n ap an Ep En Hng Hpg Mp Mn); exact Hpn).
  destruct (negb (sptr_eqb n g) && osptr_eqb (active_hd s (am_sc am)) (Some g))%bool; [|exact MP].
  destruct (MT (dq_post s g am) n) as [[| |an']|]; rewrite ?(MT_upd_other n _ _ p Hpn); exact MP.
Qed.
Section NotHead.
Hypothesis Hnh : ltac2:(tb__ "0|0|
S2S0S6cS8A1S9eVs;SdcVam;A1A2S6dS8Vg;A2A3A1").
Lemma s1_skip : ltac2:(tb__ "0|0|
S0S11S181Vs;Vg;Vam;A3S180Vs;Vg;Vam;A3A3").
Proof using HnS Hnh. destruct HnS as (n & En & _). unfold fgm_s1. exact (act_post_skip s g am n En Hnh). Qed.
Lemma MT_m_nQ_skip : ltac2:(tb__ "0|0|
S0S6cS9A1S9dSfcSdfVg;Vam;A2A2S6dS9S10S17dA1A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds HnS Hnh Hsc48 Hu mW. destruct (used_not_fq nQ anQ nQ_used nQ_ng) as [F1 F2]. rewrite (MT_m_keep nQ nQ_ng F1 F2), s1_skip. exact MT_dq_nQ. Qed.
Lemma act_m_skip : ltac2:(tb__ "0|1|
S0S6cS8A1S9eSfcSdcVam;A1M0A2S9eVs;G0A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w HR2g Hgd Hgd_holds HnS Hnh Hsc48 Hu mW.
  rewrite active_m_all, s1_skip. destruct RG as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & _).
  rewrite (hd_dq_gen s g am Hsc48' LenA3 p n ap an Ep En Hng Mp Mn sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)).
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. destruct (active_hd s (am_sc am)) as [h|]; cbn [osptr_eqb andb]; [|reflexivity].
  replace (sptr_eqb h g) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hnh eq_refl)). reflexivity.
Qed.

Lemma okC_N_skip (pv nv : sv) : ltac2:(tb__ "0|5|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vpv;A3S116VL;Se0Vg;Vam;A2M2A2A3S0S6aS10cG0G1Vnv;A3S70S6aL_;S1aSdfVg;Vam;A2M3G2A2S116VL;G3A2Sf3Vs;VL;Vg;Vam;A4X70x2A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS57S5eVpv;Vnv;Sd8P99A1Sd8P9bA1A5M4AaS157G4A1A2F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w HR2g Hgd Hgd_holds HnS Hnh Hsc48 Hu mW.
  intros Epv Env. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact HnN|].
  exists an2. split; [exact MT_m_nQ_skip|]. destruct an2_fields as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  rewrite E1, E2, E6, E7, E3, E4, Epv, Env, ze153, ze155. pose proof RN as R'. unfold zNn, U.Mal_nt__G1.Mal_nt_I.zNn.
  repeat split; try reflexivity; try (apply Z.mod_small; lia). destruct (sptr_eqb nQ pQ); reflexivity.
Qed.
End NotHead.

Lemma okC_P (pv : sv) : ltac2:(tb__ "0|1|
S2S0S8Se0Vg;Vam;A2SdfVg;Vam;A2A3A1S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8Vpv;A3Sf9Vs;VL;Vg;Vam;A4A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS57S61Vpv;Sd8P8dA1Sd8P70A1Sd8P71A1A5M0AaS157G0A1A2F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds HnS Hsc48 Hu mW.
  intros Hpn Epv. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact HpN|].
  exists (am_set_links (am_prev apQ) (Some nQ) apQ). split; [exact (MT_m_pQ Hpn)|]. cbn [am_mem am_prev am_next am_avail am_freed meta_bits am_set_links].
  rewrite Epv, ze141, ze112, ze113, zNx_n. pose proof RP as R'. unfold zPp, U.Mal_nt__G1.Mal_nt_I.zPp. repeat split; try reflexivity; apply Z.mod_small; lia.
Qed.

Lemma l1_locs_gen : ltac2:(tb__ "0|2|
S0S71S9cA1M0S100S75S9cS1b4Vs;Vg;Vam;Se0Vg;Vam;A2SdfVg;Vam;A2M1A5S70G0L_;S34S9eVs;SdcVam;A1A2S6dS8Vg;A2A2S11bG1A1S78S9cA1X70x2A3A3").
Proof using HMI Hgd HnS Hu rho.
  clear HR2g. destruct RG as (p & n & ap & an & En & Hng & _ & _ & _ & _ & _ & _ & _ & _ & EnQ & _). unfold l1_locs. rewrite En.
  replace (sptr_eqb n g) with false by (symmetry; apply sptr_eqb_neq; exact Hng). rewrite EnQ. reflexivity.
Qed.
Lemma locs_meta_klo (k : mkey) (d : od) (dsC : list od) l : ltac2:(tb__ "0|2|
S66Vs;Vam;Vk;A3S81S4bVd;VdsC;A3S0S6aS4cVs;VL;Vg;Vam;Vd;A5S67Vs;VL;Vg;Vam;Vk;A5M0A3S0S6aS4dVs;VL;Vg;Vam;Vd;A5S8cG0Z28A2A3S81S9cVl;S11bS68Vs;Vg;Vam;Vk;A4A1A3S3S4bS4bS1S81S4bR1VdsC;A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;Vl;A2M1A2S8dG1S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld';A2F_;F_;F_;F_;F_;").
Proof using HMI Hgd Hsc48 rho. intros Hk Hd E1 E2 Hl. rewrite (klo_ptr k Hk) in E1, E2. exact (locs_meta_of (kptr k) d dsC l Hd E1 E2 Hl). Qed.
End RingGen.

Section RingHead.
Hypothesis HnS : ltac2:(tb__ "0|0|
S3S8S8S1S0S6cS8A1SbVam;A1S6dS8R1A2A3S2S0S8R1Vg;A3A1A2Ln;A2").
Hypothesis Hhd : ltac2:(tb__ "0|0|
S0S6cS8A1S9eVs;SdcVam;A1A2S6dS8Vg;A2A3").
Lemma s1_act : ltac2:(tb__ "0|0|
S0S11S181Vs;Vg;Vam;A3S1b7SdfVg;Vam;A2S10S1c8S108A1A1S180Vs;Vg;Vam;A3A3A3").
Proof using HMI Hgd Hhd HnS Hu rho.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & _ & _ & Mp & Mn & EnQ & EpQ & EanQ & EapQ).
  unfold fgm_s1. rewrite (act_post_gen s g am p n ap an Ep En Hng Mp Mn Hhd). unfold an2. rewrite EnQ, EpQ, EanQ, EapQ. unfold an1.
  destruct (sptr_eqb n p); reflexivity.
Qed.
Lemma MT_m_nQ_act : ltac2:(tb__ "0|0|
S0S6cS9A1S9dSfcSdfVg;Vam;A2A2S6dS9S10S1c8S108A1A1A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hhd HnS Hsc48 Hu mW. destruct (used_not_fq nQ anQ nQ_used (nQ_ng HnS)) as [F1 F2]. rewrite (MT_m_keep nQ (nQ_ng HnS) F1 F2), s1_act. apply MT_upd_same. Qed.
Lemma act_m_head : ltac2:(tb__ "0|0|
S0S6cS8A1S9eSfcSdcVam;A1A2S6dS8SdfVg;Vam;A2A2A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hhd HnS Hsc48 Hu mW.
  rewrite active_m_all, s1_act, active_hd_upd_meta. destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & _ & _ & _ & _ & Mp & Mn & EnQ & _).
  rewrite (hd_dq_gen s g am Hsc48' LenA3 p n ap an Ep En Hng Mp Mn sc ltac:(pose proof Hsc48'; unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; lia)).
  unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl, Z.eqb_refl. cbn [andb]. rewrite EnQ. reflexivity.
Qed.
Lemma okC_act_head : ltac2:(tb__ "0|1|
S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS62Sd8P8dA1A1M0AaS157G0A1A2").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd Hgd_holds Hhd HnS Hsc48 Hu mW. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at]. split; [exact Hsc48|]. rewrite ze141, act_m_head. cbn [optrA]. exact (zNx_n HnS). Qed.
Lemma okC_N_act (pv nv : sv) : ltac2:(tb__ "0|5|
S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M0SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8M1Vpv;A3S116VL;Se0Vg;Vam;A2M2A2A3S0S6aS10cG0G1Vnv;A3S70S6aL_;S1aSdfVg;Vam;A2M3G2A2S116VL;G3A2Sf3Vs;VL;Vg;Vam;A4X70x2A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;SfcS57S5eVpv;Vnv;S105S106A5M4AaS157G4A1A2F_;F_;").
Proof using Erd Ewok HIr HMI HP13 HP13w HXz Hgd Hgd_holds Hhd HnS Hsc48 Hsp Hu bv0 mW.
  intros Epv Env. split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact (HnN HnS)|].
  exists (am_activate an2). split; [exact MT_m_nQ_act|]. destruct (an2_fields HnS) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold am_activate, act_of, am_set_avail, am_set_freed. cbn [am_mem am_prev am_next am_avail am_freed am_aidx am_last am_sc am_maplen meta_bits].
  rewrite E1, E6, E7, Epv, Env, ze_avN, ze_frN, E4, E5. unfold zNn, U.Mal_nt__G1.Mal_nt_I.zNn.
  split; [reflexivity|]. split; [rewrite <- E2; reflexivity|].
  split; [reflexivity|]. split; [destruct (sptr_eqb nQ pQ); reflexivity|]. split; reflexivity.
Qed.
Lemma l1_locs_head : ltac2:(tb__ "0|1|
S0S71S9cA1S100S75S9cS75S9cS75S9cS75S9cS11bSe0Vg;Vam;A2A1S11bSdfVg;Vam;A2A1M0A3S6fS9cSa3S8cSaeS8fZ8SdcVam;A1A2A2A1S78S9cA1A3A3S11bVg;A1A3G0A3A3").
Proof using HMI Hgd Hhd HnS Hu rho.
  rewrite (l1_locs_gen HnS). unfold dq_locs. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *. rewrite Hhd. cbn [osptr_eqb]. rewrite sptr_eqb_refl. reflexivity.
Qed.

Lemma avail_n0 : am_avail anQ = 0.
Proof using HMI Hgd Hhd HnS Hsc48 Hu rho.
  destruct (RG HnS) as (p & n & ap & an & En & Hng & Ep & Hpg & Hup & Hun & Scn & _ & _ & _ & EnQ & _ & EanQ & _).
  rewrite EanQ. apply (nonhead_avail0 n an Hun Scn Hsc48). rewrite Hhd. intros E. injection E as E. exact (Hng (eq_sym E)).
Qed.
End RingHead.
End Free3.

Section SelfRing.
Hypothesis Hng : ltac2:(tb__ "0|0|
S0S6cS8A1SbVam;A1S6dS8Vg;A2A3").
Lemma self_ring : ltac2:(tb__ "0|2|
S1S0S6cS8A1M0S13Vam;A1S6dS8Vg;A2M1A3S0G0S9eVs;SdcVam;A1A2G1A3A2").
Proof using HMI Hgd Hng Hsc48 Hsp Hu.
  clear HR2g. destruct (links_both ltac:(right; rewrite Hng; discriminate)) as (p & n & Ep & En).
  destruct (linked_ring ltac:(right; rewrite Hng; discriminate)) as (c & m0 & rest & Hc & Ec & Hhd & Rg & Hin).
  destruct (In_nth _ _ m0 Hin) as (kg & Hkg & Ekg).
  pose proof (ring_pos X s c m0 Hc rest Rg kg Hkg) as [Ng Pg]. rewrite Ekg in Ng, Pg.
  unfold mnext, mrec in Ng. rewrite HMg_inst, Hng in Ng. unfold mprev, mrec in Pg. rewrite HMg_inst, Ep in Pg.
  assert (GE : (length (m0 :: rest) <= S kg)%nat).
  { destruct (Nat.lt_ge_cases (S kg) (length (m0 :: rest))) as [LT|GE]; [|exact GE]. exfalso.
    apply (ring_distinct X s c m0 rest Rg kg (S kg) Hkg LT ltac:(lia)). rewrite Ekg. exact Ng. }
  rewrite nth_overflow in Ng by exact GE.
  assert (K0 : kg = 0%nat).
  { destruct kg as [|k]; [reflexivity|]. exfalso. apply (ring_distinct X s c m0 rest Rg 0 (S k) ltac:(cbn; lia) Hkg ltac:(lia)). transitivity g; [symmetry; exact Ng | symmetry; exact Ekg]. }
  subst kg. destruct rest as [|r rest']; [|cbn in GE; lia]. cbn [last] in Pg.
  split; [rewrite Ep, Pg, <- Ng; reflexivity | unfold sc, U.Mal_nt__G1.Mal_nt_I.sc; rewrite Ec, Hhd, Ng; reflexivity].
Qed.
Lemma Hpg1 : ltac2:(tb__ "0|0|
S0S6cS8A1S13Vam;A1S6dS8Vg;A2A3"). Proof using HMI Hgd Hng Hsc48 Hsp Hu. exact (proj1 self_ring). Qed.
Lemma Hhd1 : ltac2:(tb__ "0|0|
S0S6cS8A1S9eVs;SdcVam;A1A2S6dS8Vg;A2A3"). Proof using HMI Hgd Hng Hsc48 Hsp Hu. exact (proj2 self_ring). Qed.
Lemma act_m_none : ltac2:(tb__ "0|0|
S0S6cS8A1S9eS131SdcVam;A1A2S79S8A1A3").
Proof using Erd Ewok HIr HMI HP13 HP13w Hgd_holds Hng Hsc48 mW.
  rewrite active_m_all, (fgm_s1_D1 s g am Hng). unfold dq_post. rewrite Hng, sptr_eqb_refl, active_hd_upd_meta.
  apply active_hd_set_hd_same; [exact Hsc48' | exact LenA3].
Qed.
End SelfRing.
Section Keep.
Hypothesis Hng : ltac2:(tb__ "0|0|
S0S6cS8A1SbVam;A1S6dS8Vg;A2A3").
Hypothesis Hnok : ltac2:(tb__ "0|0|
S0S70S1cVs;Vg;Vam;A3S77A3").
Definition s_k : astate := ltac2:(tb__ "0|0|
S186Vg;Vi;Vs;Vam;A4").
Lemma Helse' : ltac2:(tb__ "0|0|
S0S70S76S93S8cS183Vam;A1S1eVi;A1A2S19ScVam;A1A1A2S1cVs;Vg;Vam;A3A2S77A3").
Proof using Hnok. rewrite Hnok. apply Bool.andb_false_r. Qed.
Lemma real_k : ltac2:(tb__ "0|0|
S1bbVX;VU;Vsr;Vg;Vam;Vi;S79S6eS73S6aA2A1S1b9S186Vg;Vi;Vsr;Vam;A4A9").
Proof using HIr HMI HR2g HU Hgd Hng Hnok Hsc48 Hsp Hu Hzs.
  destruct (Z.eq_dec mask 0) as [M0|M1].
  - apply (qg_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse'); [rewrite nmask_mask3; exact M0 | exact (proj2 (self_ring Hng))].
  - apply (or_realW X U sr s g am i Hzs HIr Hu HU HR2g Helse'). rewrite nmask_mask3. exact M1.
Qed.
Lemma nf_k : ltac2:(tb__ "0|1|
S1beVX;VU;Vs;S74S6cS6eS73S6aA2M0A1S11S79G0A1S1b9A4A4").
Proof using HMI HR2g HU Hgd Hml Hng Hnok Hsc48 Hsp Hu.
  apply (else_nf_post X U s g am i HI Hu HU HR2g 63%nat).
  - destruct (Z.eq_dec mask 0) as [M0|M1].
    + apply (qg_eq X U s g am i HI Hu Helse'); [rewrite nmask_mask3; exact M0 | exact (proj2 (self_ring Hng))].
    + apply (or_eq X s g am i Hu Helse'). rewrite nmask_mask3. exact M1.
  - change 64%nat with NEST_FUEL. apply fneed_le. pose proof R_all. lia.
Qed.
Lemma okC_k : ltac2:(tb__ "0|0|
S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;S1b9S196AaS157S196A1A2").
Proof using HMI HP12 Hgd Hng Hsc48 Hsp Hu.
  split; [|exact I]. cbn [U.Mal_nt__G1.Mal_nt_Db.od_ok_at U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.krec U.Mal_nt__G1.Mal_nt_D.kmemv U.Mal_nt__G1.Mal_nt_D.kbitsv]. split; [exact I|].
  exists (am_set_freed (Z.lor (am_freed am) (bit i)) am). split; [unfold s_k; apply MT_or_g|].
  split; [reflexivity|]. split; [reflexivity|].
  rewrite !ze12, ze133, ze_E_fr. pose proof R_all as R. cbn [am_set_freed am_prev am_next am_avail am_freed]. rewrite (proj1 (self_ring Hng)), Hng.
  unfold zG, U.Mal_nt__G1.Mal_nt_I.zG. repeat split; try reflexivity. apply Z.mod_small; lia.
Qed.
Lemma finish_keep SF (dsF : list od) rhoF msF : ltac2:(tb__ "0|1|
S11eVrhoW;VrhoF;A2Sc0S86VrhoF;VSF;S74S71S153A1S17eVtr;S17fVmsF;Vmd;A2A4M0A4VK;Vtr;Vmd;A2S0S70S19dVSF;VdsF;A2S72A3S4bS81S4bR1VdsF;A3S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S81S4bR2S6fS4bS196S78S4bA1A3A3A2F_;Fd;S81S4bS196VdsF;A3S1a2S86S87Vrho;S18cS86S115S18aVX;VU;S192Vsr;VL;A2VKc;A7G0A5F_;F_;F_;F_;F_;F_;").
Proof using EmW Erd Evm Ewok HIr HKc HMI HP12 HP13 HP13w HR2g HU HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hml Hng Hnok Hreach Hrom Hsc48 Hsm_pre Hsp Hu Hzs.
  intros HagF HsmF HK' HOK Hent Hin. destruct (HKc _ _ HK') as (HKc' & _ & _).
  destruct (keep_okb_sound SF dsF HOK) as (Hobjs & Hmatch & Hvars & HDS & Hpc & Hregs & Hfregs & Hfcsr & Hresv).
  pose proof nf_k as (HI' & Hcorr & Hub & _). cbn [fst snd] in HI', Hcorr, Hub.
  destruct (leaf_regs_ok_sound SF Hregs) as (Hcs & Ra0 & Ra1).
  assert (Hcond : forall d, In d dsF -> dcond d).
  { intros d Hd. destruct (Hent d Hd) as [[[_ C] _]|[<-|[]]]; [exact C | exact I]. }
  assert (HokC : forall d, In d [gkeep] -> In d dsF /\ od_ok_at s_k d /\ od_chg d) by (intros d [<-|[]]; split; [exact Hin | exact okC_k]).
  assert (Hlocs : forall l, In l (meta_locs g) -> exists d, In d [gkeep] /\ dlo d <= loc_addr L l < dhi d).
  { intros l Hl. apply (locs_meta_of g gkeep [gkeep] l); [left; reflexivity | reflexivity | reflexivity | exact Hl]. }
  exact (post_ok tr md msF rhoF EmW Evm HagF SF _ (tl (ss_objs SF)) dsF [gkeep] Hobjs Hmatch HsmF HDS Hcond Hent
           s_k (meta_locs g) HI' (xraw_or s am HXz) (delta_U _ _ _ (delta_or g i s am ND_s3 HMg_inst)) (bounded_of_delta _ _ (delta_or g i s am ND_s3 HMg_inst)) HokC Hlocs
           Hpc Hcs Hfregs Hfcsr Hresv Hsm_pre Kc HKc'
           ltac:(rewrite Ra0; reflexivity) ltac:(rewrite Ra1; reflexivity)
           (reach_ok_kept s s_k (shape_or g i s am HMg_inst) Hreach)
           (or_post g i sr am) real_k).
Qed.
End Keep.
End V.
End Mal_nt_V4.

Module Mal_nt_V7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasRing OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRings OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSurgery OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGeom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkReab OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRrules OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGeneric OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TryAvailPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RingFacts OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtImage OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtReal OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtRealN OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeSlotZone OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtNested.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt3_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ib OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Ic OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G1.Mal_nt_Db OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_Z OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G2.Mal_nt_V3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_nt__G3.Mal_nt_V4.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Ltac od_pw := repeat (first [ match goal with |- _ /\ _ => split | |- Forall _ _ => constructor | |- True => exact I end
                             | progress (cbv [U.Mal_nt__G2.Mal_nt_Z.od_pairwise U.Mal_nt__G2.Mal_nt_Z.od_disj U.Mal_nt__G2.Mal_nt_Z.needs_ring U.Mal_nt__G1.Mal_nt_D.kcond U.Mal_nt__G1.Mal_nt_D.fcond U.Mal_nt__G2.Mal_nt_Z.od_disj0 U.Mal_nt__G2.Mal_nt_Z.zkind U.Mal_nt__G2.Mal_nt_Z.ctx_lo U.Mal_nt__G1.Mal_nt_D.dsz U.Mal_nt__G1.Mal_nt_D.dlo U.Mal_nt__G1.Mal_nt_D.kptr U.Mal_nt__G1.Mal_nt_D.fptr]) ]);
              try assumption; try lia; try congruence.

Lemma cell_holds_zero (L0 : layout) (bv : byteview) (c : mcell) : ltac2:(tb__ "0|2|
S4S0Sb2Sb7Vc;A1M0Sb5Z0M1A1A3S0Sb2G0Sb1S79S8A1A1A3A2S73S163R1Sa2Vc;A1A2S0S6cS6aA1Vbv;S8cSa0VL0;Sa5Vc;A1A2S91R2A1A2A1S6dS6aG1A2A3F_;Fk;SaaVL0;Vbv;Vc;A3F_;F_;").
Proof.
  intros Hv Hb. unfold cell_holds. assert (E : mc_val c = VZ 0) by (destruct Hv as [E|E]; [exact E | rewrite E; reflexivity]).
  rewrite E. intros k Hk. rewrite (Hb k Hk). cbn [sval_num]. rewrite le_byte_0. reflexivity.
Qed.

Lemma toS_small n x : ltac2:(tb__ "0|1|
S8dZ0Vn;A2S1S8bS97S8eZ2S92Vn;Z1A2A2M0A1Vx;A2S8dVx;G0A2A2S0S6aS10fVn;Vx;A2Vx;A3F_;F_;").
Proof.
  intros Hn Hx. unfold toS.
  assert (P : 2 ^ n = 2 * 2 ^ (n - 1)) by (replace n with (n - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
  destruct (Z_lt_dec x 0).
  - replace (x mod 2 ^ n) with ((x + 1 * 2 ^ n) mod 2 ^ n) by (apply Z.mod_add; lia).
    rewrite Z.mod_small by lia.
    destruct (x + 1 * 2 ^ n <? 2 ^ (n - 1)) eqn:E; [apply Z.ltb_lt in E; lia | lia].
  - rewrite Z.mod_small by lia. destruct (x <? 2 ^ (n - 1)) eqn:E; [reflexivity | apply Z.ltb_ge in E; lia].
Qed.

Section V.

Variables (s : astate) (L : layout) (X : list sptr) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (i : Z).
Variable rho : valuation.
Variable gd : Z.
Variables (vm : VmMaps).
Variables (rd0 : word -> option byte) (wok0 : word -> bool).
Hypothesis HMI : ltac2:(tb__ "0|0|
S1bcS115VX;S6dS6eS8S6aA2S74S8S6aVg;Vi;A4A2VU;S192Vs;VL;A2Vrd0;Vwok0;Vvm;A8").
Hypothesis HXz : xzomb X s.
Hypothesis Hu : ltac2:(tb__ "0|0|
Sa1VX;Vs;Vg;Vam;A4").
Hypothesis Hgd : 0 <= gd < 2 ^ 64.
Local Notation "§22§ h__" := (h__ s L X U g i vm rd0 wok0 HMI) (at level 10, h__ global).
Local Abbreviation HI := (§22§ U.Mal_nt__G1.Mal_nt_I.HI).
Local Abbreviation HL := (§22§ U.Mal_nt__G1.Mal_nt_I.HL).
Local Abbreviation HV := (§22§ U.Mal_nt__G1.Mal_nt_I.HV).
Local Abbreviation HLG := (§22§ U.Mal_nt__G1.Mal_nt_I.HLG).
Local Abbreviation Hctx := (§22§ U.Mal_nt__G1.Mal_nt_I.Hctx).
Hypothesis HP12 : ltac2:(tb__ "0|0|
S0S6aSdaQ40Sc1Vrho;PcA2A2S116VL;Vg;A2A3").
Hypothesis HP13 : ltac2:(tb__ "0|0|
S0S6aSdaQ40Sc1Vrho;PdA2A2Vi;A3").
Local Abbreviation zG := (@U.Mal_nt__G1.Mal_nt_I.zG L g).
Local Abbreviation zM := (@U.Mal_nt__G1.Mal_nt_I.zM L am).
Local Abbreviation mask := (@U.Mal_nt__G1.Mal_nt_I.mask am).
Local Abbreviation g_key := (@U.Mal_nt__G1.Mal_nt_I.g_key s X g am Hu).
Local Notation "§23§ h__" := (h__ s L X U g am i gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation R_all := (§23§ U.Mal_nt__G1.Mal_nt_I.R_all).
Local Abbreviation sc := (@U.Mal_nt__G1.Mal_nt_I.sc am).
Local Abbreviation key_range40 := (@U.Mal_nt__G1.Mal_nt_I.key_range40 s L X U g i gd vm rd0 wok0 HMI Hgd).
Local Notation "§24§ h__" := (h__ s g am) (at level 10, h__ global).
Local Abbreviation gPar := (§24§ U.Mal_nt__G1.Mal_nt_I.gPar).
Local Abbreviation iPar := (§24§ U.Mal_nt__G1.Mal_nt_I.iPar).
Local Abbreviation amPar := (§24§ U.Mal_nt__G1.Mal_nt_I.amPar).
Local Abbreviation frPar := (§24§ U.Mal_nt__G1.Mal_nt_I.frPar).
Local Abbreviation par_spec := (§23§ U.Mal_nt__G1.Mal_nt_I.par_spec).
Local Notation "§25§ h__" := (h__ s L g am i rho gd rd0) (at level 10, h__ global).
Local Abbreviation rho1 := (§25§ U.Mal_nt__G1.Mal_nt_I.rho1).
Local Abbreviation zr1 := (§25§ U.Mal_nt__G1.Mal_nt_I.zr1).
Local Abbreviation zl1 := (§25§ U.Mal_nt__G1.Mal_nt_I.zl1).
Local Abbreviation zr1_any := (§25§ U.Mal_nt__G1.Mal_nt_I.zr1_any).
Local Abbreviation zl1_any := (§25§ U.Mal_nt__G1.Mal_nt_I.zl1_any).
Local Abbreviation RN := (§23§ U.Mal_nt__G1.Mal_nt_I.RN).
Local Abbreviation gPar_used := (§23§ U.Mal_nt__G1.Mal_nt_I.gPar_used).
Hypothesis Hsp : ltac2:(tb__ "0|1|
S1S8bZ1000SdaQ40Sc1Vrho;PaA2A2M0A2S0S6aS90G0Z10A2Z0A3A2").
Hypothesis Hdepth : ltac2:(tb__ "0|1|
S1S8bS10fZ40SdaQ40Sc1Vrho;PfA2A2A2M0N60A2S8bS97S8eZ2Z28A2A1G0A2A2").
Variable mV : word -> option byte.
Hypothesis Erd : ltac2:(tb__ "0|0|
S0Sd9Q40A1S6cSd9Q8A1A1F_;Vrd0;S136S86VmV;A2A3").
Hypothesis Ewok : ltac2:(tb__ "0|0|
S0Sd9Q40A1S70F_;Vwok0;S137S86VmV;A2A3").
Variable ms : machine_state.
Hypothesis Hrom : rom_ok segsU ms.
Hypothesis Hm_sct : ltac2:(tb__ "0|1|
S6aS1S8bZ0R1A2S8dR1Z60A2A2S0S6cSd9Q8A1M0A1VmV;SdbQ40S8cZ108ecR2A2A2A1S79G0A1A3F_;Fkk;").
Hypothesis Hgd_holds : ltac2:(tb__ "0|0|
S118S114Vrd0;Sd9Q40A1S72L_;A2S119S115A1U8Vgd;A4").
Let bv0 : byteview := ltac2:(tb__ "0|0|
S114S136S86VmV;A2S137S86VmV;A2A2").
Local Abbreviation AGq := (@U.Mal_nt__G1.Mal_nt_Ic.AGq L rho gd Hgd).
Local Abbreviation kptr := (§24§ U.Mal_nt__G1.Mal_nt_D.kptr).
Local Abbreviation kcond := (@U.Mal_nt__G1.Mal_nt_D.kcond s am).
Local Abbreviation fptr := (@U.Mal_nt__G1.Mal_nt_D.fptr s g).
Local Abbreviation fcond := (@U.Mal_nt__G1.Mal_nt_D.fcond s).
Local Abbreviation od := (@U.Mal_nt__G1.Mal_nt_D.od).
Local Abbreviation obj_of := (@U.Mal_nt__G1.Mal_nt_D.obj_of).
Local Notation "§26§ h__" := (h__ s L g am) (at level 10, h__ global).
Local Abbreviation dlo := (§26§ U.Mal_nt__G1.Mal_nt_D.dlo).
Local Abbreviation dsz := (@U.Mal_nt__G1.Mal_nt_D.dsz).
Local Abbreviation dhi := (§26§ U.Mal_nt__G1.Mal_nt_D.dhi).
Local Abbreviation dcells := (@U.Mal_nt__G1.Mal_nt_D.dcells).
Local Abbreviation drom := (@U.Mal_nt__G1.Mal_nt_D.drom).
Local Abbreviation ds_checkb := (@U.Mal_nt__G1.Mal_nt_D.ds_checkb).
Local Abbreviation dcond := (@U.Mal_nt__G1.Mal_nt_D.dcond am).
Local Abbreviation DS := (@U.Mal_nt__G1.Mal_nt_D.DS am).
Variable mW : word -> option byte.
Hypothesis HZ : ltac2:(tb__ "0|0|
S18dVL;VX;VmV;VmW;A4").
Let rhoW : valuation := rho1 mW.
Local Notation "§27§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsp) (at level 10, h__ global).
Local Abbreviation par_ranges := (§27§ U.Mal_nt__G1.Mal_nt_D.par_ranges).
Local Notation "§28§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd) (at level 10, h__ global).
Local Abbreviation flo_range := (§28§ U.Mal_nt__G1.Mal_nt_D.flo_range).
Local Notation "§29§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp mW) (at level 10, h__ global).
Local Abbreviation rngD := (§29§ U.Mal_nt__G1.Mal_nt_D.rngD).
Local Abbreviation klo_range' := (@U.Mal_nt__G1.Mal_nt_D.klo_range' s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd).
Local Abbreviation range64D := (@U.Mal_nt__G1.Mal_nt_D.range64D s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd Hsp).
Local Abbreviation cellsD := (§29§ U.Mal_nt__G1.Mal_nt_Db.cellsD).
Local Notation "§30§ h__" := (h__ s L g am rho gd Hgd) (at level 10, h__ global).
Local Abbreviation cellsInD := (§30§ U.Mal_nt__G1.Mal_nt_Db.cellsInD).
Local Abbreviation semD := (@U.Mal_nt__G1.Mal_nt_Db.semD am).
Local Abbreviation coverD := (§30§ U.Mal_nt__G1.Mal_nt_Db.coverD).
Local Abbreviation dunkD := (@U.Mal_nt__G1.Mal_nt_Db.dunkD am).
Local Abbreviation romD := (@U.Mal_nt__G1.Mal_nt_Db.romD s L X g am rho gd Hgd mV Hm_sct mW HZ).
Local Abbreviation od_ok_at := (§25§ U.Mal_nt__G1.Mal_nt_Db.od_ok_at).
Local Abbreviation od_ok := (§25§ U.Mal_nt__G1.Mal_nt_Db.od_ok).
Local Abbreviation zkind := (§24§ U.Mal_nt__G2.Mal_nt_Z.zkind).
Local Abbreviation ctx_lo := (@U.Mal_nt__G2.Mal_nt_Z.ctx_lo am).
Local Abbreviation od_disj0 := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_disj0).
Local Abbreviation needs_ring := (@U.Mal_nt__G2.Mal_nt_Z.needs_ring s am).
Local Abbreviation od_disj := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_disj).
Local Abbreviation g_zone := (§28§ U.Mal_nt__G2.Mal_nt_Z.g_zone).
Local Abbreviation keys_apart := (§22§ U.Mal_nt__G2.Mal_nt_Z.keys_apart).
Local Abbreviation od_pairwise := (§26§ U.Mal_nt__G2.Mal_nt_Z.od_pairwise).
Local Abbreviation zfree := (@U.Mal_nt__G2.Mal_nt_Z.zfree s L X g am).
Local Abbreviation X_key := (§22§ U.Mal_nt__G2.Mal_nt_Z.X_key).
Local Abbreviation X_not_used := (@U.Mal_nt__G2.Mal_nt_Z.X_not_used s X).
Local Abbreviation od_ok_at_zkc := (§25§ U.Mal_nt__G2.Mal_nt_Z.od_ok_at_zkc).
Local Abbreviation zfree_of := (§27§ U.Mal_nt__G2.Mal_nt_Z.zfree_of).
Local Abbreviation od_ok_zfree := (§27§ U.Mal_nt__G2.Mal_nt_Z.od_ok_zfree).
Local Abbreviation HZ_at := (@U.Mal_nt__G2.Mal_nt_Z.HZ_at L X rho gd Hgd mV mW HZ).
Local Abbreviation HZ_none := (@U.Mal_nt__G2.Mal_nt_Z.HZ_none L X mV mW HZ).
Local Abbreviation od_hold_W := (@U.Mal_nt__G2.Mal_nt_Z.od_hold_W s L X U g am i rho gd vm rd0 wok0 HMI HXz Hu Hgd HP12 Hsp Hdepth mV Erd Ewok ms Hrom Hm_sct Hgd_holds mW HZ).
Local Abbreviation sp0 := (@U.Mal_nt__G2.Mal_nt_Z.sp0 rho).
Local Abbreviation D0 := (@U.Mal_nt__G2.Mal_nt_Z.D0 rho).
Hypothesis Hsp_high : ltac2:(tb__ "0|0|
S8bS117VL;A1S8cS149Vrho;A1S14aVrho;A1A2A2").
Variable TR : assn -> assn -> Prop.
Variable K : ltac2:(tb__ "0|0|
S71S153A1S154OF_;F_;").
Hypothesis TRR : ltac2:(tb__ "0|0|
S1c0S86VTR;VK;A3").
Let TR_run := tr_run segsU TR K TRR.
Let TR_refl : ltac2:(tb__ "0|0|
S10aVTR;R1R1A2FP;") := ltac2:(tb__ "0|0|
S1c5S86VTR;VK;VTRR;A4").
Let TR_seq : ltac2:(tb__ "0|1|
S10aS10aS10aVTR;R3R2A2M0G0VTR;R5R3A2F_;F_;FQ;FR;FP;") := ltac2:(tb__ "0|0|
S1c7S86VTR;VK;VTRR;A4").
Let TR_ex := tr_ex segsU TR K TRR.
Let TR_pure : ltac2:(tb__ "0|0|
OS10aS10aR3VTR;R3R2A2F_;VTR;S10bS1R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX0;") := ltac2:(tb__ "0|0|
S1c4S86VTR;VK;VTRR;A4").
Let TR_conseq : ltac2:(tb__ "0|2|
S10aS10aS10aS10aS10bR4R1A1M0R6R2A1F_;Fw;S10bG0R4R2A1F_;Fw;VTR;R6R4A2M1G1F_;F_;F_;FQ';FQ;FP';FP;") := ltac2:(tb__ "0|0|
S1c1S86VTR;VK;VTRR;A4").
Let TR_pointwise : ltac2:(tb__ "0|0|
S10aS10aS10bR3R1A1VTR;S10bS0S10bR1R3A3Lw';R3A2F_;Fw;VTR;R3R2A2F_;FQ;FR;") := ltac2:(tb__ "0|0|
S1c3S86VTR;VK;VTRR;A4").
Let TR_disj : ltac2:(tb__ "0|0|
S10aS10aS10aVTR;R3R1A2VTR;R3R2A2VTR;S10bS4R6R1A1R5R1A1A2Lw;R3A2F_;F_;FQ;FP2;FP1;") := ltac2:(tb__ "0|0|
S1c2S86VTR;VK;VTRR;A4").
Variable sr : astate.
Hypothesis Hzs : ltac2:(tb__ "0|0|
S1baVX;Vsr;Vs;A3").
Hypothesis HIr : ltac2:(tb__ "0|0|
Sa6VX;S6dS6eS8S6aA2S74S8S6aVg;Vi;A4A2VU;Vsr;A4").
Local Notation agreesW := (agrees rhoW).
Hypothesis HP13w : ltac2:(tb__ "0|1|
S0Sd9Q40M0A1Sc1Vrho;PdA2SdbG0Vi;A2A3").
Variables (tr : list event) (md : Model) (Kc : list event -> Model -> Prop).
Hypothesis EmW : ltac2:(tb__ "0|0|
S0Sd9Q40A1S6cSd9Q8A1A1F_;VmW;SceVrho;A1A3").
Hypothesis Evm : ltac2:(tb__ "0|0|
S0S155Vvm;S156Vmd;A1A3").
Hypothesis HKc : ltac2:(tb__ "0|1|
S71S153A1M0S154VK;R2R1A2S1VKc;R3R2A2S1S0G0R3Vtr;A3S0S154R2Vmd;A3A2A2F_;Fmd';Ftr';").
Hypothesis Hsm_pre : ltac2:(tb__ "0|0|
Sc0S86Vrho;S18fS18aA1S74S71S153A1S17eVtr;S17fVms;Vmd;A2A4A4").
Hypothesis HU : ltac2:(tb__ "0|0|
S6aS8bZ0VU;R1A1A2Fc;").
Hypothesis HR2g : ltac2:(tb__ "0|2|
S2S0S6eS6cS8A1M0G0A2S74G0G0S13Vam;A1SbVam;A1A4S74G0G0S79S8A1M1G1A4A3A1S2S0G0S9eVs;SeVam;A1A2S6dS8Vg;A2A3A1S2S0S6aS17Vam;A1Z0A3A1F_;F_;").
Hypothesis Hreach : reach_ok s.
Hypothesis Hall : ltac2:(tb__ "0|0|
S0S6aS8cSebVam;A1S1eVi;A1A2S19ScVam;A1A1A3").
Hypothesis Hsc48 : 0 <= sc < 48.
Local Abbreviation nmask_mask3 := (@U.Mal_nt__G3.Mal_nt_V4.nmask_mask3 am).
Local Abbreviation HnU3 := (§23§ U.Mal_nt__G3.Mal_nt_V4.HnU3).
Local Abbreviation HpU3 := (§23§ U.Mal_nt__G3.Mal_nt_V4.HpU3).
Local Abbreviation Hlinks3 := (§28§ U.Mal_nt__G3.Mal_nt_V4.Hlinks3).
Local Abbreviation HactU3 := (§28§ U.Mal_nt__G3.Mal_nt_V4.HactU3).
Local Notation "§31§ h__" := (h__ s L X U g am i rho gd vm rd0 wok0 HMI Hu Hgd Hsc48) (at level 10, h__ global).
Local Abbreviation Hact3 := (§31§ U.Mal_nt__G3.Mal_nt_V4.Hact3).
Local Abbreviation l1_locs := (§24§ U.Mal_nt__G3.Mal_nt_V4.l1_locs).
Local Abbreviation s1_facts := (§31§ U.Mal_nt__G3.Mal_nt_V4.s1_facts).

Hypothesis Hml0 : am_maplen am = 0.

Lemma HuP : ltac2:(tb__ "0|0|
Sa1VX;Vs;Se6Vs;Vg;Vam;A3Se2Vs;Vg;Vam;A3A4"). Proof using HMI Hgd Hml0 Hu. exact (gPar_used Hml0). Qed.
Lemma HiP : ltac2:(tb__ "0|1|
S1S8bZ0Se4Vs;Vg;Vam;A3M0A2S8bG0ScSe2Vs;Vg;Vam;A3A1A2A2"). Proof using HMI Hgd Hml0 Hu. exact (proj1 (proj2 (par_spec Hml0))). Qed.
Lemma HfrP : ltac2:(tb__ "0|0|
S0S6cS1bA1S28S26Se2Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A2A1S6dS1bSf0Vs;Vg;Vam;A3A2A3"). Proof using HMI Hgd Hml0 Hu. exact (proj1 (proj2 (proj2 (par_spec Hml0)))). Qed.
Lemma HkP : ltac2:(tb__ "0|0|
S0S40S41Sf0Vs;Vg;Vam;A3A1S3cA3"). Proof using HMI Hgd Hml0 Hu. exact (proj1 (proj2 (proj2 (proj2 (par_spec Hml0))))). Qed.
Lemma HmemP : ltac2:(tb__ "0|0|
S0S8S16Vam;A1S27Se2Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A2A3"). Proof using HMI Hgd Hml0 Hu. exact (proj1 (proj2 (proj2 (proj2 (proj2 (par_spec Hml0)))))). Qed.
Lemma HscP : ltac2:(tb__ "0|0|
S8dSdcVam;A1SeSe2Vs;Vg;Vam;A3A1A2"). Proof using HMI Hgd Hml0 Hu. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (par_spec Hml0))))))). Qed.
Lemma HgPg : gPar <> g. Proof using HMI Hgd Hml0 Hu. pose proof (par_spec Hml0) as P. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 P)))))))))))). Qed.
Lemma HallN : ltac2:(tb__ "0|0|
S0S6aS8cS183Vam;A1S1eVi;A1A2S19ScVam;A1A1A3"). Proof using Hall. rewrite nmask_mask3. exact Hall. Qed.
Lemma Hsc48am : ltac2:(tb__ "0|1|
S1S8bZ0SeVam;A1M0A2S8dG0Z30A2A2"). Proof using Hsc48. exact Hsc48. Qed.

Definition amPar' : ameta := am_forget amPar iPar.
Definition s3v : astate := ltac2:(tb__ "0|0|
S1ceVs;Vg;Vam;Se6Vs;Vg;Vam;A3Se2Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A6").
Definition s2n : astate := ltac2:(tb__ "0|0|
S1ccVs;Vg;Vam;A3").

Lemma Hact3' : ltac2:(tb__ "0|1|
S8SaS0S6cS8A1M0SbVam;A1S6dS8R2A2A3S2S0S8R3Vg;A3A1S0G0S9eVs;SeVam;A1A2S6dS8Vg;A2A3S0S6cS9A1S9dS180Vs;Vg;Vam;A3R5A2S6dS9S10R4A1A2A3S0S6aS22R5A1Z0A3F_;F_;F_;F_;Fan;Fn;").
Proof using HMI Hgd Hsc48 Hu rho. exact Hact3. Qed.
Lemma HactU3' : ltac2:(tb__ "0|1|
S8S0S6cS8A1M0SbVam;A1S6dS8R1A2A3S2S0S8R2Vg;A3A1S0G0S9eVs;SeVam;A1A2S6dS8Vg;A2A3S3SaSaS0S6cS9A1S9dS180Vs;Vg;Vam;A3R5A2S6dS9S10R1A1A2A3Lan;A2F_;F_;F_;Fn;").
Proof using HMI Hgd Hu rho. exact HactU3. Qed.

Ltac fgn_arg := first [ exact HuP | exact HiP | exact HfrP | exact HkP | exact HmemP | exact HscP
                      | exact HI | exact Hu | exact HU | exact HR2g | exact HallN | exact Hsc48am | exact Hml0 | exact Hlinks3 | exact HnU3 | exact Hact3' | exact HactU3'
                      | exact HXz | exact (proj1 Hreach) | exact Hreach ].
Lemma N3_call : ltac2:(tb__ "0|5|
S1Sa6S6fS8Vg;VX;A3M0S6dS6eS8S6aA2S74S8S6aSe6Vs;Vg;Vam;A3M1Se4Vs;Vg;Vam;A3A4A2VU;S132A4S1Sa1G0S132G1S133A4S1S0S6cS9A1M2S9dS132Vg;A2S6dS9S12S79S8A1M3G3A2A2A3S1S8S2S0S8R1Vg;A3A1S2S0S8R2G1A3A1S0G2S9dS132R3A2S9dS135R3A2A3F_;F_;Fq;S2S0S6eS6cS8A1M4G4A2S74G4G4S13S133A1SbS133A1A4S74G4G4G3G3A4A3A1S2S0G4S9eS132SeS133A1A2S6dS8G1A2A3A1S2S0S6aS17S133A1Z0A3A1F_;F_;A2A2A2A2").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. unfold s3v, s2n, amPar'. eapply (fgn_call X U s g am i) with (frP := frPar); fgn_arg. Qed.
Lemma HI3v : ltac2:(tb__ "0|0|
Sa6S6fS8Vg;VX;A3S6dS6eS8S6aA2S74S8S6aSe6Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A4A2VU;S132A4"). Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact (proj1 N3_call). Qed.
Lemma HXz3v : ltac2:(tb__ "0|0|
S18eS6fS8Vg;VX;A3S132A2").
Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hsc48 Hu rho. intros x Hx. unfold s3v. eapply (xzomb_s3v X U s g am i) with (frP := frPar); try fgn_arg. exact Hx. Qed.
Lemma HXr3v : ltac2:(tb__ "0|0|
S1caS6fS8Vg;VX;A3S132A2"). Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hsc48 Hu rho. exact (xzomb_xraw _ _ HXz3v). Qed.
Lemma Mg3v : ltac2:(tb__ "0|1|
S0S6cS9A1S9dS132Vg;A2S6dS9S12S79S8A1M0G0A2A2A3"). Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact (proj1 (proj2 (proj2 N3_call))). Qed.
Lemma HuP3v : ltac2:(tb__ "0|0|
Sa1S6fS8Vg;VX;A3S132Se6Vs;Vg;Vam;A3S133A4"). Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. exact (proj1 (proj2 N3_call)). Qed.
Lemma reach3v : reach_ok s3v.
Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hreach Hsc48 Hu rho. unfold s3v. eapply (reach_s3v X U s g am i) with (frP := frPar); fgn_arg. Qed.

Definition s3r : astate := ltac2:(tb__ "0|0|
S1cdVsr;Vg;Vam;Se6Vs;Vg;Vam;A3Se2Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A6").
Lemma s3r_inv : ltac2:(tb__ "0|2|
S1Sa6S6fS8Vg;VX;A3M0S6dS6eS8S6aA2S74S8S6aSe6Vs;Vg;Vam;A3M1Se4Vs;Vg;Vam;A3A4A2VU;S134A4Sa1G0S134G1S133A4A2").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. unfold s3r, amPar'. exact (s3r_factsW X U sr s g am i Hzs HIr Hu HU HR2g HallN Hsc48am Hml0 Hlinks3 HnU3 HpU3 Hact3' HactU3' gPar amPar iPar frPar HuP HiP HfrP HmemP HscP). Qed.
Lemma s3v_real : ltac2:(tb__ "0|0|
S0S11S132S1cfS6fS8Vg;VX;A3S134A2A3").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. unfold s3v, s3r. exact (s3v_zombW X U sr s g am i Hzs HIr Hu HU HR2g HallN Hsc48am Hml0 Hlinks3 HnU3 HpU3 Hact3' HactU3' gPar amPar iPar frPar HuP HiP HfrP HmemP HscP). Qed.

Lemma ntf_nested fuel r t4 t5 : ltac2:(tb__ "0|4|
S0S32S11S6eS6cS6eS73S6aA2A1M0S11A2M1A2M2S33Vfuel;Se6Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3S134A4S24S11G1S74G0S11Vr;Vt4;A4A3A3S0S32S11S6eS7eS11A2M3A2S42Vg;Vt4;A2S24S11G3S74S7eS11S80Vt5;A4A3A3S0G2S33S7cVfuel;A1Vg;Vi;Vsr;A4S24S11G1S74G0S11Vr;Vt5;A4A3A3F_;F_;").
Proof using HIr HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu Hzs rho. unfold s3r. exact (fgn_realW X U sr s g am i Hzs HIr Hu HU HR2g HallN Hsc48am Hml0 Hlinks3 HnU3 HpU3 Hact3' HactU3' gPar amPar iPar frPar HuP HiP HfrP HkP HmemP HscP fuel r t4 t5). Qed.
Lemma scP48 : ltac2:(tb__ "0|1|
S1S8bZ0SeSe2Vs;Vg;Vam;A3A1M0A2S8dG0Z30A2A2").
Proof using HMI Hgd Hml0 Hsc48 Hu.
  pose proof (par_spec Hml0) as (HuP0 & _ & _ & _ & _ & HscP0 & HscP63 & _). pose proof Hsc48am as SC.
  pose proof (inv_groups HI gPar amPar HuP0) as (_ & _ & _ & GC & _). destruct GC as [(E & _)|(R & _)]; [exfalso; exact (HscP63 E) | exact R].
Qed.
Lemma fneed_par F : ltac2:(tb__ "0|0|
S164S1bdSdcVam;A1A1S7cVF;A1A2S164S1bdSeSe2Vs;Vg;Vam;A3A1A1VF;A2F_;").
Proof using HMI Hgd Hml0 Hsc48 Hsp Hu. intros HF. pose proof scP48 as P. pose proof HscP as Q. pose proof Hsc48am as SC. unfold fneed in *. unfold sc, U.Mal_nt__G1.Mal_nt_I.sc in *.
  destruct (am_sc am <? 48) eqn:E1; [|apply Z.ltb_ge in E1; lia]. destruct (am_sc amPar <? 48) eqn:E2; [|apply Z.ltb_ge in E2; lia]. lia. Qed.
Lemma tier3v : ltac2:(tb__ "0|0|
S163S1bfSeSe2Vs;Vg;Vam;A3A1A1S1bfSdcVam;A1A1A2").
Proof using HMI Hgd Hml0 Hreach Hu. eapply (tier_par X s g am); fgn_arg. Qed.
Lemma HI2n : ltac2:(tb__ "0|0|
Sa6S6fS8Vg;VX;A3S79S6eS8S6aA2A1VU;S135A4").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. unfold s2n. eapply (s2_facts_model X U s g am i); fgn_arg. Qed.
Lemma HuP2n : ltac2:(tb__ "0|0|
Sa1S6fS8Vg;VX;A3S135Se6Vs;Vg;Vam;A3Se2Vs;Vg;Vam;A3A4").
Proof using HMI HR2g Hall Hgd Hml0 Hsc48 Hu rho. unfold s2n. eapply (HuP2 X U s g am i); fgn_arg. Qed.
Lemma deltaU3v : ltac2:(tb__ "0|1|
S1b3Vs;S132S75S9cS75S9cS75S9cS1d1Vs;Vg;Vam;A3S6fS9cSa3S8cSa8S8fZ8SdcVam;A1A2A2A1S78S9cA1M0A3A3G0A3S11bVg;A1A3A3").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. unfold s3v. eapply (deltaU_s3v X U s g am i) with (frP := frPar); try fgn_arg. exact (proj1 s1_facts). Qed.
Lemma corr3v q a : ltac2:(tb__ "0|0|
Sa1S6fS8Vg;VX;A3S132Vq;Va;A4S3SaSaS1Sa1VX;Vs;Vq;R1A4S1S0S8S16Va;A1S16R1A1A3S1S0S6aS14Va;A1S14R1A1A3S1S0S6aScVa;A1ScR1A1A3S1S0S6aSeVa;A1SeR1A1A3S0S6aS15Va;A1S15R1A1A3A2A2A2A2A2La0;A2F_;").
Proof using HMI HR2g Hall Hgd Hml0 Hsc48 Hu rho. unfold s3v. intros Hq. eapply (corr_s3v X U s g am i) with (frP := frPar); try fgn_arg. exact Hq. Qed.
Lemma ub3v : ub_same s s3v.
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. unfold s3v. eapply (ub_s3v X U s g am i) with (frP := frPar); fgn_arg. Qed.
Lemma amPar'_fr : ltac2:(tb__ "0|0|
S0S6cS1bA1S28S26S133Se4Vs;Vg;Vam;A3A2A1S79S1bA1A3").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. unfold amPar'. rewrite (fu_nth (g :: X) None U s2n gPar amPar iPar HI2n HuP2n HiP iPar ltac:(pose proof HiP; lia)). rewrite Z.eqb_refl. reflexivity. Qed.
Lemma amPar'_fields : ltac2:(tb__ "0|1|
S1S0S8S16S133A1S16Se2Vs;Vg;Vam;A3M0A1A3S1S0S6aScS133A1ScG0A1A3S1S0S6aSeS133A1SeG0A1A3S1S0S6aS14S133A1S14G0A1A3S1S0S6aS20S133A1S20G0A1A3S1S0S6aSafS133A1SafG0A1A3S6aS0S8S27S133R1A2S27G0R1A2A3Fj;A2A2A2A2A2A2").
Proof using . exact (upd_slot_fields amPar iPar _). Qed.
Lemma keys3v : ltac2:(tb__ "0|0|
S0S71S8A1Sa4S132A1Sa4Vs;A1A3").
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho. pose proof deltaU3v as (_&_&_&_&_&_&KK&_). exact KK. Qed.
Lemma HL3v : layout_ok L s3v.
Proof using HMI HR2g HU Hall Hgd Hml0 Hsc48 Hu rho.
  pose proof deltaU3v as (Dfp & _ & _ & _ & Dreg & _).
  pose proof HL as (A & B & C' & D). split; [exact A|]. split; [|rewrite Dfp; split; [exact C' | exact D]].
  intros k rg Hr Hl. unfold region_of in Hr. rewrite Dreg in Hr. exact (B k rg Hr Hl).
Qed.

Lemma bptr_free c : ltac2:(tb__ "0|0|
S81S9fVc;S75S9fSa7S132A1S191S132A1A3A3S1c9VL;Vc;SedVL;Vam;A2Z8A4S5F_;F_;").
Proof using HMI HR2g HU HXz Hall Hgd Hml0 Hsc48 Hu rho.
  intros Hc Hm. pose proof amPar'_fields as (_ & F2 & _ & _ & _ & _ & F7).
  refine (free_slot_zone (g :: X) (Some (gPar, iPar)) U s3v L HI3v HXr3v HL3v gPar amPar' iPar c HuP3v ltac:(rewrite F2; exact HiP) amPar'_fr Hc _).
  rewrite (F7 iPar), <- HmemP. exact Hm.
Qed.

Section ReabC.
Variables (msF : machine_state) (rhoF : valuation).
Hypothesis HagF : agreesW rhoF.

Variable scut : Z.
Hypothesis Hscut : ltac2:(tb__ "0|1|
S1S8bZ0M0Vscut;A2S8bS8cS14aVrho;A1Vscut;A2G0A2A2").

Variables (SF : sstate) (stkc : list cell) (objsF : list sobj) (dsF dsC dsO dsB : list od).

Definition dsX : list od := ltac2:(tb__ "0|0|
S75S4bVdsC;S75S4bVdsO;VdsB;A3A3").
Definition oStkF : sobj := ltac2:(tb__ "0|0|
Sd3SccPaA1SccPfA1SbdZ0A1Vstkc;Sd1A5").
Definition NRELW : list sobj := map obj_of dsF.
Hypothesis HSF_objs : ltac2:(tb__ "0|0|
S0S71SbbA1ScfVSF;A1S6fSbbS13eVobjsF;A3A3").
Hypothesis HSF_match : ltac2:(tb__ "0|0|
S0S70S15aVobjsF;S141A2S72A3").
Hypothesis HsmF : ltac2:(tb__ "0|0|
Sc0S86VrhoF;VSF;S74S71S153A1S17eVtr;S17fVmsF;Vmd;A2A4A4").
Hypothesis HdsF_vars : ltac2:(tb__ "0|0|
S0S70S82SbbS1a3S11fA1S141A3S72A3").
Hypothesis HdsF_DS : ltac2:(tb__ "0|0|
S0S70S82S4bS53VdsF;A3S72A3").
Hypothesis HdsF_cond : ltac2:(tb__ "0|0|
S4bS81S4bR1VdsF;A3S5bVam;R2A2F_;Fd;").

Hypothesis HdsF_ent : ltac2:(tb__ "0|0|
S4bS81S4bR1VdsF;A3S4S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;R2A9S81S4bR2S138A3A2F_;Fd;").
Variables (s' : astate) (locs : list loc).
Hypothesis HI' : ltac2:(tb__ "0|0|
Sa6S6fS8Vg;VX;A3S6dS6eS8S6aA2S74S8S6aSe6Vs;Vg;Vam;A3Se4Vs;Vg;Vam;A3A4A2VU;Vs';A4").
Hypothesis HXz' : ltac2:(tb__ "0|0|
S18eS6fS8Vg;VX;A3Vs';A2").
Lemma HXr' : ltac2:(tb__ "0|0|
S1caS6fS8Vg;VX;A3Vs';A2"). Proof using HXz'. exact (xzomb_xraw (g :: X) s' HXz'). Qed.
Hypothesis Hdelta : ltac2:(tb__ "0|0|
S1b3Vs;Vs';Vlocs;A3").
Hypothesis Hbounded' : bounded s'.

Definition od_chgC (d : od) : Prop := ltac2:(tb__ "0|1|
S4bOLd;Vd;S5S5S5S69SbaSbaSbaSbaS6Lfv;Lav;Lnv;Lpv;Lk;SbaS6Lhv;SbaS6Lx;M0SbaSbaSbaSbaS6Ld0;Lc;Lb;La;G0S65S70SbaSbaS6Lnv;Lpv;Lfive;Lk;G0G0SbaS5Lx;S5SbaS5Lc0;S5S5S5S5S71S6eS6eS6aS73A2SbaA2A1S6Lcs;X4bx13").
Hypothesis HdsC : ltac2:(tb__ "0|0|
S4bS81S4bR1VdsC;A3S1S81S4bR2VdsF;A3S1S14dVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vs';R2AaS146R2A1A2A2F_;Fd;").
Hypothesis HdsO : ltac2:(tb__ "0|1|
S4bS81S4bR1VdsO;A3S1S81S4bR2VdsF;A3S1S0S6cS6bA1S56R2A1S79S6bA1A3S1S8bSe8VL;Vg;A2M0S4cVs;VL;Vg;Vam;R2A5A2S8bS4dVs;VL;Vg;Vam;R2A5S8cG0Z28A2A2A2A2A2F_;Fd;").
Hypothesis HdsO_cover : ltac2:(tb__ "0|1|
S6aS1S8bSe8VL;Vg;A2M0R1A2S8dR1S8cG0Z28A2A2A2S3S4bS4bS1S81S4bR1VdsO;A3S1S8bS4cVs;VL;Vg;Vam;R1A5R3A2S8dR3S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2F_;Fx;").
Hypothesis HdsB : ltac2:(tb__ "0|2|
S4bS81S4bR1VdsB;A3S1S81S4bR2VdsF;A3S1S0S6cS6bA1S56R2A1S79S6bA1A3S1S14bVs;VL;VX;Vg;Vam;R2A6S1S9fS81S9fR1S75S9fSa7Vs';A1S191Vs';A1A3A3S1c9VL;R2S4cVs;VL;Vg;Vam;R4A5M0S92S4dVs;VL;Vg;Vam;R4A5G0A2A4S5F_;F_;Fc;S1S4S8bS4dVs;VL;Vg;Vam;R2A5Z10000A2S8bZ5b000S4cVs;VL;Vg;Vam;R2A5M1A2A2S1S8bZ1000G1A2S6aS1S8bS4cVs;VL;Vg;Vam;R3A5R1A2S8dR1S4dVs;VL;Vg;Vam;R3A5A2A2Sa9VL;Vs;R2A3F_;Fx;A2A2A2A2A2A2F_;Fd;").
Hypothesis Hlocs : ltac2:(tb__ "0|3|
S9cS81S9cR1Vlocs;A3S4S3S4bS4bS1S81S4bR1VdsC;A3S1S8bS4cVs;VL;Vg;Vam;R1A5Sa0VL;R3A2M0A2S8dG0S4dVs;VL;Vg;Vam;R1A5A2A2A2Ld;A2S1S8bSe8VL;Vg;A2M1Sa0VL;R2A2M2A2S8dG2S8cG1Z28A2A2A2A2F_;Fl;").

Hypothesis HdsCB_g : ltac2:(tb__ "0|1|
S4bS81S4bR1S75S4bVdsC;VdsB;A3A3S4S8bS4dVs;VL;Vg;Vam;R2A5Se8VL;Vg;A2M0A2S8bS8cG0Z28A2S4cVs;VL;Vg;Vam;R2A5A2A2F_;Fd;").

Lemma HdsF d : ltac2:(tb__ "0|0|
S81S4bVd;VdsF;A3S54Vam;Vd;A2F_;").
Proof using HdsF_DS HdsF_cond. intros Hd. split; [exact (proj1 (forallb_forall _ _) HdsF_DS d Hd) | exact (HdsF_cond d Hd)]. Qed.
Lemma Hent_hold d : ltac2:(tb__ "0|0|
S81S4bVd;VdsF;A3S14eVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;Vd;A9Sd5S86VrhoW;S1cbVms;VmW;A2S4fVd;A1A4F_;F_;").
Proof using Erd Ewok HMI HP12 HXz HZ Hdepth Hgd Hgd_holds Hm_sct Hrom Hsp Hu. intros _ Hok. exact (od_hold_W d Hok). Qed.
Lemma HdsC_sub d : ltac2:(tb__ "0|0|
S81S4bVd;VdsC;A3S1S81S4bVd;VdsF;A3S0S6cS6bA1S56Vd;A1S79S6bA1A3A2F_;").
Proof using HdsC. intros Hd. destruct (HdsC d Hd) as (A & _ & B). split; [exact A|]. destruct d; try reflexivity. destruct B. Qed.
Lemma HdsX_sub d : ltac2:(tb__ "0|0|
S81S4bVd;S138A3S1S81S4bVd;VdsF;A3S0S6cS6bA1S56Vd;A1S79S6bA1A3A2F_;").
Proof using HdsB HdsC HdsO.
  intros Hd. unfold dsX in Hd. apply in_app_iff in Hd as [Hd|Hd]; [exact (HdsC_sub d Hd)|].
  apply in_app_iff in Hd as [Hd|Hd]; [destruct (HdsO d Hd) as (A & B & _) | destruct (HdsB d Hd) as (A & B & _)]; auto.
Qed.
Lemma inX_C d : ltac2:(tb__ "0|0|
S81S4bVd;VdsC;A3S81S4bVd;S138A3F_;"). Proof using . intros H. unfold dsX. apply in_app_iff. left. exact H. Qed.
Lemma inX_O d : ltac2:(tb__ "0|0|
S81S4bVd;VdsO;A3S81S4bVd;S138A3F_;"). Proof using . intros H. unfold dsX. apply in_app_iff. right. apply in_app_iff. left. exact H. Qed.
Lemma inX_B d : ltac2:(tb__ "0|0|
S81S4bVd;VdsB;A3S81S4bVd;S138A3F_;"). Proof using . intros H. unfold dsX. apply in_app_iff. right. apply in_app_iff. right. exact H. Qed.
Lemma inX_cases d : ltac2:(tb__ "0|0|
S81S4bVd;S138A3S4S81S4bVd;VdsC;A3S4S81S4bVd;VdsO;A3S81S4bVd;VdsB;A3A2A2F_;").
Proof using . intros H. unfold dsX in H. apply in_app_iff in H as [H|H]; [left; exact H|]. apply in_app_iff in H as [H|H]; right; [left | right]; exact H. Qed.
Lemma EmW' : ltac2:(tb__ "0|0|
S0Sd9Q40A1S6cSd9Q8A1A1F_;SceVrhoW;A1VmW;A3"). Proof using L am g gd i rd0 rho s. reflexivity. Qed.

Let m' : word -> option byte := ltac2:(tb__ "0|0|
S15bS4bS4fVmsF;VrhoF;VdsF;A5").
Let touched : Z -> Prop := ltac2:(tb__ "0|0|
S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S138A4").
Let touchedC : Z -> Prop := ltac2:(tb__ "0|0|
S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsC;A4").
Let touchedB : Z -> Prop := ltac2:(tb__ "0|0|
S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsB;A4").
Definition gslot (x : Z) : Prop := ltac2:(tb__ "0|1|
S1S8bSe8VL;Vg;A2M0Vx;A2S8dVx;S8cG0Z28A2A2A2").
Definition stk (x : Z) : Prop := ltac2:(tb__ "0|1|
S1S8bS92S149Vrho;A1M0Vscut;A2Vx;A2S8dVx;G0A2A2").
Definition touchedV (x : Z) : Prop := ltac2:(tb__ "0|0|
S4VtouchedC;Vx;A1S4VtouchedB;Vx;A1S4S139Vx;A1S13aVx;A1A2A2A2").
Let bv1 : byteview := ltac2:(tb__ "0|0|
S114S136S86Vm';A2S137S86Vm';A2A2").
Let rv1 : byteview := ltac2:(tb__ "0|0|
S114S136S86Vm';A2Sd9Q40A1S72L_;A2").

Lemma V1' : ltac2:(tb__ "0|2|
S6aS1S8bZ0R1A2S8dR1S8eZ2Z40A2A2A2S2Vtouched;R2A1A1S1S0S6cS6aA1M0Vbv1;R3A1S114S136S86VmW;A2M1S137S86VmW;A2R3A3A3S0G0Vrv1;R3A1S114G1Sd9Q40A1S72L_;R3A3A3A2F_;F_;Fx;").
Proof using Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsF_DS HdsF_cond HdsF_ent Hgd Hgd_holds Hm_sct Hrom HsmF Hsp Hu m'.
  exact (V1 segsU rhoW zr1 zl1 (zr1_any mW) (zl1_any mW) od obj_of dlo dhi dcells drom DS mW EmW' rngD range64D cellsD cellsInD semD coverD dunkD romD
           ms Hrom tr md msF rhoF HagF SF oStkF objsF dsF dsX HSF_objs HSF_match HsmF HdsF od_ok HdsF_ent Hent_hold).
Qed.
Lemma VM' : ltac2:(tb__ "0|0|
S6aS1S8bZ0R1A2S8dR1S8eZ2Z40A2A2A2Vtouched;R2A1Sa9VL;Vs';R3A3S2S0S6cS6aA1Vbv1;R4A1S79S6aA1A3A1F_;F_;F_;Fx;").
Proof using HMI HP12 HSF_match HSF_objs HXz HagF HdsB HdsC HdsF_DS HdsF_cond HdsO Hgd HsmF Hsp Hu m'.
  intros x Hx T _. exact (VM segsU rhoW od obj_of dlo dhi drom DS rngD dunkD tr md msF rhoF HagF SF oStkF objsF dsF dsX HSF_objs HSF_match HsmF HdsF HdsX_sub x Hx T).
Qed.
Definition cell_from_odW : ltac2:(tb__ "0|3|
S4bS6aS73SbaS9fS6aS81S4bR6S138A3S81S6eS6eS6aS73A2M0SbaA2S74G0SbaS74S6aS73R6R5A4R4A4S58R7A1A3S0S6aSa0VL;Sa5R4A1A2S8cS4cVs;VL;Vg;Vam;R8A5R7A2A3S0S73Sa2R5A1R7A3S0S6cS6aA1S1b8VL;R6A2S6dS6aR5A2A3S0S6aS90R6S8eZ2S8fZ8S91R9A1A2A2M1A2S90S10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R8A3G1A2A3SaaVL;S114S136S86S15bS4bS4fVmsF;VrhoF;VdsF;A5M2A2S137S86G2A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S15eS86VrhoW;SdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SefVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SeeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S4bS4fS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S58S56S54Vam;A1S5aVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S5dVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S14fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S150Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S152Vam;A1S151Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S13eVobjsF;VdsF;S138VHSF_objs;VHSF_match;VHsmF;S13cS140VL;A23").
Definition cell_from_od_subW : ltac2:(tb__ "0|2|
S4bS6aS73SbaS73S9fS6aS81S4bR7S138A3S81S6eS6eS6aS73A2M0SbaA2S74G0SbaS74S6aS73R7R6A4R5A4S58R8A1A3S0S6aSa0VL;Sa5R4A1A2S8cS8cS4cVs;VL;Vg;Vam;R9A5R8A2S91R5A1A2A3S164S1aeR6Sa2R5A1A2R8A2S0S6cS6aA1S1b8VL;R6A2S6dS6aR5A2A3S73S163R1Sa2R8A1A2S0S6aSabR8Sa2R9A1R2A3SabS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8RbA3RcS1aeRaR2A2A3A3F_;Fj;SaaVL;S114S136S86S15bS4bS4fVmsF;VrhoF;VdsF;A5M1A2S137S86G1A2A2R8A3F_;F_;F_;F_;F_;F_;Fz;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S15fS86VrhoW;SdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SefVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SeeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S4bS4fS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S58S56S54Vam;A1S5aVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S5dVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S14fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S150Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S152Vam;A1S151Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S13eVobjsF;VdsF;S138VHSF_objs;VHSF_match;VHsmF;S13cS140VL;A23").
Definition cell_from_od_zeroW : ltac2:(tb__ "0|3|
S4bS6aS73SbaS73S9fS81S4bR6S138A3S81S6eS6eS6aS73A2M0SbaA2S74G0SbaS74S6aS73R6R5A4R4A4S58R7A1A3S0S6aSa0VL;Sa5R3A1A2S8cS8cS4cVs;VL;Vg;Vam;R8A5R7A2S91R4A1A2A3S164S1aeR5Sa2R4A1A2R7A2S0S6cS6aA1S1b8VL;R5A2S6dS6aZ0M1A2A3S0S6aS10cSdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8R8A3G1A3SaaVL;S114S136S86S15bS4bS4fVmsF;VrhoF;VdsF;A5M2A2S137S86G2A2A2R7A3F_;F_;F_;F_;F_;F_;Fc;Fk;Fe;Fw;Foff;Fd;") := ltac2:(tb__ "0|0|
S160S86VrhoW;SdeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SddVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;A8SefVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9SeeVs;VL;Vg;Vam;Vi;Vrho;Vgd;Vrd0;VmW;A9S4bS4fS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S58S56S54Vam;A1S5aVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S5dVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHsp;A11S14fVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13S150Vs;VL;Vg;Vam;Vrho;Vgd;VHgd;A7S152Vam;A1S151Vam;A1Vtr;Vmd;VmsF;VrhoF;VHagF;VSF;S13eVobjsF;VdsF;S138VHSF_objs;VHSF_match;VHsmF;S13cS140VL;A23").
Definition m'_inW : ltac2:(tb__ "0|1|
S4bS6aS81S4bR2VdsF;A3S1S8bS4cVs;VL;Vg;Vam;R3A5R2A2S8dR2S4dVs;VL;Vg;Vam;R3A5A2A2S1S8bZ0R3A2S8dR3S8eZ2Z40A2A2A2S0S6cSd9Q8A1A1S15bS4bS4fVmsF;VrhoF;VdsF;SdbQ40R4A2M0A6S1b2VmsF;G0A2A3F_;F_;F_;Fx;Fd;") := ltac2:(tb__ "0|0|
S161VrhoW;S4bS4fS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S54Vam;A1S5aVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13VmsF;VrhoF;VHagF;VdsF;S13cAc").
Definition m'_outW : ltac2:(tb__ "0|1|
S6aS1S8bZ0R1A2S8dR1S8eZ2Z40A2A2A2S4bS81S4bR1VdsF;A3S2S1S8bS4cVs;VL;Vg;Vam;R2A5R4A2S8dR4S4dVs;VL;Vg;Vam;R2A5A2A2A1F_;Fd;S0S6cSd9Q8A1A1S15bS4bS4fVmsF;VrhoF;VdsF;SdbQ40R3A2M0A6VmW;G0A1A3F_;F_;Fx;") := ltac2:(tb__ "0|0|
S162VrhoW;S4bS4fS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S54Vam;A1VmW;S144S5aVs;VL;VX;VU;Vg;Vam;Vi;Vrho;Vgd;Vvm;Vrd0;Vwok0;VHMI;VHXz;VHu;VHgd;VHP12;VHsp;VmW;A13VmsF;VrhoF;VHagF;VdsF;S13cAe").
Definition touched_decW : ltac2:(tb__ "0|1|
S6aS1b0S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S138R1A5M0S2G0A1A2Fx;") := ltac2:(tb__ "0|0|
S15dS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4S138A4").
Definition touchedC_dec : ltac2:(tb__ "0|1|
S6aS1b0S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsC;R1A5M0S2G0A1A2Fx;") := ltac2:(tb__ "0|0|
S15dS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsC;A4").
Definition touchedB_dec : ltac2:(tb__ "0|1|
S6aS1b0S15cS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsB;R1A5M0S2G0A1A2Fx;") := ltac2:(tb__ "0|0|
S15dS4bS4cVs;VL;Vg;Vam;A4S4dVs;VL;Vg;Vam;A4VdsB;A4").
Lemma touchedV_dec x : ltac2:(tb__ "0|1|
S1b0S13fVx;A1M0S2G0A1A2").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched.
  unfold touchedV, gslot, stk. destruct (touchedC_dec x) as [T|T]; [left; tauto|]. destruct (touchedB_dec x) as [T2|T2]; [left; tauto|].
  destruct (Z_le_dec zG x); [destruct (Z_lt_dec x (zG + 40)); [left; right; right; left; lia|]|];
  (destruct (Z_le_dec (sp0 - scut) x); [destruct (Z_lt_dec x sp0); [left; right; right; right; lia|]|]); right; intros [H|[H|[H|H]]]; try tauto; lia.
Qed.
Lemma touchedC_real x : ltac2:(tb__ "0|0|
VtouchedC;Vx;A1Vtouched;Vx;A1F_;").
Proof using L am dsB dsC dsO g s. intros (d & HdC & R). exists d. split; [exact (inX_C d HdC) | exact R]. Qed.
Lemma touchedB_real x : ltac2:(tb__ "0|0|
VtouchedB;Vx;A1Vtouched;Vx;A1F_;").
Proof using L am dsB dsC dsO g s. intros (d & HdC & R). exists d. split; [exact (inX_B d HdC) | exact R]. Qed.

Lemma D_fp : ltac2:(tb__ "0|0|
S0S71S6eS9cS6aA2A1SadVs';A1SadVs;A1A3"). Proof using Hdelta. exact (proj1 Hdelta). Qed.
Lemma D_ub : ltac2:(tb__ "0|0|
S0S71S6eS8S6aA2A1Sb3Vs';A1Sb3Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 Hdelta)). Qed.
Lemma D_init : ltac2:(tb__ "0|0|
S0S70S3aVs';A1S3aVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 Hdelta))). Qed.
Lemma D_areas : ltac2:(tb__ "0|0|
S0S71S8A1S29Vs';A1S29Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 Hdelta)))). Qed.
Lemma D_regions : ltac2:(tb__ "0|0|
S0S71SdA1S2dVs';A1S2dVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hdelta))))). Qed.
Lemma D_brk : ltac2:(tb__ "0|0|
S0S3fS39Vs';A1S39Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))). Qed.
Lemma D_keys : ltac2:(tb__ "0|0|
S0S71S8A1Sa4Vs';A1Sa4Vs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))). Qed.
Lemma D_shift : ltac2:(tb__ "0|0|
S0S6aS2cVs';A1S2cVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))). Qed.
Lemma D_acount : ltac2:(tb__ "0|0|
S0S6aS2aVs';A1S2aVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta))))))))). Qed.
Lemma D_aptr : ltac2:(tb__ "0|0|
S0S8S2bVs';A1S2bVs;A1A3"). Proof using Hdelta. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))))). Qed.
Lemma D_cells : ltac2:(tb__ "0|0|
S9fS81S9fR1S75S9fSa7Vs';A1S191Vs';A1A3A3S4S81S9fR2S75S9fSa7Vs;A1S191Vs;A1A3A3S81S9cSa5R2A1Vlocs;A3A2F_;Fc;").
Proof using Hdelta. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hdelta)))))))))). Qed.

Lemma region_of' k : ltac2:(tb__ "0|0|
S0S6cSdA1SacVs';Vk;A2SacVs;Vk;A2A3").
Proof using Hdelta. unfold region_of. rewrite D_regions. reflexivity. Qed.
Lemma HL' : layout_ok L s'.
Proof using HMI Hdelta.
  pose proof HL as (A & B & C' & D). split; [exact A|]. split; [|rewrite D_fp; split; [exact C' | exact D]].
  intros k rg Hr Hl. rewrite region_of' in Hr. exact (B k rg Hr Hl).
Qed.

Lemma Hvm' : ltac2:(tb__ "0|0|
S11aVL;Vs';Vvm;A3").
Proof using HMI Hdelta.
  pose proof HV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11). unfold vm_ok.
  split; [intros r rg Hr; rewrite region_of' in Hr; exact (V1 r rg Hr)|].
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

Lemma fp_entry_below rg : ltac2:(tb__ "0|1|
S81S6eS9cS6aA2Vrg;SadVs';A1A3S8bZ0S7dS9cS6aVrg;A3M0A2S8bS8cSa0VL;S7bS9cS6aVrg;A3A2G0A2S117VL;A1A2F_;F_;").
Proof using HMI Hdelta Hgd Hsc48 rho touched touchedB touchedC.
  intros Hin Hn. destruct rg as [[o|p] n]; cbn [fst snd] in *.
  - unfold footprint in Hin. destruct Hin as [E|Hin].
    + injection E as <- <-. cbn [loc_addr]. rewrite Hctx. top_ranges. unfold CTX_SIZE. lia.
    + exfalso. apply in_app_iff in Hin as [Hin|Hin].
      * apply in_map_iff in Hin as (a & E & _). discriminate E.
      * apply in_flat_map in Hin as (k & _ & Hin). destruct (region_of s' k) as [rg|]; [|destruct Hin].
        destruct (rg_kind rg); try destruct Hin. destruct (rg_live rg); [|destruct Hin]. destruct Hin as [E|[]]. discriminate E.
  - exact (proj1 (proj2 (footprint_mem_range C_U L s' vm p n Hvm' HLG Hin Hn))).
Qed.
Lemma cell_below_ceiling c k : ltac2:(tb__ "0|0|
S81S9fVc;S75S9fSa7Vs';A1S191Vs';A1A3A3S163Vk;Sa2Vc;A1A2S8dS8cSa0VL;Sa5Vc;A1A2S91Vk;A1A2S117VL;A1A2F_;F_;").
Proof using HI' HMI HXz' Hdelta Hgd Hsc48 Hsp touched touchedB touchedC.
  intros Hc Hk. destruct (cell_in_footprintI (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' c Hc) as (rg & Hrg & [I1 I2]).
  unfold crange, cell_range in I1, I2. cbn [fst snd] in I1, I2.
  pose proof (fp_entry_below rg Hrg ltac:(lia)). lia.
Qed.
Lemma owned_below_ceiling x : ltac2:(tb__ "0|0|
Sa9VL;Vs';Vx;A3S8dVx;S117VL;A1A2F_;").
Proof using HMI Hdelta Hgd Hsc48 Hsp touched touchedB touchedC. intros [(rg & Hrg & Hx) _]. pose proof (fp_entry_below rg Hrg ltac:(lia)). lia. Qed.

Definition meets (c : mcell) : Prop := ltac2:(tb__ "0|0|
S3S73S73S1S163R1Sa2Vc;A1A2S13fS8cSa0VL;Sa5Vc;A1A2S91R1A1A2A1A2Lk;A2").
Definition meetsC (c : mcell) : Prop := ltac2:(tb__ "0|0|
S3S73S73S1S163R1Sa2Vc;A1A2VtouchedC;S8cSa0VL;Sa5Vc;A1A2S91R1A1A2A1A2Lk;A2").

Lemma dsF_zfree d : ltac2:(tb__ "0|0|
S81S4bVd;VdsF;A3S14bVs;VL;VX;Vg;Vam;Vd;A6F_;").
Proof using HMI HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hsp Hu touched touchedB touchedC.
  intros Hd. destruct (HdsF_ent d Hd) as [Hok | HdX]; [exact (od_ok_zfree d Hok)|].
  unfold dsX in HdX. apply in_app_iff in HdX as [HdC|HdX]; [|apply in_app_iff in HdX as [HdO|HdB]].
  - destruct (HdsC d HdC) as (_ & Hok' & _). exact (zfree_of d (HdsF d Hd) (od_ok_at_zkc s' d Hok')).
  -
    destruct (HdsO d HdO) as (_ & _ & R1 & R2). intros x Hx.
    pose proof (keys_apart g x g_key (X_key x Hx) ltac:(intros E; apply (X_not_used x am Hx); rewrite <- E; exact Hu)). unfold zG, U.Mal_nt__G1.Mal_nt_I.zG in *. lia.
  - exact (proj1 (proj2 (proj2 (HdsB d HdB)))).
Qed.
Lemma dsF_nz d x : ltac2:(tb__ "0|0|
S81S4bVd;VdsF;A3S1S8bS4cVs;VL;Vg;Vam;Vd;A5Vx;A2S8dVx;S4dVs;VL;Vg;Vam;Vd;A5A2A2S2S18bVL;VX;Vx;A3A1F_;F_;").
Proof using HMI HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hsp Hu touched touchedB touchedC. intros Hd R (q & Hq & Rq). pose proof (dsF_zfree d Hd q Hq). unfold META_SIZE in Rq. lia. Qed.
Lemma touched_nz x : ltac2:(tb__ "0|0|
Vtouched;Vx;A1S2S18bVL;VX;Vx;A3A1F_;").
Proof using HMI HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hsp Hu touchedB touchedC. intros (d & HdX & R). exact (dsF_nz d x (proj1 (HdsX_sub d HdX)) R). Qed.

Lemma touchedCB_ng x : ltac2:(tb__ "0|0|
S4VtouchedC;Vx;A1VtouchedB;Vx;A1A2S2S139Vx;A1A1F_;").
Proof using HdsCB_g Hgd Hsc48 Hsp touched.
  unfold gslot. intros [(d & HdC & R)|(d & HdC & R)];
    [pose proof (HdsCB_g d ltac:(apply in_app_iff; left; exact HdC)) | pose proof (HdsCB_g d ltac:(apply in_app_iff; right; exact HdC))]; lia.
Qed.
Lemma dhi_below d : ltac2:(tb__ "0|0|
S54Vam;Vd;A2S8bS4dVs;VL;Vg;Vam;Vd;A5S117VL;A1A2F_;").
Proof using HMI HXz Hgd Hsc48 Hsp Hsp_high Hu touched touchedB touchedC.
  intros Hd. pose proof (proj2 Hd) as HC. unfold dhi. pose proof R_all as R. pose proof (ceiling_small L). pose proof RN.
  destruct d; cbn [dcond] in HC; cbn [dlo dsz]; try (pose proof (klo_range' k)); try (pose proof (flo_range k)); try (pose proof (par_ranges HC)); unfold sc; top_ranges; lia.
Qed.
Lemma dsF_below d x : ltac2:(tb__ "0|0|
S81S4bVd;VdsF;A3S1S8bS4cVs;VL;Vg;Vam;Vd;A5Vx;A2S8dVx;S4dVs;VL;Vg;Vam;Vd;A5A2A2S8dVx;S117VL;A1A2F_;F_;").
Proof using HMI HXz HdsF_DS HdsF_cond Hgd Hsc48 Hsp Hsp_high Hu touched touchedB touchedC. intros Hd R. pose proof (dhi_below d (HdsF d Hd)). lia. Qed.
Lemma stk_high x : ltac2:(tb__ "0|0|
S13aVx;A1S1S8bS117VL;A1Vx;A2S8dVx;S8eZ2Z40A2A2A2F_;").
Proof using Hgd Hsc48 Hscut Hsp Hsp_high touched touchedB touchedC. unfold stk. intros R. pose proof Hsp_high. pose proof Hscut. pose proof (urange (rw rho 10%positive)). unfold sp0, U.Mal_nt__G2.Mal_nt_Z.sp0 in *. lia. Qed.
Lemma touched_nstk x : ltac2:(tb__ "0|0|
Vtouched;Vx;A1S2S13aVx;A1A1F_;").
Proof using HMI HXz HdsB HdsC HdsF_DS HdsF_cond HdsO Hgd Hsc48 Hscut Hsp Hsp_high Hu touchedB touchedC. intros (d & HdX & R) S. pose proof (dsF_below d x (proj1 (HdsX_sub d HdX)) R). pose proof (stk_high x S). lia. Qed.
Lemma gslot_nstk x : ltac2:(tb__ "0|0|
S139Vx;A1S2S13aVx;A1A1F_;").
Proof using HMI Hgd Hsc48 Hscut Hsp Hsp_high Hu touched touchedB touchedC. unfold gslot. intros R S. pose proof g_zone. pose proof (stk_high x S). lia. Qed.
Lemma gslot_nz x : ltac2:(tb__ "0|0|
S139Vx;A1S2S18bVL;VX;Vx;A3A1F_;").
Proof using HMI Hgd Hsc48 Hsp Hu touched touchedB touchedC.
  unfold gslot. intros R (q & Hq & Rq).
  pose proof (keys_apart g q g_key (X_key q Hq) ltac:(intros E; apply (X_not_used q am Hq); rewrite <- E; exact Hu)). unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, META_SIZE in *. lia.
Qed.
Lemma stk_nz x : ltac2:(tb__ "0|0|
S13aVx;A1S2S18bVL;VX;Vx;A3A1F_;").
Proof using HMI Hgd Hsc48 Hscut Hsp Hsp_high touched touchedB touchedC. intros S (q & Hq & Rq). pose proof (key_range40 q (X_key q Hq)). pose proof (stk_high x S). unfold META_SIZE in *. lia. Qed.

Definition gslotb (x : Z) : bool := ltac2:(tb__ "0|1|
S76S95Se8VL;Vg;A2M0Vx;A2S96Vx;S8cG0Z28A2A2A2").
Definition stkb (x : Z) : bool := ltac2:(tb__ "0|1|
S76S95S92S149Vrho;A1M0Vscut;A2Vx;A2S96Vx;G0A2A2").
Lemma gslotb_spec x : ltac2:(tb__ "0|0|
S7S0S70S142Vx;A1S72A3S139Vx;A1A2").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC. unfold gslotb, gslot. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma stkb_spec x : ltac2:(tb__ "0|0|
S7S0S70S143Vx;A1S72A3S13aVx;A1A2").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC. unfold stkb, stk. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Definition m'c : word -> option byte := ltac2:(tb__ "0|1|
Sd9Q40M0A1S70S6cSd9Q8A1A1L_;S143SdaG0R1A2A1S1b2VmsF;R1A2Vm';R1A1X70x2La;").

Definition m'v : word -> option byte := ltac2:(tb__ "0|5|
Sd9Q40M0A1S70S6cSd9Q8M1A1M2A1L_;M3S142SdaG0R1A2M4A1S6dG2SdbG1Z0A2A2G3S190VL;VX;G4A3VmV;R1A1S13dR1A1X70x2X70x2La;").
Lemma m'c_stk a : ltac2:(tb__ "0|0|
S13aSdaQ40Va;A2A1S0S6cSd9Q8A1A1S13dVa;A1S1b2VmsF;Va;A2A3F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC. intros H. unfold m'c. rewrite (proj2 (stkb_spec _) H). reflexivity. Qed.
Lemma m'c_nstk a : ltac2:(tb__ "0|0|
S2S13aSdaQ40Va;A2A1A1S0S6cSd9Q8A1A1S13dVa;A1Vm';Va;A1A3F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC. intros H. unfold m'c. destruct (stkb (bv_unsigned a)) eqn:E; [exfalso; exact (H (proj1 (stkb_spec _) E)) | reflexivity]. Qed.
Lemma m'v_g a : ltac2:(tb__ "0|2|
S139SdaQ40Va;A2A1S0S6cSd9Q8M0A1M1A1S13bVa;A1S6dG1SdbG0Z0A2A2A3F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC. intros H. unfold m'v. rewrite (proj2 (gslotb_spec _) H). reflexivity. Qed.
Let bv1v : byteview := ltac2:(tb__ "0|0|
S114S136S86S13bA2S137S86S13bA2A2").
Let rv1v : byteview := ltac2:(tb__ "0|0|
S114S136S86S13bA2Sd9Q40A1S72L_;A2").
Let rvV : byteview := ltac2:(tb__ "0|0|
S114S136S86VmV;A2Sd9Q40A1S72L_;A2").

Lemma m'v_nz a : ltac2:(tb__ "0|1|
S2S139SdaQ40Va;A2M0A1A1S2S18bVL;VX;G0A3A1S0S6cSd9Q8A1A1S13bVa;A1S13dVa;A1A3F_;F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC.
  intros G0 H. unfold m'v. destruct (gslotb (bv_unsigned a)) eqn:E; [exfalso; exact (G0 (proj1 (gslotb_spec _) E))|].
  rewrite (proj2 (zslotb_false L X _) H). reflexivity.
Qed.
Lemma m'v_z a : ltac2:(tb__ "0|1|
S2S139SdaQ40Va;A2M0A1A1S18bVL;VX;G0A3S0S6cSd9Q8A1A1S13bVa;A1VmV;Va;A1A3F_;F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp i touched touchedB touchedC.
  intros G0 H. unfold m'v. destruct (gslotb (bv_unsigned a)) eqn:E; [exfalso; exact (G0 (proj1 (gslotb_spec _) E))|].
  rewrite (proj2 (zslotb_spec L X _) H). reflexivity.
Qed.

Lemma views_at (m1 m2 : word -> option byte) x : ltac2:(tb__ "0|6|
S0S6cSd9Q8A1A1Vm1;SdbQ40M0Vx;A2M1A1Vm2;G1A1A3S1S0S6cS6aA1M2S114S136S86Vm1;A2M3S137S86Vm1;A2Vx;A3S114S136S86Vm2;A2M4S137S86Vm2;A2Vx;A3A3S0G2S114G3Sd9G0A1S72L_;M5Vx;A3S114G4G5Vx;A3A3A2F_;").
Proof using . intros E. unfold byteview_of, Glue.rd_of, Glue.wok_of. rewrite E. auto. Qed.

Lemma m'_zslot x : ltac2:(tb__ "0|1|
S1S8bZ0Vx;A2S8dVx;S8eZ2Z40A2A2A2S18bVL;VX;Vx;A3S0S6cSd9Q8A1A1Vm';SdbQ40Vx;A2M0A1VmW;G0A1A3F_;F_;").
Proof using HMI HP12 HXz HagF HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hsp Hu msF touched touchedB touchedC. intros Hx Z0. apply (m'_outW x Hx). intros d Hd R. exact (dsF_nz d x Hd R Z0). Qed.

Theorem V1v : ltac2:(tb__ "0|1|
S6aS1S8bZ0R1A2S8dR1S8eZ2Z40A2A2A2S2S13fR2A1A1S1S0S6cS6aA1M0Vbv1v;R3A1Vbv0;R3A1A3S0G0Vrv1v;R3A1VrvV;R3A1A3A2F_;F_;Fx;").
Proof using Erd Ewok HMI HP12 HSF_match HSF_objs HXz HZ HagF Hdepth HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hgd_holds Hm_sct Hrom Hsc48 Hscut HsmF Hsp Hu bv1 rv1 touched.
  intros x Hx NT. unfold bv1v, rv1v, bv0, rvV. unfold touchedV in NT.
  assert (NG : ~ gslot x) by tauto. assert (NS : ~ stk x) by tauto.
  assert (NTr : ~ touched x).
  { intros (d & HdX & R). unfold dsX in HdX. apply in_app_iff in HdX as [HdC|HdX]; [apply NT; left; exists d; auto|].
    apply in_app_iff in HdX as [HdO|HdB]; [|apply NT; right; left; exists d; auto].
    destruct (HdsO d HdO) as (_ & _ & R1 & R2). apply NG. unfold gslot. lia. }
  destruct (zslotb L X x) eqn:Ez.
  - apply views_at. apply m'v_z; rewrite u64_of_sum by lia; [exact NG | exact (proj1 (zslotb_spec L X x) Ez)].
  - pose proof (proj1 (zslotb_false L X x) Ez) as NZ.
    destruct (views_at m'v m' x ltac:(rewrite (m'v_nz (Z_to_bv 64 x)); rewrite ?u64_of_sum by lia; [apply m'c_nstk; rewrite u64_of_sum by lia; exact NS | exact NG | exact NZ])) as [A1 A2]. rewrite A1, A2.
    destruct (V1' x Hx NTr) as [B1 B2]. unfold bv1, rv1 in B1, B2. rewrite B1, B2.
    apply views_at. symmetry. apply HZ_at. intros q Hq R. apply NZ. exists q. rewrite u64_of_sum in R by lia. unfold META_SIZE. auto.
Qed.
Lemma bv_zero x : ltac2:(tb__ "0|1|
S1S8bZ0M0Vx;A2S8dVx;S8eZ2Z40A2A2A2S139Vx;A1S0S6cS6aA1Vbv1v;Vx;A1S6dS6aG0A2A3F_;F_;").
Proof using Hdepth Hgd Hsc48 Hscut Hsp X i m' mV touched touchedB touchedC.
  intros Hx G0. unfold bv1v, byteview_of, Glue.rd_of, Glue.wok_of.
  replace ((0 <=? x) && (x <? 2 ^ 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite (m'v_g (Z_to_bv 64 x)) by (rewrite u64_of_sum by lia; exact G0). cbn. reflexivity.
Qed.
Theorem VMv : ltac2:(tb__ "0|0|
S6aS1S8bZ0R1A2S8dR1S8eZ2Z40A2A2A2S13fR2A1Sa9VL;Vs';R3A3S2S0S6cS6aA1Vbv1v;R4A1S79S6aA1A3A1F_;F_;F_;Fx;").
Proof using HMI HP12 HSF_match HSF_objs HXz HagF Hdelta Hdepth HdsB HdsC HdsF_DS HdsF_cond HdsF_ent HdsO Hgd Hsc48 Hscut HsmF Hsp Hsp_high Hu bv1 mV touched.
  intros x Hx T OW.
  destruct (Z_le_dec zG x) as [G1|G1]; [destruct (Z_lt_dec x (zG + 40)) as [G2|G2]|].
  { rewrite (bv_zero x Hx ltac:(unfold gslot; lia)). discriminate. }
  all: assert (NG : ~ gslot x) by (unfold gslot; lia).
  all: destruct T as [T|[T|[T|T]]]; [ | | exfalso; exact (NG T) | exfalso; pose proof (stk_high x T); pose proof (owned_below_ceiling x OW); lia].
  all: first [pose proof (touchedC_real x T) as TRx | pose proof (touchedB_real x T) as TRx].
  all: unfold bv1v; rewrite (proj1 (views_at m'v m' x ltac:(rewrite (m'v_nz (Z_to_bv 64 x)); rewrite ?u64_of_sum by lia; [apply m'c_nstk; rewrite u64_of_sum by lia; exact (touched_nstk x TRx) | exact NG | exact (touched_nz x TRx)]))).
  all: pose proof (VM' x Hx TRx OW) as H; unfold bv1 in H; exact H.
Qed.

Lemma gslot_owned x : ltac2:(tb__ "0|0|
S139Vx;A1Sa9VL;Vs';Vx;A3F_;").
Proof using HI' HIr HMI HP12 HR2g HXz' HagF Hdelta Hdepth HdsB HdsC HdsCB_g HdsF_ent HdsO HdsO_cover Hgd Hlocs Hsc48 Hscut Hsp Hu touched touchedB touchedC.
  unfold gslot. intros R. pose proof D_keys as DK.
  assert (Kg : In g (keys s')) by (rewrite DK; exact g_key).
  pose proof (HXz' g ltac:(left; reflexivity)) as Mg'.
  pose proof (fun c Hc => meta_cells_in_imageI (g :: X) (Some (gPar, iPar)) U s' HI' g c Kg Hc) as MI. rewrite Mg' in MI. cbn [meta_slot_cells] in MI.
  assert (AGq : forall dd, loc_addr L (LMem (padd g dd)) = zG + dd) by (intros dd; unfold zG, U.Mal_nt__G1.Mal_nt_I.zG, addr_of, loc_addr; destruct g; cbn [padd]; lia).
  assert (C6 : forall off (w : nat) vv, In (MCell (LMem (padd g off)) w vv)
             [MCell (LMem (padd g META_prev)) 8 (MallocInv.optr None); MCell (LMem (padd g META_next)) 8 (MallocInv.optr None); MCell (LMem (padd g META_mem)) 8 (VZ 0);
              MCell (LMem (padd g META_avail)) 4 (VZ 0); MCell (LMem (padd g META_freed)) 4 (VZ 0); MCell (LMem (padd g META_bits)) 8 (VZ 0)] ->
             zG + off <= x < zG + off + Z.of_nat w -> alloc_owned L s' x).
  { intros off w vv Hin Hx'.
    pose proof (image_cell_owned (g :: X) (Some (gPar, iPar)) U s' L HI' HXr' HL' _ (MI _ Hin) (Z.to_nat (x - (zG + off))) ltac:(cbn [mc_w]; lia)) as OW.
    cbn [mc_loc] in OW. rewrite AGq in OW. replace (zG + off + Z.of_nat (Z.to_nat (x - (zG + off)))) with x in OW by lia. exact OW. }
  unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits in C6.
  destruct (Z_lt_dec x (zG + 8)); [eapply (C6 0 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  destruct (Z_lt_dec x (zG + 16)); [eapply (C6 8 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  destruct (Z_lt_dec x (zG + 24)); [eapply (C6 16 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  destruct (Z_lt_dec x (zG + 28)); [eapply (C6 24 4%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  destruct (Z_lt_dec x (zG + 32)); [eapply (C6 28 4%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]|].
  eapply (C6 32 8%nat); [cbn; tauto | cbv [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.
Lemma gslot_touched x : ltac2:(tb__ "0|0|
S139Vx;A1Vtouched;Vx;A1F_;").
Proof using HdsO_cover dsB dsC.
  intros G0. pose proof G0 as R. unfold gslot in R.

  destruct (HdsO_cover x G0) as (d & HdO & Rd). exists d. split; [exact (inX_O d HdO) | exact Rd].
Qed.
Lemma magree_post : ltac2:(tb__ "0|0|
S18dVL;S6fS8Vg;VX;A3S13bS13dA4").
Proof using HI' HIr HMI HP12 HR2g HSF_match HSF_objs HXz HXz' HZ HagF Hdelta Hdepth HdsB HdsC HdsCB_g HdsF_DS HdsF_cond HdsF_ent HdsO HdsO_cover Hgd Hlocs Hsc48 Hscut HsmF Hsp Hsp_high Hu touched touchedB touchedC.
  split.
  - intros a Ha. apply m'v_nz; [intros G0; apply Ha; exists g; split; [left; reflexivity | unfold gslot, zG, U.Mal_nt__G1.Mal_nt_I.zG, META_SIZE in *; lia]
                               | intros (q & Hq & Rq); apply Ha; exists q; split; [right; exact Hq | exact Rq]].
  - intros a. pose proof (urange a) as Ua.
    destruct (Z_le_dec zG (bv_unsigned a)) as [G1|G1]; [destruct (Z_lt_dec (bv_unsigned a) (zG + 40)) as [G2|G2]|].
    { assert (G0 : gslot (bv_unsigned a)) by (unfold gslot; lia). rewrite (m'v_g a G0).
      rewrite (m'c_nstk a (gslot_nstk _ G0)).
      pose proof (VM' (bv_unsigned a) Ua (gslot_touched _ G0) (gslot_owned _ G0)) as NN. unfold bv1, byteview_of, Glue.rd_of, Glue.wok_of in NN.
      replace ((0 <=? bv_unsigned a) && (bv_unsigned a <? 2 ^ 64))%bool with true in NN by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Z_to_bv_bv_unsigned in NN. destruct (m' a) as [b|] eqn:Em; [split; intros; discriminate|]. exfalso.
      cbn [andb] in NN. destruct (Glue.wseg_addr segsU a) eqn:Ew; [|apply NN; reflexivity].
      change (Glue.wseg_addr segsU a) with (Contract.wseg_addr segsU a) in Ew.
      pose proof (ClientLaws.wseg_in_image_U a Ew) as WI. cbn [mc_img_lo mc_img_hi C_U] in WI. pose proof g_zone as GZ. unfold gslot in G0. lia. }
    all: assert (NG : ~ gslot (bv_unsigned a)) by (unfold gslot; lia).
    all: destruct (zslotb L X (bv_unsigned a)) eqn:Ez;
      [ pose proof (proj1 (zslotb_spec L X _) Ez) as Z0; rewrite (m'v_z a NG Z0); rewrite (m'c_nstk a ltac:(intros S; exact (stk_nz _ S Z0)));
        rewrite <- (Z_to_bv_bv_unsigned 64 a); rewrite (m'_zslot (bv_unsigned a) ltac:(lia) Z0); apply HZ_none
      | rewrite (m'v_nz a NG (proj1 (zslotb_false L X _) Ez)); tauto ].
Qed.

Theorem OLD : ltac2:(tb__ "0|0|
S9fS81S9fR1S75S9fSa7Vs';A1S191Vs';A1A3A3S2S145R2A1A1S81S9fR3S75S9fSa7Vs;A1S191Vs;A1A3A3F_;F_;Fc;").
Proof using Hdelta Hlocs.
  intros c Hc NM. destruct (D_cells c Hc) as [Hold | Hloc]; [exact Hold|]. exfalso.
  apply NM. exists 0%nat. split; [exact (cell_w_posI s' c Hc)|]. rewrite Z.add_0_r.
  destruct (Hlocs _ Hloc) as [(d & HdC & R) | R]; [left; exists d; auto | right; right; left; exact R].
Qed.

Lemma optrZ_num o : ltac2:(tb__ "0|0|
S0S6aSf5VL;Vo;A2Sb9VL;Sb1Vo;A1A2A3").
Proof using . destruct o; reflexivity. Qed.

End ReabC.

End V.
End Mal_nt_V7.
